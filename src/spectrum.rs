//! FFT, spectrum computation, and spectral filtering.

#![allow(unused_imports)]

use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering as AtomicOrdering};
use std::time::Instant;

use rustfft::num_complex::Complex;

use turyn::mdd_reorder;
use turyn::mdd_zw_first;
use turyn::sat_z_middle;

use crate::config::*;
use crate::enumerate::*;
use crate::legacy_search::*;
use crate::mdd_pipeline::*;
use crate::stochastic::*;
use crate::types::*;
use crate::xy_sat::*;
use crate::SPECTRAL_FREQS;


#[derive(Clone, Debug)]
pub(crate) struct SeqWithSpectrum {
    pub(crate) seq: PackedSeq,
    pub(crate) spectrum: Vec<f64>,
}

// BoundarySignature removed: bucketing provided no benefit (see commit history).


#[derive(Clone)]
pub(crate) struct SpectralFilter {
    pub(crate) fft_size: usize,
    /// Real-input FFT (rustfft's RealFftPlanner wrapper, ~2x faster than
    /// complex FFT for real data). Input length = fft_size, output length =
    /// fft_size/2 + 1.
    pub(crate) rfft: Arc<dyn realfft::RealToComplex<f64>>,
}


impl fmt::Debug for SpectralFilter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SpectralFilter")
            .field("fft_size", &self.fft_size)
            .finish()
    }
}


impl SpectralFilter {
    pub(crate) fn new(seq_len: usize, theta_samples: usize) -> Self {
        // FFT of size M yields M/2+1 unique frequency bins for real input.
        // To match theta_samples frequency checks, need M >= 2*theta_samples.
        // Use at least 4*n for minimum spectral resolution.
        let min_size = (4 * seq_len).max(2 * theta_samples);
        let fft_size = min_size.next_power_of_two().max(16);
        let mut planner = realfft::RealFftPlanner::<f64>::new();
        let rfft = planner.plan_fft_forward(fft_size);
        Self { fft_size, rfft }
    }
}



/// Convert a signed full-sequence sum to the SAT cardinality count over a
/// middle slice with a fixed boundary contribution.  Returns `None` if the
/// resulting mid_sum is out of range or has the wrong parity.
///
///   σ_mid = σ_full − σ_bnd
///   cnt   = (σ_mid + L_mid) / 2
#[inline]
pub(crate) fn sigma_full_to_cnt(sigma_full: i32, sigma_bnd: i32, l_mid: usize) -> Option<u32> {
    let mid_sum = sigma_full - sigma_bnd;
    if mid_sum.unsigned_abs() as usize > l_mid { return None; }
    let shifted = mid_sum + l_mid as i32;
    if shifted & 1 != 0 { return None; }
    Some((shifted / 2) as u32)
}


/// Build the sorted-deduped set V of valid middle-count SAT targets for a
/// sequence, across a list of **unsigned** tuples.  Every tuple contributes
/// both `+|σ|` and `−|σ|` as candidate signed full sums (or just 0 when
/// `|σ| = 0`); each is mapped to the corresponding middle count via
/// `sigma_full_to_cnt`, skipping out-of-range / wrong-parity candidates.
///
/// `sigma_abs_of` extracts the unsigned σ magnitude for a tuple (e.g.,
/// `|t| t.w.unsigned_abs() as i32`).
///
/// Also returns the inverse map `count → [(tuple_idx, signed_sigma_full)]`
/// so callers can narrow the surviving tuple list once the SAT locks in a
/// specific count.
#[allow(dead_code)] // reference helper; see `sanity_check_canonical_tt` in tests
pub(crate) fn valid_mid_counts<F>(
    tuples: &[SumTuple],
    sigma_abs_of: F,
    sigma_bnd: i32,
    l_mid: usize,
) -> (Vec<u32>, Vec<(u32, usize, i32)>)
where F: Fn(&SumTuple) -> i32,
{
    let mut entries: Vec<(u32, usize, i32)> = Vec::new();
    for (ti, t) in tuples.iter().enumerate() {
        let abs_s = sigma_abs_of(t);
        let signs: &[i32] = if abs_s == 0 { &[0] } else { &[1, -1] };
        for &sign in signs {
            let sigma = sign * abs_s;
            if let Some(cnt) = sigma_full_to_cnt(sigma, sigma_bnd, l_mid) {
                entries.push((cnt, ti, sigma));
            }
        }
    }
    // Dedup-and-sort the distinct counts.
    let mut counts: Vec<u32> = entries.iter().map(|e| e.0).collect();
    counts.sort_unstable();
    counts.dedup();
    (counts, entries)
}


/// Given the solved middle bits and the boundary contribution, return the
/// signed full-sequence sum σ_full.
#[inline]
#[allow(dead_code)]
pub(crate) fn decode_sigma_full(mid_bits: &[i8], sigma_bnd: i32) -> i32 {
    let mid_sum: i32 = mid_bits.iter().map(|&b| b as i32).sum();
    sigma_bnd + mid_sum
}


/// Scratch buffers for realfft-based spectrum computation. Each worker
/// keeps one of these for Z and one for W. Reusing the buffers avoids
/// reallocation in the hot path (~millions of calls per run).
pub(crate) struct FftScratch {
    /// Real input (length = fft_size).
    pub(crate) input: Vec<f64>,
    /// Complex output (length = fft_size / 2 + 1).
    pub(crate) output: Vec<Complex<f64>>,
}


impl FftScratch {
    pub(crate) fn new(filter: &SpectralFilter) -> Self {
        Self {
            input: vec![0.0; filter.fft_size],
            output: vec![Complex::new(0.0, 0.0); filter.fft_size / 2 + 1],
        }
    }
}


#[inline]
pub(crate) fn fill_real_input(values: &[i8], input: &mut Vec<f64>, fft_size: usize) {
    // input is pre-sized to fft_size. Overwrite the first values.len()
    // slots and zero the rest (padding).
    debug_assert!(input.len() == fft_size);
    for (i, &v) in values.iter().enumerate() {
        input[i] = v as f64;
    }
    for slot in input.iter_mut().skip(values.len()) {
        *slot = 0.0;
    }
}


/// Write the spectrum into `out` (reusable buffer) instead of allocating.
pub(crate) fn compute_spectrum_into(
    values: &[i8],
    filter: &SpectralFilter,
    scratch: &mut FftScratch,
    out: &mut Vec<f64>,
) {
    let m = filter.fft_size;
    fill_real_input(values, &mut scratch.input, m);
    filter.rfft.process(&mut scratch.input, &mut scratch.output).unwrap();
    out.clear();
    out.reserve(scratch.output.len());
    for c in &scratch.output {
        out.push(c.norm_sqr());
    }
}


pub(crate) fn spectrum_if_ok(
    values: &[i8],
    filter: &SpectralFilter,
    bound: f64,
    scratch: &mut FftScratch,
) -> Option<Vec<f64>> {
    let m = filter.fft_size;
    fill_real_input(values, &mut scratch.input, m);
    filter.rfft.process(&mut scratch.input, &mut scratch.output).unwrap();
    let mut spectrum = Vec::with_capacity(scratch.output.len());
    for c in &scratch.output {
        let p = c.norm_sqr();
        if p > bound {
            return None;
        }
        spectrum.push(p);
    }
    Some(spectrum)
}


/// Like `spectrum_if_ok` but writes into a reusable buffer and returns a
/// bool. The buffer is cleared and sized to `half = fft_size/2 + 1` on
/// success; its contents are undefined on failure. Use this in hot loops
/// where the spectrum is discarded 80%+ of the time — it avoids allocating
/// a fresh `Vec<f64>` per rejected candidate.
pub(crate) fn spectrum_into_if_ok(
    values: &[i8],
    filter: &SpectralFilter,
    bound: f64,
    scratch: &mut FftScratch,
    out: &mut Vec<f64>,
) -> bool {
    let m = filter.fft_size;
    fill_real_input(values, &mut scratch.input, m);
    filter.rfft.process(&mut scratch.input, &mut scratch.output).unwrap();
    out.clear();
    out.reserve(scratch.output.len());
    for c in &scratch.output {
        let p = c.norm_sqr();
        if p > bound {
            return false;
        }
        out.push(p);
    }
    true
}


pub(crate) fn spectral_pair_ok(z_spectrum: &[f64], w_spectrum: &[f64], bound: f64) -> bool {
    for i in 0..z_spectrum.len() {
        if z_spectrum[i] + w_spectrum[i] > bound {
            return false;
        }
    }
    true
}


/// Index for fast spectral pair lookups.
/// For each frequency, stores W candidate indices sorted by power at that frequency.
/// Given a Z spectrum, we find the tightest frequency (highest Z power), then binary
/// search to find only the W candidates that could pass at that frequency.
pub(crate) struct SpectralIndex {
    /// For each frequency f: Vec of (w_power_at_f, w_index), sorted by power.
    pub(crate) sorted_by_freq: Vec<Vec<(f64, usize)>>,
}


impl SpectralIndex {
    pub(crate) fn build(w_candidates: &[SeqWithSpectrum]) -> Self {
        if w_candidates.is_empty() {
            return Self { sorted_by_freq: Vec::new() };
        }
        let num_freqs = w_candidates[0].spectrum.len();
        let mut sorted_by_freq = Vec::with_capacity(num_freqs);
        for f in 0..num_freqs {
            let mut entries: Vec<(f64, usize)> = w_candidates.iter().enumerate()
                .map(|(i, w)| (w.spectrum[f], i))
                .collect();
            entries.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
            sorted_by_freq.push(entries);
        }
        Self { sorted_by_freq }
    }

    /// Find W candidates that pass budget constraints at the top-4 tightest frequencies.
    /// Uses binary search on the tightest, then filters by frequencies 2-4.
    /// Results are written into `out` (cleared first) as W indices.
    pub(crate) fn candidates_for(&self, z_spectrum: &[f64], pair_bound: f64, w_candidates: &[SeqWithSpectrum], out: &mut Vec<usize>) {
        out.clear();
        if self.sorted_by_freq.is_empty() { return; }
        // Find top-4 tightest frequencies (highest Z power = least budget for W)
        let mut top: [(f64, usize); 4] = [(f64::MIN, 0); 4];
        for (f, &zp) in z_spectrum.iter().enumerate() {
            if zp > top[3].0 {
                top[3] = (zp, f);
                // Bubble up
                for i in (0..3).rev() {
                    if top[i + 1].0 > top[i].0 {
                        top.swap(i, i + 1);
                    } else {
                        break;
                    }
                }
            }
        }
        // Binary search on tightest frequency
        let budget0 = pair_bound - top[0].0;
        let sorted = &self.sorted_by_freq[top[0].1];
        let cutoff = sorted.partition_point(|(wp, _)| *wp <= budget0);
        // Filter by frequencies 2-4
        let budget1 = pair_bound - top[1].0;
        let budget2 = pair_bound - top[2].0;
        let budget3 = pair_bound - top[3].0;
        let f1 = top[1].1;
        let f2 = top[2].1;
        let f3 = top[3].1;
        for &(_, wi) in &sorted[..cutoff] {
            let spec = &w_candidates[wi].spectrum;
            if spec[f1] <= budget1 && spec[f2] <= budget2 && spec[f3] <= budget3 {
                out.push(wi);
            }
        }
    }
}

