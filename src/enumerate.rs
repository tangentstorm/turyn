//! Tuple and sequence enumeration; W / ZW candidate streaming.

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
use crate::legacy_search::*;
use crate::mdd_pipeline::*;
use crate::spectrum::*;
use crate::stochastic::*;
use crate::types::*;
use crate::xy_sat::*;
use crate::SPECTRAL_FREQS;


/// A (Z, W) candidate reduced to everything the XY SAT stage actually
/// reads — the aperiodic autocorrelation sum `2·N_Z(s) + 2·N_W(s)` for
/// `s in 1..n`. Z and W themselves are carried alongside as PackedSeq
/// values in the work item (`SatWorkItem`); this struct is just the
/// per-lag target that drives `SolveXyPerCandidate`.
#[derive(Clone, Debug)]
pub(crate) struct CandidateZW {
    pub(crate) zw_autocorr: Vec<i32>,
}


pub(crate) fn enumerate_sum_tuples(problem: Problem) -> Vec<SumTuple> {
    let mut out = Vec::new();
    let w_values = problem.valid_w_values();

    for x in (-(problem.n as i32))..=(problem.n as i32) {
        if x % 2 != 0 {
            continue;
        }
        for y in (-(problem.n as i32))..=(problem.n as i32) {
            if y % 2 != 0 {
                continue;
            }
            for z in (-(problem.n as i32))..=(problem.n as i32) {
                if z % 2 != 0 {
                    continue;
                }
                for &w in &w_values {
                    let lhs = x * x + y * y + 2 * z * z + 2 * w * w;
                    if lhs == problem.target_energy() {
                        out.push(SumTuple { x, y, z, w });
                    }
                }
            }
        }
    }

    out
}


pub(crate) fn normalized_tuples(raw: &[SumTuple]) -> Vec<SumTuple> {
    let mut seen = HashMap::new();
    for t in raw {
        let key = t.norm_key();
        // Store canonical form: all positive, x <= y
        seen.entry(key).or_insert(SumTuple {
            x: key.0, y: key.1, z: key.2, w: key.3,
        });
    }
    let mut items: Vec<_> = seen.into_values().collect();
    items.sort_by_key(|t| t.norm_key());
    items
}


/// Unified Phase A: enumerate sum-tuples with normalization, dedup, parity filter, and --tuple filter.
/// Returns canonical forms: all positive, x <= y.
pub(crate) fn phase_a_tuples(problem: Problem, test_tuple: Option<&SumTuple>) -> Vec<SumTuple> {
    let raw = enumerate_sum_tuples(problem);
    let mut tuples = normalized_tuples(&raw);
    // Parity filter
    tuples.retain(|t| {
        (t.x + problem.n as i32) % 2 == 0
            && (t.y + problem.n as i32) % 2 == 0
            && (t.z + problem.n as i32) % 2 == 0
            && (t.w + problem.m() as i32) % 2 == 0
    });
    // --tuple filter
    if let Some(tt) = test_tuple {
        let key = tt.norm_key();
        tuples.retain(|u| u.norm_key() == key);
    }
    tuples
}



#[allow(dead_code)]
pub(crate) fn generate_sequences_with_sum(
    len: usize,
    target_sum: i32,
    root_one: bool,
    tail_one: bool,
    limit: usize,
) -> Vec<PackedSeq> {
    let mut out = Vec::new();
    generate_sequences_with_sum_visit(len, target_sum, root_one, tail_one, limit, |values| {
        out.push(PackedSeq::from_values(values));
        true
    });
    out
}


/// Generate ±1 sequences of given length and sum, calling `visit` for each.
/// `visit` returns `true` to continue, `false` to stop early.
pub(crate) fn generate_sequences_with_sum_visit<F: FnMut(&[i8]) -> bool>(
    len: usize,
    target_sum: i32,
    root_one: bool,
    tail_one: bool,
    limit: usize,
    mut visit: F,
) {
    let mut curr = vec![1i8; len];
    let mut emitted = 0usize;
    let mut stopped = false;

    fn dfs(
        i: usize,
        len: usize,
        curr_sum: i32,
        target_sum: i32,
        curr: &mut [i8],
        emitted: &mut usize,
        stopped: &mut bool,
        limit: usize,
        root_one: bool,
        tail_one: bool,
        visit: &mut impl FnMut(&[i8]) -> bool,
    ) {
        if *emitted >= limit || *stopped {
            return;
        }
        if i == len {
            if curr_sum == target_sum {
                *emitted += 1;
                if !visit(curr) {
                    *stopped = true;
                }
            }
            return;
        }

        if root_one && i == 0 {
            curr[0] = 1;
            dfs(
                i + 1,
                len,
                curr_sum + 1,
                target_sum,
                curr,
                emitted,
                stopped,
                limit,
                root_one,
                tail_one,
                visit,
            );
            return;
        }

        if tail_one && i == len - 1 {
            curr[i] = 1;
            dfs(
                i + 1,
                len,
                curr_sum + 1,
                target_sum,
                curr,
                emitted,
                stopped,
                limit,
                root_one,
                tail_one,
                visit,
            );
            return;
        }

        let remaining_total = (len - i - 1) as i32;
        let forced_plus = if tail_one && i < (len - 1) { 1 } else { 0 };
        let free_remaining = remaining_total - forced_plus;

        curr[i] = 1;
        let max_pos = curr_sum + 1 + forced_plus + free_remaining;
        let min_pos = curr_sum + 1 + forced_plus - free_remaining;
        if target_sum >= min_pos && target_sum <= max_pos {
            dfs(
                i + 1,
                len,
                curr_sum + 1,
                target_sum,
                curr,
                emitted,
                stopped,
                limit,
                root_one,
                tail_one,
                visit,
            );
        }

        if *stopped { return; }

        curr[i] = -1;
        let max_neg = curr_sum - 1 + forced_plus + free_remaining;
        let min_neg = curr_sum - 1 + forced_plus - free_remaining;
        if target_sum >= min_neg && target_sum <= max_neg {
            dfs(
                i + 1,
                len,
                curr_sum - 1,
                target_sum,
                curr,
                emitted,
                stopped,
                limit,
                root_one,
                tail_one,
                visit,
            );
        }
    }

    dfs(
        0,
        len,
        0,
        target_sum,
        &mut curr,
        &mut emitted,
        &mut stopped,
        limit,
        root_one,
        tail_one,
        &mut visit,
    );
}


/// Print search space statistics for a set of tuples.
/// For each tuple, shows k!n (J notation for binomial) for each sequence —
/// the number of {+1,-1} strings of the given length with the given sum.
pub(crate) fn print_search_space(problem: Problem, tuples: &[SumTuple]) {
    let n = problem.n;
    let m = problem.m();
    let mut grand_total: f64 = 0.0;
    for t in tuples {
        let kx = ((t.x + n as i32) / 2) as usize;
        let ky = ((t.y + n as i32) / 2) as usize;
        let kz = ((t.z + n as i32) / 2) as usize;
        let kw = ((t.w + m as i32) / 2) as usize;
        let cx = binom(n, kx);
        let cy = binom(n, ky);
        let cz = binom(n, kz);
        let cw = binom(m, kw);
        let prod = cx as f64 * cy as f64 * cz as f64 * cw as f64;
        grand_total += prod;
        eprintln!("  {:>2} {:>2} {:>2} {:>2}   X:{}!{}={:.3e}  Y:{}!{}={:.3e}  Z:{}!{}={:.3e}  W:{}!{}={:.3e}  total {:.3e}",
            t.x, t.y, t.z, t.w,
            kx, n, cx as f64,
            ky, n, cy as f64,
            kz, n, cz as f64,
            kw, m, cw as f64,
            prod);
    }
    eprintln!("  Brute-force search space (all tuples): {:.3e}", grand_total);
}


/// Compute binomial coefficient C(n, k) as u128 (enough for n ≤ 60).
pub(crate) fn binom(n: usize, k: usize) -> u128 {
    if k > n { return 0; }
    let k = k.min(n - k);
    let mut result = 1u128;
    for i in 0..k {
        result = result * (n - i) as u128 / (i + 1) as u128;
    }
    result
}


/// Unrank: given index `rank` in [0, C(f, r)), produce the rank-th combination
/// of choosing r positions from f slots (in colex order).
/// Writes +1/-1 into `out[start..start+f]`.
pub(crate) fn unrank_combination(rank: u128, f: usize, r: usize, out: &mut [i8], start: usize) {
    // Set all to -1, then place r ones
    for i in 0..f { out[start + i] = -1; }
    let mut remaining_rank = rank;
    let mut remaining_choose = r;
    let mut pos = f;
    while remaining_choose > 0 {
        pos -= 1;
        let c = binom(pos, remaining_choose);
        if remaining_rank >= c {
            remaining_rank -= c;
            out[start + pos] = 1;
            remaining_choose -= 1;
        }
    }
}


/// Generate ±1 sequences with a given sum in permuted (pseudo-random) order.
/// Uses an LCG bijection over [0, C(f, r)) to visit every sequence exactly once
/// but in a scattered order, so the first `limit` sequences are representative
/// of the full space rather than clustered lexicographically.
pub(crate) fn generate_sequences_permuted<F: FnMut(&[i8]) -> bool>(
    len: usize,
    target_sum: i32,
    root_one: bool,
    tail_one: bool,
    limit: usize,
    mut visit: F,
) {
    // Determine fixed positions and free count
    let fixed_sum: i32 = (if root_one { 1 } else { 0 }) + (if tail_one { 1 } else { 0 });
    let free_start = if root_one { 1 } else { 0 };
    let free_end = if tail_one { len - 1 } else { len };
    let f = free_end - free_start; // number of free positions
    let free_target = target_sum - fixed_sum; // sum needed from free positions
    // free positions have values in {-1, +1}, sum = 2*ones - f
    // so ones = (free_target + f) / 2
    if (free_target + f as i32) % 2 != 0 { return; }
    let r_signed = (free_target + f as i32) / 2;
    if r_signed < 0 || r_signed > f as i32 { return; }
    let r = r_signed as usize; // number of +1s among free positions

    let total = binom(f, r);
    let n_visit = (limit as u128).min(total);

    let mut curr = vec![1i8; len];
    if root_one { curr[0] = 1; }
    if tail_one { curr[len - 1] = 1; }

    // If the full space fits within the limit, DFS is faster (no unranking overhead).
    if total <= limit as u128 {
        generate_sequences_with_sum_visit(len, target_sum, root_one, tail_one, limit, visit);
        return;
    }

    // Bijective scatter: index i -> (a * i + c) mod total
    // `a` coprime to `total` guarantees a permutation of [0, total).
    let m = total;
    let a = {
        let mut candidate = 6364136223846793005u128 % m;
        if candidate == 0 { candidate = 1; }
        while gcd128(candidate, m) != 1 {
            candidate = (candidate + 1) % m;
            if candidate == 0 { candidate = 1; }
        }
        candidate
    };
    let c = 1442695040888963407u128 % m;

    for i in 0..n_visit {
        let rank = (a * i + c) % m;
        unrank_combination(rank, f, r, &mut curr, free_start);
        if !visit(&curr) { return; }
    }
}


pub(crate) fn gcd128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 { let t = b; b = a % b; a = t; }
    a
}


/// Generate all spectrally-valid W sequences for a given sum.
/// W is the shorter sequence (length n-1) so we materialize it; Z is streamed.
pub(crate) fn build_w_candidates(
    problem: Problem,
    w_sum: i32,
    cfg: &SearchConfig,
    spectral_w: &SpectralFilter,
    stats: &mut SearchStats,
    found: &AtomicBool,
) -> Vec<SeqWithSpectrum> {
    let individual_bound = problem.spectral_bound();
    let mut w_candidates: Vec<SeqWithSpectrum> = Vec::new();
    let mut fft_buf = FftScratch::new(spectral_w);
    generate_sequences_permuted(problem.m(), w_sum, true, false, cfg.max_w, |values| {
        if found.load(AtomicOrdering::Relaxed) { return false; }
        stats.w_generated += 1;
        if let Some(spectrum) =
            spectrum_if_ok(values, spectral_w, individual_bound, &mut fft_buf)
        {
            stats.w_spectral_ok += 1;
            w_candidates.push(SeqWithSpectrum {
                spectrum,
                seq: PackedSeq::from_values(values),
            });
        }
        true
    });
    w_candidates
}


/// Streaming Z×W pairing with spectral index for fast candidate lookup.
/// For each spectrally-valid Z, uses the index to find W candidates that pass
/// the top-4 tightest frequency constraints, then full-checks only those.
/// Calls `emit` for each valid pair; `emit` returns true to continue.
pub(crate) fn for_each_zw_pair(
    problem: Problem,
    z_sum: i32,
    w_candidates: &[SeqWithSpectrum],
    w_index: &SpectralIndex,
    cfg: &SearchConfig,
    spectral_z: &SpectralFilter,
    stats: &mut SearchStats,
    found: &AtomicBool,
    mut emit: impl FnMut(&PackedSeq, &PackedSeq, Vec<i32>, &[f64], &[f64]) -> bool,
) {
    let individual_bound = problem.spectral_bound();
    let pair_bound = cfg.max_spectral.unwrap_or(problem.spectral_bound());
    let mut fft_buf = FftScratch::new(spectral_z);
    let mut idx_buf = Vec::new();
    generate_sequences_permuted(problem.n, z_sum, true, true, cfg.max_z, |values| {
        if found.load(AtomicOrdering::Relaxed) { return false; }
        stats.z_generated += 1;
        let Some(z_spectrum) =
            spectrum_if_ok(values, spectral_z, individual_bound, &mut fft_buf) else { return true; };
        stats.z_spectral_ok += 1;
        let z_seq = PackedSeq::from_values(values);
        w_index.candidates_for(&z_spectrum, pair_bound, w_candidates, &mut idx_buf);
        for &wi in &idx_buf {
            let w = &w_candidates[wi];
            stats.candidate_pair_attempts += 1;
            if !spectral_pair_ok(&z_spectrum, &w.spectrum, pair_bound) { continue; }
            stats.candidate_pair_spectral_ok += 1;
            let zw = compute_zw_autocorr(problem, &z_seq, &w.seq);
            if !emit(&z_seq, &w.seq, zw, &z_spectrum, &w.spectrum) { return false; }
        }
        true
    });
}


pub(crate) fn stream_zw_candidates(
    problem: Problem,
    z_sum: i32,
    w_candidates: &[SeqWithSpectrum],
    w_index: &SpectralIndex,
    cfg: &SearchConfig,
    spectral_z: &SpectralFilter,
    stats: &mut SearchStats,
    found: &AtomicBool,
) -> Vec<CandidateZW> {
    let mut out = Vec::new();
    for_each_zw_pair(problem, z_sum, w_candidates, w_index, cfg, spectral_z, stats, found,
        |_z_seq, _w_seq, zw, _, _| {
            out.push(CandidateZW { zw_autocorr: zw });
            true
        });
    out
}


pub(crate) fn build_zw_candidates(
    problem: Problem,
    tuple: SumTuple,
    cfg: &SearchConfig,
    spectral_z: &SpectralFilter,
    spectral_w: &SpectralFilter,
    stats: &mut SearchStats,
    found: &AtomicBool,
) -> Vec<CandidateZW> {
    let w_candidates = build_w_candidates(problem, tuple.w, cfg, spectral_w, stats, found);
    if found.load(AtomicOrdering::Relaxed) { return Vec::new(); }
    let w_index = SpectralIndex::build(&w_candidates);
    stream_zw_candidates(problem, tuple.z, &w_candidates, &w_index, cfg, spectral_z, stats, found)
}

