//! Core problem-domain types: Problem, PackedSeq, SumTuple, and shared helpers.

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
use crate::spectrum::*;
use crate::stochastic::*;
use crate::xy_sat::*;
use crate::SPECTRAL_FREQS;


#[derive(Clone, Copy, Debug)]
pub(crate) struct Problem {
    pub(crate) n: usize,
}

impl Problem {
    pub(crate) fn new(n: usize) -> Self {
        assert!(n == 0 || n >= 2, "n must be at least 2");
        Self { n }
    }

    pub(crate) fn m(self) -> usize {
        self.n - 1
    }

    pub(crate) fn target_energy(self) -> i32 {
        (6 * self.n as i32) - 2
    }

    pub(crate) fn spectral_bound(self) -> f64 {
        self.target_energy() as f64 / 2.0
    }

    pub(crate) fn valid_w_values(self) -> Vec<i32> {
        let max_abs = (((self.target_energy() as f64) / 2.0).sqrt().floor() as i32).max(1);
        (-max_abs..=max_abs).filter(|v| v.abs() % 2 == 1).collect()
    }
}


#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct PackedSeq {
    pub(crate) len: usize,
    pub(crate) bits: Vec<u64>,
}

impl PackedSeq {
    pub(crate) fn new(len: usize) -> Self {
        let words = len.div_ceil(64);
        Self {
            len,
            bits: vec![0; words],
        }
    }

    pub(crate) fn from_values(values: &[i8]) -> Self {
        let mut seq = Self::new(values.len());
        for (i, &v) in values.iter().enumerate() {
            seq.set(i, v);
        }
        seq
    }

    pub(crate) fn len(&self) -> usize {
        self.len
    }

    pub(crate) fn get(&self, idx: usize) -> i8 {
        let word = self.bits[idx / 64];
        let bit = (word >> (idx % 64)) & 1;
        if bit == 1 { 1 } else { -1 }
    }

    pub(crate) fn set(&mut self, idx: usize, value: i8) {
        debug_assert!(value == 1 || value == -1);
        let mask = 1u64 << (idx % 64);
        let word = &mut self.bits[idx / 64];
        if value == 1 {
            *word |= mask;
        } else {
            *word &= !mask;
        }
    }

    pub(crate) fn sum(&self) -> i32 {
        (0..self.len).map(|i| self.get(i) as i32).sum()
    }

    #[allow(dead_code)]
    pub(crate) fn reverse(&self) -> Self {
        let mut out = Self::new(self.len);
        for i in 0..self.len {
            out.set(i, self.get(self.len - 1 - i));
        }
        out
    }

    #[allow(dead_code)]
    pub(crate) fn negate(&self) -> Self {
        let mut out = Self::new(self.len);
        for i in 0..self.len {
            out.set(i, -self.get(i));
        }
        out
    }

    #[allow(dead_code)]
    pub(crate) fn alternate(&self) -> Self {
        let mut out = Self::new(self.len);
        for i in 0..self.len {
            let mut v = self.get(i);
            if i % 2 == 1 {
                v = -v;
            }
            out.set(i, v);
        }
        out
    }

    pub(crate) fn autocorrelation(&self, shift: usize) -> i32 {
        debug_assert!(shift < self.len);
        let mut acc = 0;
        let limit = self.len - shift;
        let mut i = 0usize;
        while i + 4 <= limit {
            acc += (self.get(i) as i32) * (self.get(i + shift) as i32);
            acc += (self.get(i + 1) as i32) * (self.get(i + 1 + shift) as i32);
            acc += (self.get(i + 2) as i32) * (self.get(i + 2 + shift) as i32);
            acc += (self.get(i + 3) as i32) * (self.get(i + 3 + shift) as i32);
            i += 4;
        }
        while i < limit {
            acc += (self.get(i) as i32) * (self.get(i + shift) as i32);
            i += 1;
        }
        acc
    }


    #[allow(dead_code)]
    pub(crate) fn as_string(&self) -> String {
        (0..self.len)
            .map(|i| if self.get(i) == 1 { '+' } else { '-' })
            .collect()
    }
}


/// Extract a ±1 sequence from a SAT solver's assignment.
pub(crate) fn extract_seq(solver: &radical::Solver, var_fn: impl Fn(usize) -> i32, len: usize) -> PackedSeq {
    PackedSeq::from_values(&extract_vals(solver, var_fn, len))
}


/// Extract ±1 values from a SAT solver's assignment.
pub(crate) fn extract_vals(solver: &radical::Solver, var_fn: impl Fn(usize) -> i32, len: usize) -> Vec<i8> {
    (0..len).map(|i| if solver.value(var_fn(i)) == Some(true) { 1 } else { -1 }).collect()
}


/// Expand packed boundary bits into ±1 prefix and suffix arrays.
/// Low k bits → prefix, next k bits → suffix.
pub(crate) fn expand_boundary_bits(bits: u32, k: usize) -> (Vec<i8>, Vec<i8>) {
    let prefix: Vec<i8> = (0..k).map(|i| if (bits >> i) & 1 == 1 { 1 } else { -1 }).collect();
    let suffix: Vec<i8> = (0..k).map(|i| if (bits >> (k + i)) & 1 == 1 { 1 } else { -1 }).collect();
    (prefix, suffix)
}


/// Format a sequence as a colorized +/- string for terminal display.
/// '+' gets black text on light gray background, '-' gets white text on dark gray.
/// Copies as plain +/- from most terminals.
pub(crate) fn colored_pm(seq: &PackedSeq) -> String {
    let mut out = String::new();
    for i in 0..seq.len() {
        if seq.get(i) == 1 {
            out.push_str("\x1b[30;47m+\x1b[0m");
        } else {
            out.push_str("\x1b[37;100m-\x1b[0m");
        }
    }
    out
}


pub(crate) fn print_solution(label: &str, x: &PackedSeq, y: &PackedSeq, z: &PackedSeq, w: &PackedSeq) {
    use std::io::Write;
    let n = x.len().max(y.len()).max(z.len()).max(w.len());
    let mut buf = format!("\n{}\n", label);
    for (name, seq) in [("X", x), ("Y", y), ("Z", z), ("W", w)] {
        let pad = " ".repeat(n.saturating_sub(seq.len()));
        buf.push_str(&format!("{} =: '{}'{}  NB. {}\n", name, colored_pm(seq), pad, seq.sum()));
    }
    buf.push('\n');
    let stdout = std::io::stdout();
    let mut lock = stdout.lock();
    let _ = lock.write_all(buf.as_bytes());
    let _ = lock.flush();
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) struct SumTuple {
    pub(crate) x: i32,
    pub(crate) y: i32,
    pub(crate) z: i32,
    pub(crate) w: i32,
}

impl SumTuple {
    /// Normalization key for tuple deduplication in hybrid search.
    ///
    /// Unsigned only (folds T1, per-sequence negation):
    /// `(|σ_X|, |σ_Y|, |σ_Z|, |σ_W|)`.  Sign freedom is restored per
    /// sequence inside the SAT via `PbSetEq`, whose `V` is built from
    /// `{+|σ|, -|σ|}` of the stored tuple (and, for the MDD pipeline's
    /// middle SATs, shifted by the boundary contribution).
    ///
    /// Does **not** fold T4 (X↔Y swap).  Rule (vi) breaks T4 at the
    /// position level — the canonical representative has a specific
    /// (σ_X, σ_Y) orientation, and the orbit's T4-image has a
    /// *different* orientation that fails rule (vi) on the same
    /// position bits.  Sorting |σ_X|, |σ_Y| here would silently
    /// exclude orbits whose canonical has max(|σ_X|, |σ_Y|) = |σ_Y|
    /// (e.g., TT(26) canonical has σ = (−4, +8, −6, +1): σ_Y is the
    /// max).  We accept the up-to-2× tuple-enumeration cost to keep
    /// every orbit reachable.
    ///
    /// Verified empirically at n=6: 4 distinct BDKR orbits exist and
    /// 2 of them have at least one negative sum in their canonical
    /// representative.  Under this unsigned key + `PbSetEq` sum
    /// encoding, all 4 orbits are reachable.
    pub(crate) fn norm_key(&self) -> (i32, i32, i32, i32) {
        (self.x.abs(), self.y.abs(), self.z.abs(), self.w.abs())
    }

}

impl fmt::Display for SumTuple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(x={}, y={}, z={}, w={})",
            self.x, self.y, self.z, self.w
        )
    }
}


pub(crate) fn verify_tt(problem: Problem, x: &PackedSeq, y: &PackedSeq, z: &PackedSeq, w: &PackedSeq) -> bool {
    if x.len() != problem.n
        || y.len() != problem.n
        || z.len() != problem.n
        || w.len() != problem.m()
    {
        return false;
    }

    for s in 1..problem.n {
        let nx = x.autocorrelation(s);
        let ny = y.autocorrelation(s);
        let nz = z.autocorrelation(s);
        let nw = if s < problem.m() {
            w.autocorrelation(s)
        } else {
            0
        };
        if nx + ny + 2 * nz + 2 * nw != 0 {
            return false;
        }
    }
    true
}


