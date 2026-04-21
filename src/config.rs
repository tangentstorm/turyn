//! CLI configuration, outfix specification, and search-config parsing helpers.

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

use crate::SPECTRAL_FREQS;
use crate::enumerate::*;
use crate::legacy_search::*;
use crate::mdd_pipeline::*;
use crate::spectrum::*;
use crate::stochastic::*;
use crate::types::*;
use crate::xy_sat::*;

/// A specific (Z, W) boundary — optionally also (X, Y) — encoded as hex
/// prefix/suffix pairs.  Each `*_bits` value follows the internal
/// encoding used by `expand_boundary_bits`: bit `i` of the prefix/suffix
/// word is position `i` of the corresponding k-length prefix/suffix,
/// with LSB = leftmost position.
#[derive(Clone, Debug)]
pub(crate) struct OutfixSpec {
    /// MDD-boundary Z bits (packed as in `expand_boundary_bits`): bits
    /// 0..k-1 = prefix Z[0..k], bits k..2k-1 = suffix Z[n-k..n].
    pub(crate) z_bits: u32,
    /// Same for W.
    pub(crate) w_bits: u32,
    /// Optional XY pinning (same encoding as z_bits/w_bits).  When set,
    /// the XY search is restricted to this single (x_bits, y_bits).
    pub(crate) xy_bits: Option<(u32, u32)>,
    /// Middle-position pins for Z: `(middle_idx, value)` where
    /// `middle_idx ∈ 0..middle_n` indexes `Z[k+middle_idx]` and `value`
    /// is ±1.  Forces the corresponding SAT var in SolveWZ.
    pub(crate) z_middle_pins: Vec<(usize, i8)>,
    /// Same for W (indexing `W[k+middle_idx]` with `middle_idx ∈ 0..middle_m`).
    pub(crate) w_middle_pins: Vec<(usize, i8)>,
    /// Same for X (full sequence position `k+middle_idx`).  Used by the
    /// XY SAT to pin middle bits via assumptions.
    pub(crate) x_middle_pins: Vec<(usize, i8)>,
    /// Same for Y.
    pub(crate) y_middle_pins: Vec<(usize, i8)>,
}

/// Parse `--outfix=<prefHex>...<sufHex>`.  BDKR hex encoding: each hex
/// digit packs all four sequences (A, B, C, D) = (X, Y, Z, W) at one
/// position.  With `+1 → 0, -1 → 1` bit polarity, the digit is
/// `8·bit(A) + 4·bit(B) + 2·bit(C) + bit(D)`.  The last digit (position
/// `n-1`) is 3-bit (only A, B, C, since W has length `n-1`).
///
/// `prefHex` has `k` digits (positions `0..k`).  `sufHex` has `k+1`
/// digits (positions `n-1-k..n`): the leading digit picks up `W[n-1-k]`
/// (the first element of W's boundary suffix, which BDKR places one
/// digit earlier than X/Y/Z's suffix), the next `k-1` digits fill in
/// the rest of the 4-bit suffix, and the trailing digit is the 3-bit
/// `h_{n-1}`.
///
/// Example (canonical TT(18) at `k=5`):
/// ```text
///   X = "++-+++++++++-+--++"
///   Y = "++----++-+---+-+-+"
///   Z = "++-+++----+-+-++--"
///   W = "++----+--+--+++-+"
///     h_0..h_4   = 00f55         (prefix, k=5 digits)
///     h_12..h_17 = c2c961        (suffix, k+1=6 digits; last digit 001=1 is 3-bit)
///   --outfix=00f55...c2c961
/// ```
pub(crate) fn parse_outfix(s: &str, n: usize, k: usize) -> Result<OutfixSpec, String> {
    let parts: Vec<&str> = s.split("...").collect();
    if parts.len() != 2 {
        return Err(format!("--outfix: expected 'prefHex...sufHex', got '{s}'"));
    }
    let pref_hex = parts[0].trim_start_matches("0x");
    let suf_hex = parts[1].trim_start_matches("0x");
    // Minimum: k prefix digits (the MDD boundary).  Maximum: up to n
    // (full sequence pinned).  Longer prefixes pin middle Z/W/X/Y
    // positions via unit clauses added at SAT build time.
    if pref_hex.len() < k {
        return Err(format!(
            "--outfix: prefix has {} hex digits, need at least k={k}",
            pref_hex.len()
        ));
    }
    // Suffix minimum is k+1 (the MDD boundary + h_{n-1-k}); maximum is
    // n-pref_len (so pref+suf don't overlap).
    if suf_hex.len() < k + 1 {
        return Err(format!(
            "--outfix: suffix has {} hex digits, need at least k+1={}",
            suf_hex.len(),
            k + 1
        ));
    }
    if pref_hex.len() + suf_hex.len() > n + 1 {
        return Err(format!(
            "--outfix: prefix ({}) + suffix ({}) hex digits exceed n+1={}",
            pref_hex.len(),
            suf_hex.len(),
            n + 1
        ));
    }
    fn hex_digit(c: char) -> Result<u32, String> {
        c.to_digit(16)
            .ok_or_else(|| format!("--outfix: '{c}' is not a hex digit"))
    }
    // BDKR: bit polarity 0=+1, 1=-1.  For boundary bits we use the
    // packed u32 convention (`expand_boundary_bits`): internal bit 1 = +1.
    let set = |bits: &mut u32, pos: usize, bdkr_bit: u32| {
        if bdkr_bit == 0 {
            *bits |= 1 << pos;
        }
    };
    // Convert BDKR polarity bit to ±1 value.
    let polarity_val = |bdkr_bit: u32| -> i8 { if bdkr_bit == 0 { 1 } else { -1 } };

    let (mut x_bits, mut y_bits, mut z_bits, mut w_bits) = (0u32, 0u32, 0u32, 0u32);
    let mut z_middle_pins: Vec<(usize, i8)> = Vec::new();
    let mut w_middle_pins: Vec<(usize, i8)> = Vec::new();
    let mut x_middle_pins: Vec<(usize, i8)> = Vec::new();
    let mut y_middle_pins: Vec<(usize, i8)> = Vec::new();

    // Prefix: h_0..h_{len_pref-1}.  For i < k, this is boundary (packed
    // into x/y/z/w_bits).  For i >= k, this pins the middle position
    // k + (i - k) = i for all four sequences.  Middle index is (i - k).
    for (i, c) in pref_hex.chars().enumerate() {
        let d = hex_digit(c)?;
        if d > 0xf {
            return Err(format!("--outfix: prefix digit {i} '{c}' > f"));
        }
        if i < k {
            set(&mut x_bits, i, (d >> 3) & 1);
            set(&mut y_bits, i, (d >> 2) & 1);
            set(&mut z_bits, i, (d >> 1) & 1);
            set(&mut w_bits, i, d & 1);
        } else {
            let mid = i - k;
            x_middle_pins.push((mid, polarity_val((d >> 3) & 1)));
            y_middle_pins.push((mid, polarity_val((d >> 2) & 1)));
            z_middle_pins.push((mid, polarity_val((d >> 1) & 1)));
            w_middle_pins.push((mid, polarity_val(d & 1)));
        }
    }

    // Suffix: covers positions (n - suf_len)..n-1 for X/Y/Z and a
    // W-shifted-by-one range for W.  See the function-level doc for the
    // BDKR suffix alignment.
    //
    //   - Digit 0 of suffix (`h_{n-1-suf_len+1}` = position n - suf_len):
    //     only W uses the D bit (W's suffix starts one position earlier
    //     than X/Y/Z's, since len(W) = n-1 < len(X)=n).  Whether X/Y/Z
    //     at this position is middle or boundary depends on suf_len:
    //     if suf_len - 1 <= k, it's strictly middle; otherwise X/Y/Z's
    //     A/B/C bits are ignored here (they're handled at the matching
    //     position via pref or later suffix digits).
    //   - Digits 1..suf_len-1: 4-bit, cover position n - suf_len + i
    //     for X/Y/Z and W (shifted).
    //   - Last digit: 3-bit, position n-1 for X/Y/Z only (no W).
    //
    // To keep things simple we honor the legacy convention: the first
    // suffix digit pins W only, the middle digits pin all four, and the
    // last digit pins XYZ only.  A suffix of exactly k+1 reproduces the
    // boundary-only encoding; a longer suffix adds middle pins going
    // inward (toward the center of the sequence).
    let suf_chars: Vec<char> = suf_hex.chars().collect();
    let suf_len = suf_chars.len();
    for (i, &c) in suf_chars.iter().enumerate() {
        let d = hex_digit(c)?;
        // W's position for this suffix digit: positions m-suf_len..m-1
        // where m = n-1.  Digit i ↔ W position (n - suf_len + i).  When
        // the W-pos falls in the boundary range [m-k..m-1], write to
        // w_bits; else pin the middle.
        let w_pos_abs: Option<usize> = Some(n - suf_len + i);
        // XYZ position for this suffix digit: positions n-suf_len+1..n-1
        // (shifted by one because digit 0 of suffix has no XYZ).  For
        // i == 0, XYZ is skipped.  For i > 0, digit i ↔ XYZ position
        // (n - suf_len + i).
        let xyz_pos_abs: Option<usize> = if i == 0 { None } else { Some(n - suf_len + i) };

        if i == 0 {
            // Only W at this digit.  Other 3 bits must be zero (A=B=C=0).
            if (d >> 1) != 0 {
                return Err(format!(
                    "--outfix: suffix digit 0 '{c}' has X/Y/Z bits set — must be 0..1 (only D bit / W used)"
                ));
            }
        } else if i == suf_len - 1 {
            // Last digit: 3-bit (no W).
            if d > 0x7 {
                return Err(format!(
                    "--outfix: last suffix digit '{c}' > 7 (must be 3-bit)"
                ));
            }
        }

        if let Some(wp) = w_pos_abs {
            let m = n - 1;
            // W boundary suffix occupies positions [m-k, m).  Internal
            // bit: k + (wp - (m - k)) = wp - m + 2k.
            if wp >= m - k && wp < m {
                set(&mut w_bits, k + (wp - (m - k)), d & 1);
            } else if wp < m - k {
                // W middle position wp, which is index (wp - k) within
                // the middle range [k, m-k).
                if i != suf_len - 1 {
                    // last digit has no W anyway
                    w_middle_pins.push((wp - k, polarity_val(d & 1)));
                }
            }
            // wp == m is out of range (W has no position m).
        }
        if let Some(xp) = xyz_pos_abs {
            // Last digit is 3-bit (no W, so A=bit 2, B=bit 1, C=bit 0).
            // Other digits are 4-bit (A=bit 3, B=bit 2, C=bit 1, D=bit 0).
            let is_last_3bit = i == suf_len - 1;
            let (x_b, y_b, z_b) = if is_last_3bit {
                ((d >> 2) & 1, (d >> 1) & 1, d & 1)
            } else {
                ((d >> 3) & 1, (d >> 2) & 1, (d >> 1) & 1)
            };
            if xp >= n - k && xp < n {
                // Boundary suffix: internal bit = k + (xp - (n - k)) = xp - n + 2k.
                set(&mut x_bits, k + (xp - (n - k)), x_b);
                set(&mut y_bits, k + (xp - (n - k)), y_b);
                set(&mut z_bits, k + (xp - (n - k)), z_b);
            } else if xp >= k && xp < n - k {
                // Middle.
                let mid = xp - k;
                x_middle_pins.push((mid, polarity_val(x_b)));
                y_middle_pins.push((mid, polarity_val(y_b)));
                z_middle_pins.push((mid, polarity_val(z_b)));
            }
        }
    }

    Ok(OutfixSpec {
        z_bits,
        w_bits,
        xy_bits: Some((x_bits, y_bits)),
        z_middle_pins,
        w_middle_pins,
        x_middle_pins,
        y_middle_pins,
    })
}

#[derive(Clone, Debug)]
pub(crate) struct SearchConfig {
    pub(crate) problem: Problem,
    pub(crate) theta_samples: usize,
    pub(crate) max_z: usize,
    pub(crate) max_w: usize,
    pub(crate) benchmark_repeats: usize,
    pub(crate) stochastic: bool,
    pub(crate) stochastic_seconds: u64,
    /// London §5.1: restrict spectral pair sum to ≤ max_spectral.
    /// If None, uses the default spectral_bound (= (6n-2)/2).
    /// Setting this lower than spectral_bound trades completeness for speed.
    pub(crate) max_spectral: Option<f64>,
    /// Test mode: verify a known solution or test SAT on known Z/W.
    /// Format: 4 strings of +/- chars, e.g. "++--+-" for [1,1,-1,-1,1,-1].
    pub(crate) verify_seqs: Option<[String; 4]>,
    /// Test SAT X/Y with given Z/W (2 strings of +/- chars).
    pub(crate) test_zw: Option<[String; 2]>,
    /// Conflict limit per SAT solve (0 = unlimited).
    pub(crate) conflict_limit: u64,
    /// Test a specific sum-tuple (x,y,z,w) only.
    pub(crate) test_tuple: Option<SumTuple>,
    /// Force the MDD search to only visit one specific (Z, W) boundary.
    /// Format: `z_pref_hex...z_suf_hex:w_pref_hex...w_suf_hex`.  Each hex
    /// encodes `k` bits with position 0 as LSB (same encoding as the
    /// internal `z_bits` / `w_bits`).  E.g., at `k=7`, the canonical
    /// TT(26) boundary is `--outfix=03...21:5f...51`.
    pub(crate) test_outfix: Option<OutfixSpec>,
    /// Run only Phase A (print tuples) or Phase B (print Z/W pairs).
    pub(crate) phase_only: Option<String>,
    /// Dump DIMACS CNF to this path instead of solving.
    pub(crate) dump_dimacs: Option<String>,
    /// SAT solver feature flags.
    pub(crate) sat_config: radical::SolverConfig,
    /// Time limit in seconds for the hybrid / MDD search (0 = unlimited).
    pub(crate) sat_secs: u64,
    /// Use quad PB encoding instead of totalizer.
    pub(crate) quad_pb: bool,
    /// MDD boundary width (default: 8).
    pub(crate) mdd_k: usize,
    /// Extension filter: prune dead boundaries by checking k+N extensibility (0 = off).
    pub(crate) mdd_extend: usize,
    /// In the MDD-walker producers (`--wz=apart|together`), solve W and Z
    /// with a single combined SAT call instead of the default SolveW →
    /// SolveZ two-stage pipeline. Set to `true` by `--wz=together`.
    pub(crate) wz_together: bool,
    /// Explicit (Z, W) producer selection via `--wz=cross|together|apart`.
    /// `None` defaults to `WzMode::Cross`. The legacy `--wz-together`
    /// flag and the `--mdd-k=` / `--mdd-extend=` shortcuts also set this
    /// when it's still `None`.
    pub(crate) wz_mode: Option<WzMode>,
    /// Hypothetical XY canonical-rep constraint: for 1 <= i <= n with
    /// U_i := x_i * y_i, enforce U_1 = +1, U_n = +1, and
    /// U_i = -U_{n+1-i} for 2 <= i <= n-1. Endpoint pins already hold
    /// from rule (i) (x_0=y_0=x_{n-1}=y_{n-1}=+1), so only the middle
    /// pairwise equalities are added. Enabled via `--conj-xy-product`
    /// (implies `X · Y = 2`; see conjectures/xy-product.md).
    pub(crate) conj_xy_product: bool,
    /// ZW high-lag U-bound tightness conjecture: enforce equality
    /// `|N_Z(s) + N_W(s)| = ((n - s) + N_U(s)) / 2` at s in
    /// {n-1, n-2, n-3}, where `N_U(s) = Σ_i u_i u_{i+s}`,
    /// `u_i = x_i y_i`. Applied as an XY-stage pre-filter on known
    /// z,w boundary bits + x,y boundary bits. Enabled via
    /// `--conj-zw-bound` (see conjectures/zw-u-bound-tight.md).
    pub(crate) conj_zw_bound: bool,
    /// Auto-select a single sum-tuple with the smallest search space
    /// (minimum `C(n,·) * C(n,·) * C(n,·) * C(n-1,·)`) and restrict
    /// the search to it, like `--tuple=` but automatic.  Density
    /// (#solutions / space) is unknowable a priori at open n, so we
    /// pick the best proxy we can compute: minimum space.  If
    /// `--tuple=` is also provided it takes priority and this flag
    /// is a no-op. Enabled via `--conj-tuple` (see
    /// conjectures/positive-tuple.md).
    pub(crate) conj_tuple: bool,
}

/// Which (Z, W) candidate producer feeds the shared XY SAT stage.
///
/// All three modes funnel through the same `SolveXyPerCandidate` fast
/// path; they differ only in how they *generate* the `(Z, W)` pairs that
/// the XY consumer gets to see.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum WzMode {
    /// Brute-force full Z and W sequences, spectral-filter each side,
    /// and cross-match them via `SpectralIndex` buckets that enforce the
    /// pair spectral bound `|Z(ω)|² + |W(ω)|² ≤ 3n-1`. The classic
    /// `run_hybrid_search` producer — the fastest path at small n.
    Cross,
    /// MDD boundary walker feeding a combined W+Z SAT call (one solve()
    /// produces both the W and Z middle). `run_mdd_sat_search` with
    /// `wz_together = true`.
    Together,
    /// MDD boundary walker feeding the SolveW → SolveZ two-stage SAT
    /// pipeline. `run_mdd_sat_search` with `wz_together = false`.
    Apart,
    /// Synchronized 4-sequence heuristic walker. Builds the bouncing
    /// boundary MDD on the fly (no `mdd-k.bin` required), scoring each
    /// 16-way level by running autocorrelation pressure. Persistent SAT
    /// solver absorbs full BDKR (i)–(vi) + Turyn identity as per-lag
    /// quad PB; learned clauses persist across the walk. See `sync_walker`.
    Sync,
}

impl Default for SearchConfig {
    fn default() -> Self {
        Self {
            problem: Problem::new(0),
            theta_samples: 128,
            max_z: 200_000,
            max_w: 200_000,
            benchmark_repeats: 0,
            stochastic: false,
            stochastic_seconds: 0,
            max_spectral: None,
            verify_seqs: None,
            test_zw: None,
            conflict_limit: 0,
            test_tuple: None,
            test_outfix: None,
            phase_only: None,
            dump_dimacs: None,
            sat_config: radical::SolverConfig::default(),
            sat_secs: 0,
            quad_pb: true,
            mdd_k: 8,
            mdd_extend: 0,
            wz_together: false,
            wz_mode: None,
            conj_xy_product: false,
            conj_zw_bound: false,
            conj_tuple: false,
        }
    }
}

impl SearchConfig {
    /// Resolve the effective `WzMode`: explicit `--wz` (or a legacy
    /// alias that populated `wz_mode`) if set, otherwise the
    /// `WzMode::Cross` default.
    pub(crate) fn effective_wz_mode(&self) -> WzMode {
        self.wz_mode.unwrap_or(WzMode::Cross)
    }

    /// Apply the auto-defaults that the unified search branch in `main`
    /// would otherwise apply lazily: pick `--wz=together` when an
    /// `mdd-k.bin` is present, fall back to `--wz=cross` with `mdd_k=7`
    /// otherwise, then clamp `mdd_k` against `n` / `m`.  Returns the
    /// final `(mode, mdd_k)` so callers can print them.
    pub(crate) fn resolve_for_unified_search(&mut self) -> (WzMode, usize) {
        if self.wz_mode.is_none() {
            let default_k = self.mdd_k == SearchConfig::default().mdd_k;
            let try_k = if default_k { 5 } else { self.mdd_k };
            let max_k = try_k.min((self.problem.n - 1) / 2);
            let has_mdd = (1..=max_k)
                .rev()
                .any(|k| std::path::Path::new(&format!("mdd-{}.bin", k)).exists());
            if has_mdd {
                self.wz_mode = Some(WzMode::Together);
                if default_k {
                    self.mdd_k = 5;
                }
                if self.mdd_extend == 0 {
                    self.mdd_extend = 1;
                }
            }
        }
        let mode = self.effective_wz_mode();
        if mode == WzMode::Cross && self.mdd_k == SearchConfig::default().mdd_k {
            self.mdd_k = 7;
        }
        self.wz_together = matches!(mode, WzMode::Together);
        let m = self.problem.m();
        let mdd_k = self.mdd_k.min((self.problem.n - 1) / 2).min(m / 2);
        (mode, mdd_k)
    }

    /// Render the resolved CLI configuration as a single-line summary.
    /// Includes both user-supplied values and auto-defaults so the user
    /// can see exactly what the run is doing.
    pub(crate) fn settings_line(&self, mode: Option<WzMode>, mdd_k: Option<usize>) -> String {
        let mut parts: Vec<String> = Vec::new();
        parts.push(format!("--n={}", self.problem.n));
        if let Some(m) = mode {
            let label = match m {
                WzMode::Cross => "cross",
                WzMode::Together => "together",
                WzMode::Apart => "apart",
                WzMode::Sync => "sync",
            };
            parts.push(format!("--wz={label}"));
        }
        if let Some(k) = mdd_k {
            parts.push(format!("--mdd-k={k}"));
        }
        parts.push(format!("--mdd-extend={}", self.mdd_extend));
        parts.push(format!("--theta={}", self.theta_samples));
        parts.push(format!("--max-z={}", self.max_z));
        parts.push(format!("--max-w={}", self.max_w));
        if let Some(s) = self.max_spectral {
            parts.push(format!("--max-spectral={s}"));
        }
        parts.push(format!("--conflict-limit={}", self.conflict_limit));
        if self.sat_secs > 0 {
            parts.push(format!("--sat-secs={}", self.sat_secs));
        }
        parts.push(format!("--quad-pb={}", self.quad_pb));
        if self.sat_config.ema_restarts {
            parts.push("--ema-restarts".into());
        }
        if self.sat_config.probing {
            parts.push("--probing".into());
        }
        if self.sat_config.rephasing {
            parts.push("--rephasing".into());
        }
        if self.sat_config.xor_propagation {
            parts.push("--xor-propagation".into());
        }
        if self.stochastic {
            parts.push("--stochastic".into());
            if self.stochastic_seconds > 0 {
                parts.push(format!("--stochastic-secs={}", self.stochastic_seconds));
            }
        }
        if self.benchmark_repeats > 0 {
            parts.push(format!("--benchmark={}", self.benchmark_repeats));
        }
        if let Some(t) = self.test_tuple.as_ref() {
            parts.push(format!("--tuple={t}"));
        }
        if let Some(p) = self.phase_only.as_ref() {
            parts.push(format!("--{p}"));
        }
        if let Some(d) = self.dump_dimacs.as_ref() {
            parts.push(format!("--dump-dimacs={d}"));
        }
        let threads = std::env::var("TURYN_THREADS")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or_else(num_cpus_or_one);
        format!("turyn settings: {}  (threads={threads})", parts.join(" "))
    }
}

/// Best-effort parallelism count: prefer `RAYON_NUM_THREADS`, then
/// `std::thread::available_parallelism`, then 1. Matches the worker
/// count rayon spawns by default.
pub(crate) fn num_cpus_or_one() -> usize {
    if let Ok(v) = std::env::var("RAYON_NUM_THREADS") {
        if let Ok(n) = v.parse() {
            return n;
        }
    }
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
}
