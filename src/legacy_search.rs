//! Legacy hybrid search driver (phases A+B+C), verification, and benchmarks.

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
use crate::mdd_pipeline::*;
use crate::spectrum::*;
use crate::stochastic::*;
use crate::types::*;
use crate::xy_sat::*;
use crate::SPECTRAL_FREQS;


#[derive(Default, Clone, Debug)]
pub(crate) struct SearchStats {
    pub(crate) z_generated: usize,
    pub(crate) z_spectral_ok: usize,
    pub(crate) w_generated: usize,
    pub(crate) w_spectral_ok: usize,
    pub(crate) candidate_pair_attempts: usize,
    pub(crate) candidate_pair_spectral_ok: usize,
    pub(crate) xy_nodes: usize,
    pub(crate) phase_b_nanos: u64,
}


impl SearchStats {
    pub(crate) fn merge_from(&mut self, other: &SearchStats) {
        self.z_generated += other.z_generated;
        self.z_spectral_ok += other.z_spectral_ok;
        self.w_generated += other.w_generated;
        self.w_spectral_ok += other.w_spectral_ok;
        self.candidate_pair_attempts += other.candidate_pair_attempts;
        self.candidate_pair_spectral_ok += other.candidate_pair_spectral_ok;
        self.xy_nodes += other.xy_nodes;
        self.phase_b_nanos += other.phase_b_nanos;
    }
}


/// Per-worker warm-start state for phase transfer between SAT solves.
/// Each worker captures the last solver's phase vector and injects it
/// into the next clone-and-solve cycle — a cheap way to preserve value
/// hints across closely-related XY SAT instances.
pub(crate) struct WarmStartState {
    pub(crate) phase: Option<Vec<bool>>,
    pub(crate) inject_phase: bool,
}


#[derive(Clone, Debug)]
pub(crate) struct SearchReport {
    pub(crate) stats: SearchStats,
    pub(crate) elapsed: std::time::Duration,
    pub(crate) found_solution: bool,
}

// ==================== Unified SAT work-item types ====================


pub(crate) fn run_benchmark(cfg: &SearchConfig) {
    if cfg.stochastic {
        run_stochastic_benchmark(cfg);
    } else {
        run_hybrid_benchmark(cfg);
    }
}


pub(crate) fn run_hybrid_benchmark(cfg: &SearchConfig) {
    let repeats = cfg.benchmark_repeats.max(1);
    let warmup = run_hybrid_search(cfg, false);
    println!(
        "benchmark,warmup,elapsed_ms={:.3},found_solution={}",
        warmup.elapsed.as_secs_f64() * 1000.0,
        warmup.found_solution
    );
    println!("benchmark,run,elapsed_ms,found_solution");
    let mut elapsed_ms = Vec::with_capacity(repeats);
    for run in 1..=repeats {
        let report = run_hybrid_search(cfg, false);
        let ms = report.elapsed.as_secs_f64() * 1000.0;
        elapsed_ms.push(ms);
        println!("benchmark,{},{:.3},{}", run, ms, report.found_solution);
    }
    elapsed_ms.sort_by(|a, b| a.partial_cmp(b).unwrap_or(Ordering::Equal));
    let median = elapsed_ms[elapsed_ms.len() / 2];
    let mean = elapsed_ms.iter().sum::<f64>() / elapsed_ms.len() as f64;
    println!("benchmark,summary,mean_ms={:.3},median_ms={:.3},repeats={}", mean, median, repeats);
}


pub(crate) fn run_stochastic_benchmark(cfg: &SearchConfig) {
    let secs = if cfg.stochastic_seconds > 0 { cfg.stochastic_seconds } else { 10 };
    let repeats = cfg.benchmark_repeats.max(1);
    // Warmup
    let warmup = stochastic_search(cfg.problem, cfg.test_tuple.as_ref(), false, secs);
    let warmup_rate = warmup.stats.xy_nodes as f64 / warmup.elapsed.as_secs_f64();
    println!(
        "benchmark,warmup,elapsed_s={:.3},flips={},flips_per_sec={:.0},found_solution={}",
        warmup.elapsed.as_secs_f64(),
        warmup.stats.xy_nodes,
        warmup_rate,
        warmup.found_solution
    );
    println!("benchmark,run,elapsed_s,flips,flips_per_sec,found_solution");
    let mut rates = Vec::with_capacity(repeats);
    for run in 1..=repeats {
        let report = stochastic_search(cfg.problem, cfg.test_tuple.as_ref(), false, secs);
        let rate = report.stats.xy_nodes as f64 / report.elapsed.as_secs_f64();
        rates.push(rate);
        println!(
            "benchmark,{},{:.3},{},{:.0},{}",
            run,
            report.elapsed.as_secs_f64(),
            report.stats.xy_nodes,
            rate,
            report.found_solution
        );
    }
    rates.sort_by(|a, b| a.partial_cmp(b).unwrap_or(Ordering::Equal));
    let median = rates[rates.len() / 2];
    let mean = rates.iter().sum::<f64>() / rates.len() as f64;
    println!(
        "benchmark,summary,mean_flips_per_sec={:.0},median_flips_per_sec={:.0},repeats={}",
        mean, median, repeats
    );
}


/// **`solve_xyzw`** — solve all four Turyn sequences (X, Y, Z, W) in a
/// single SAT call, with the full ZW+XY MDD as a native constraint and
/// the full Turyn identity as per-lag quad PB.
///
/// Designed for cube-and-conquer: the caller may supply a
/// `partial_boundary` cube (list of signed SAT literals) that pins some
/// boundary bits. An outer MDD walker can shard the boundary space into
/// independent cubes and dispatch each to a different worker/machine;
/// each cube becomes an independent SAT call.
///
/// SAT variable layout (1-based):
///   X[0..n]   -> 1..=n
///   Y[0..n]   -> n+1..=2n
///   Z[0..n]   -> 2n+1..=3n
///   W[0..m]   -> 3n+1..=3n+m   (m = n-1)
///
/// Constraints added:
///   - BDKR Canonical1: 6 endpoint fixings (see inline comment).
///   - BDKR Canonical6: A/B tie-break clauses.
///   - 4 sum PB constraints encoding tuple sums.
///   - n-1 quad PB constraints encoding the full Turyn identity at each
///     lag s: agree_X(s) + agree_Y(s) + 2*agree_Z(s) + 2*agree_W(s) =
///     3n - 3s - 1  (for s < m); for s = m..n-1 the W term drops and
///     target becomes 2(n-s). The quad PB propagator's slack tracking
///     already provides the "remaining pairs can't bring it back to
///     target" early-conflict watchdog.
///   - BDKR Canonical2..5 are NOT enforced here — they're best expressed
///     as MDD path pruning at `gen_mdd` build time (separate change).
///   - Native MDD constraint over all 4k boundary positions (Z, W, X, Y
///     interleaved per the MDD's level structure: 0..2k = ZW, 2k..4k = XY).
///
/// No spectral constraint in this prototype — the SAT is sound without
/// it but slower than it could be. Adding spectral requires multi-
/// sequence support in `radical::SpectralConstraint`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn solve_xyzw(
    problem: Problem,
    tuple: Option<SumTuple>,    // None = any valid tuple (clauses transfer across tuples)
    k: usize,
    mdd_nodes: &[[u32; 4]],
    mdd_root: u32,
    mdd_depth: usize,           // = 4*k
    pos_order: &[usize],        // length = 2*k, used twice (once for ZW, once for XY)
    sat_config: &radical::SolverConfig,
    partial_boundary: &[i32],   // cube assumptions; empty = no external pinning
    conflict_limit: u64,
) -> (Option<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>, XyStats) {
    let n = problem.n;
    let m = problem.m();
    let x_var = |i: usize| -> i32 { (i + 1) as i32 };
    let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };
    let z_var = |i: usize| -> i32 { (2 * n + i + 1) as i32 };
    let w_var = |i: usize| -> i32 { (3 * n + i + 1) as i32 };

    let mut solver: radical::Solver = {
        let mut s = radical::Solver::new();
        s.config = sat_config.clone();
        s
    };

    // BDKR Canonical1 (Best, Djoković, Kharaghani, Ramp 2013):
    //   A[0] = A[n-1] = B[0] = B[n-1] = C[0] = D[0] = +1
    // Note: C[n-1] and D[n-2] are deliberately NOT fixed.
    // Canonical2..5 (first asymmetric/symmetric/exceptional index
    // conditions on A, B, C, D) are cleanest to bake into the MDD at
    // gen_mdd time as path pruning — they only constrain boundary
    // positions — and are NOT enforced here.
    solver.add_clause([x_var(0)]);
    solver.add_clause([x_var(n - 1)]);
    solver.add_clause([y_var(0)]);
    solver.add_clause([y_var(n - 1)]);
    solver.add_clause([z_var(0)]);
    solver.add_clause([w_var(0)]);

    // BDKR Canonical6 (A vs B tie-break at positions 1 and n-2):
    //   n <= 2  OR  (A[1] ≠ B[1]  AND  A[1] = +1)
    //           OR  (A[1]  = B[1]  AND  A[n-2] = +1  AND  B[n-2] = -1)
    //
    // Five 2-literal clauses (see CANONICAL.md §rule (vi)).  This form
    // both forbids (A[1]=-1, B[1]=+1) AND derives A[n-2]=+1 ∧ B[n-2]=-1
    // in the A[1]=B[1] case via CNF distribution.  The previous 3-lit
    // encoding accidentally forced A[n-2]=+1 ∧ B[n-2]=-1 in the A[1]≠B[1]
    // case too — over-constraining and rejecting valid canonical orbits
    // such as known TT(6) with A[1]=+1, B[1]=-1, A[n-2]=-1.
    if n >= 4 {
        let a1  = x_var(1);
        let b1  = y_var(1);
        let aam = x_var(n - 2);
        let bbm = y_var(n - 2);
        solver.add_clause([a1, -b1]);       // forbid A[1]=-1 ∧ B[1]=+1
        solver.add_clause([a1, aam]);       // A[1]=-1 → A[n-2]=+1
        solver.add_clause([-b1, aam]);      // B[1]=+1 → A[n-2]=+1
        solver.add_clause([a1, -bbm]);      // A[1]=-1 → B[n-2]=-1
        solver.add_clause([-b1, -bbm]);     // B[1]=+1 → B[n-2]=-1
    }

    // BDKR Canonical2 (A is lex-min under reversal):
    //   ∀ i' ∈ [1, n-1]: (∀ j' < i': A[j']=A[n-1-j']) ∧ (A[i']≠A[n-1-i']) → A[i']=+1
    // Tseitin-encode eq_A[j'] = (A[j']=A[n-1-j']) as aux vars; each main
    // clause becomes one disjunction of length O(i').
    //
    // Aux var numbering: we start at 3n+m+1 (first free after X,Y,Z,W)
    // and allocate sequentially. eq_a[j'] only exists for j' ∈ [1, (n-1)/2]
    // (positions in [n/2, n-1] alias to eq_a[n-1-j']).
    //
    // Only generate clauses for i' ∈ [1, (n-1)/2]: for larger i', the
    // premise ∀j'<i' (A[j']=A[n-1-j']) together with j' = n-1-i' forces
    // A[i'] = A[n-1-i'], contradicting A[i']≠A[n-1-i']. So those clauses
    // are vacuously true given Canonical1.
    let mut next_aux: i32 = (3 * n + m + 1) as i32;
    let mut eq_a: Vec<Option<i32>> = vec![None; n];
    for j_prime in 1..n {
        let mirror = n - 1 - j_prime;
        if mirror <= j_prime { break; } // past center, or at center
        let a = x_var(j_prime);
        let b = x_var(mirror);
        let y = next_aux; next_aux += 1;
        // y ↔ (a=b): 4 clauses
        solver.add_clause([-y, -a,  b]);
        solver.add_clause([-y,  a, -b]);
        solver.add_clause([ y,  a,  b]);
        solver.add_clause([ y, -a, -b]);
        eq_a[j_prime] = Some(y);
        eq_a[mirror] = Some(y); // alias
    }
    for i_prime in 1..n {
        let mirror = n - 1 - i_prime;
        if mirror <= i_prime { break; }
        // clause: ¬eq_a[1] ∨ ... ∨ ¬eq_a[i'-1] ∨ eq_a[i'] ∨ A[i']
        let mut clause: Vec<i32> = Vec::with_capacity(i_prime + 1);
        for j_prime in 1..i_prime {
            if let Some(y) = eq_a[j_prime] { clause.push(-y); }
        }
        if let Some(y) = eq_a[i_prime] { clause.push(y); }
        clause.push(x_var(i_prime));
        solver.add_clause(clause);
    }

    // BDKR Canonical3 (B): same structure as Canonical2, over Y.
    let mut eq_b: Vec<Option<i32>> = vec![None; n];
    for j_prime in 1..n {
        let mirror = n - 1 - j_prime;
        if mirror <= j_prime { break; }
        let a = y_var(j_prime);
        let b = y_var(mirror);
        let y = next_aux; next_aux += 1;
        solver.add_clause([-y, -a,  b]);
        solver.add_clause([-y,  a, -b]);
        solver.add_clause([ y,  a,  b]);
        solver.add_clause([ y, -a, -b]);
        eq_b[j_prime] = Some(y);
        eq_b[mirror] = Some(y);
    }
    for i_prime in 1..n {
        let mirror = n - 1 - i_prime;
        if mirror <= i_prime { break; }
        let mut clause: Vec<i32> = Vec::with_capacity(i_prime + 1);
        for j_prime in 1..i_prime {
            if let Some(y) = eq_b[j_prime] { clause.push(-y); }
        }
        if let Some(y) = eq_b[i_prime] { clause.push(y); }
        clause.push(y_var(i_prime));
        solver.add_clause(clause);
    }

    // BDKR Canonical4 (C is lex-min under "alt-reversal", i.e. anti-symmetric
    // premise rather than symmetric):
    //   ∀ i' ∈ [1, n-1]: (∀ j' < i': C[j']≠C[n-1-j']) ∧ (C[i']=C[n-1-i']) → C[i']=+1
    // Same eq-aux as Canonical2, but the main clause flips eq polarity:
    //   eq_c[1] ∨ ... ∨ eq_c[i'-1] ∨ ¬eq_c[i'] ∨ C[i']
    let mut eq_c: Vec<Option<i32>> = vec![None; n];
    for j_prime in 1..n {
        let mirror = n - 1 - j_prime;
        if mirror <= j_prime { break; }
        let a = z_var(j_prime);
        let b = z_var(mirror);
        let y = next_aux; next_aux += 1;
        solver.add_clause([-y, -a,  b]);
        solver.add_clause([-y,  a, -b]);
        solver.add_clause([ y,  a,  b]);
        solver.add_clause([ y, -a, -b]);
        eq_c[j_prime] = Some(y);
        eq_c[mirror] = Some(y);
    }
    for i_prime in 1..n {
        let mirror = n - 1 - i_prime;
        if mirror <= i_prime { break; }
        let mut clause: Vec<i32> = Vec::with_capacity(i_prime + 1);
        for j_prime in 1..i_prime {
            if let Some(y) = eq_c[j_prime] { clause.push(y); }
        }
        if let Some(y) = eq_c[i_prime] { clause.push(-y); }
        clause.push(z_var(i_prime));
        solver.add_clause(clause);
    }

    // BDKR Canonical5 (D, triple-product condition):
    //   ∀ i' ∈ [1, m-1]:
    //     (∀ j' < i': D[j'] * D[m-1-j'] = D[m-1]) ∧
    //     (D[i'] * D[m-1-i'] ≠ D[m-1])
    //   → D[i'] = +1
    // where m = n-1 (the length of D).
    //
    // Define prod_D[j'] = aux var for (D[j'] * D[m-1-j'] * D[m-1] = +1), i.e.
    // XNOR3(D[j'], D[m-1-j'], D[m-1]). Main clause for i':
    //   ¬prod_D[1] ∨ ... ∨ ¬prod_D[i'-1] ∨ prod_D[i'] ∨ D[i']
    // prod_D[j'] aliases to prod_D[m-1-j'] by symmetry in j' ↔ m-1-j'.
    let mlen = m;  // length of D; n-1
    let d_last = w_var(mlen - 1);
    let mut prod_d: Vec<Option<i32>> = vec![None; mlen];
    for j_prime in 1..mlen {
        let mirror = mlen - 1 - j_prime;
        if mirror <= j_prime { break; }
        let a = w_var(j_prime);
        let b = w_var(mirror);
        let c = d_last;
        let y = next_aux; next_aux += 1;
        // y ↔ XNOR3(a,b,c):  y ↔ "even number of (a,b,c) are true" (0 or 2)
        //   y → XNOR3: forbid (y=T, 1-or-3 trues)
        //     (y=T,a=F,b=F,c=T): clause (¬y ∨ a ∨ b ∨ ¬c)
        //     (y=T,a=F,b=T,c=F): (¬y ∨ a ∨ ¬b ∨ c)
        //     (y=T,a=T,b=F,c=F): (¬y ∨ ¬a ∨ b ∨ c)
        //     (y=T,a=T,b=T,c=T): (¬y ∨ ¬a ∨ ¬b ∨ ¬c)
        solver.add_clause([-y,  a,  b, -c]);
        solver.add_clause([-y,  a, -b,  c]);
        solver.add_clause([-y, -a,  b,  c]);
        solver.add_clause([-y, -a, -b, -c]);
        //   ¬y → XOR3: forbid (y=F, 0-or-2 trues)
        //     (y=F,a=F,b=F,c=F): (y ∨ a ∨ b ∨ c)
        //     (y=F,a=F,b=T,c=T): (y ∨ a ∨ ¬b ∨ ¬c)
        //     (y=F,a=T,b=F,c=T): (y ∨ ¬a ∨ b ∨ ¬c)
        //     (y=F,a=T,b=T,c=F): (y ∨ ¬a ∨ ¬b ∨ c)
        solver.add_clause([ y,  a,  b,  c]);
        solver.add_clause([ y,  a, -b, -c]);
        solver.add_clause([ y, -a,  b, -c]);
        solver.add_clause([ y, -a, -b,  c]);
        prod_d[j_prime] = Some(y);
        prod_d[mirror] = Some(y);
    }
    // Rule (v) main clause at i':
    //   (∃ j<i', premise(j)) ∨ ¬premise(i') ∨ D[i']=+1
    // with premise(j) ≡ prod_d[j] = (D[j]·D[m-1-j]·D[m-1] = -1) via
    // XNOR3 aux.  Previous version had polarities flipped, silently
    // accepting non-canonical W's that rule (v) should reject.
    for i_prime in 1..mlen {
        let mirror = mlen - 1 - i_prime;
        if mirror <= i_prime { break; }
        let mut clause: Vec<i32> = Vec::with_capacity(i_prime + 1);
        for j_prime in 1..i_prime {
            if let Some(y) = prod_d[j_prime] { clause.push(y); }
        }
        if let Some(y) = prod_d[i_prime] { clause.push(-y); }
        clause.push(w_var(i_prime));
        solver.add_clause(clause);
    }
    // Silence unused-var warning when n < 4 (no aux vars allocated).
    let _ = next_aux;

    // Sum constraints.
    //
    // When `tuple = Some(t)`, pin each sequence sum to t.x / t.y / t.z / t.w
    // via PB equalities — the classic "one solve per tuple" behaviour.
    //
    // When `tuple = None`, omit the sum PBs entirely. The energy identity
    //   (sum X)^2 + (sum Y)^2 + 2(sum Z)^2 + 2(sum W)^2 = 6n - 2
    // follows from summing the per-lag Turyn quad PBs over s ∈ [1, n-1]
    // (proof: sum_{s>=1} N_X(s) = ((sum X)^2 - n)/2 by
    // (sum X)^2 = N_X(0) + 2*sum_{s>=1} N_X(s); substitute into the
    // Turyn identity summed over s), so the solver automatically restricts
    // to valid tuples. One solve then covers the entire phase-A tuple
    // space; learnt clauses transfer across tuples.
    if let Some(t) = tuple {
        let parity_ok = (t.x + n as i32) % 2 == 0
                     && (t.y + n as i32) % 2 == 0
                     && (t.z + n as i32) % 2 == 0
                     && (t.w + m as i32) % 2 == 0;
        if !parity_ok { return (None, XyStats::default()); }
        let x_pos = ((t.x + n as i32) / 2) as usize;
        let y_pos = ((t.y + n as i32) / 2) as usize;
        let z_pos = ((t.z + n as i32) / 2) as usize;
        let w_pos = ((t.w + m as i32) / 2) as usize;
        let ones_n: Vec<u32> = vec![1; n];
        let ones_m: Vec<u32> = vec![1; m];
        let x_lits: Vec<i32> = (0..n).map(x_var).collect();
        let y_lits: Vec<i32> = (0..n).map(y_var).collect();
        let z_lits: Vec<i32> = (0..n).map(z_var).collect();
        let w_lits: Vec<i32> = (0..m).map(w_var).collect();
        solver.add_pb_eq(&x_lits, &ones_n, x_pos as u32);
        solver.add_pb_eq(&y_lits, &ones_n, y_pos as u32);
        solver.add_pb_eq(&z_lits, &ones_n, z_pos as u32);
        solver.add_pb_eq(&w_lits, &ones_m, w_pos as u32);
    }

    // Quad PB: full Turyn identity per lag.
    for s in 1..n {
        let mut lits_a: Vec<i32> = Vec::new();
        let mut lits_b: Vec<i32> = Vec::new();
        let mut coeffs: Vec<u32> = Vec::new();
        // agree(X[i], X[i+s]) — coeff 1 (both-true + both-false form)
        for i in 0..(n - s) {
            lits_a.push(x_var(i));   lits_b.push(x_var(i + s));   coeffs.push(1);
            lits_a.push(-x_var(i));  lits_b.push(-x_var(i + s));  coeffs.push(1);
            lits_a.push(y_var(i));   lits_b.push(y_var(i + s));   coeffs.push(1);
            lits_a.push(-y_var(i));  lits_b.push(-y_var(i + s));  coeffs.push(1);
        }
        // agree(Z[i], Z[i+s]) — coeff 2 (Z contributes double in identity)
        for i in 0..(n - s) {
            lits_a.push(z_var(i));   lits_b.push(z_var(i + s));   coeffs.push(2);
            lits_a.push(-z_var(i));  lits_b.push(-z_var(i + s));  coeffs.push(2);
        }
        // agree(W[i], W[i+s]) — coeff 2, only when s < m
        if s < m {
            for i in 0..(m - s) {
                lits_a.push(w_var(i));   lits_b.push(w_var(i + s));   coeffs.push(2);
                lits_a.push(-w_var(i));  lits_b.push(-w_var(i + s));  coeffs.push(2);
            }
        }
        // Target derived from energy identity. For ±1 sequences:
        //   N_S(s) = 2*agree_S(s) - len_S(s)
        // Substituting into N_X + N_Y + 2*N_Z + 2*N_W = 0 and dividing by 2:
        //   agree_X(s) + agree_Y(s) + 2*agree_Z(s) + 2*agree_W(s) = 3n - 3s - 1
        // (assuming m = n-1 so the W contribution is 2*agree_W with len m-s).
        // For s >= m, the W term drops:
        //   agree_X(s) + agree_Y(s) + 2*agree_Z(s) = 2(n-s)
        // The encoded LHS is exactly that (1 unit per X/Y agree term, 2 per Z/W).
        let target = if s < m { (3 * n as i32 - 3 * s as i32 - 1) as u32 }
                     else { (2 * (n - s)) as u32 };
        solver.add_quad_pb_eq(&lits_a, &lits_b, &coeffs, target);
    }

    // MDD constraint over the full ZW+XY boundary.
    // Levels 0..2k branch on (Z, W); levels 2k..4k branch on (X, Y).
    // pos_order is reused for both halves.
    let mut level_a: Vec<i32> = Vec::with_capacity(mdd_depth);
    let mut level_b: Vec<i32> = Vec::with_capacity(mdd_depth);
    for l in 0..2 * k {
        let b = pos_order[l];
        let z_pos = if b < k { b } else { n - 2 * k + b };
        // For W (length m=n-1), the suffix bit k+i maps to position m-k+i = n-1-k+i.
        let w_pos = if b < k { b } else { (n - 1) - 2 * k + b };
        level_a.push(z_var(z_pos));
        level_b.push(w_var(w_pos));
    }
    for l in 0..2 * k {
        let b = pos_order[l];
        let xy_pos = if b < k { b } else { n - 2 * k + b };
        level_a.push(x_var(xy_pos));
        level_b.push(y_var(xy_pos));
    }
    solver.add_mdd_constraint(mdd_nodes, mdd_root, mdd_depth, &level_a, &level_b);

    let d0 = solver.num_decisions();
    let p0 = solver.num_propagations();
    let vars_pre_forced = solver.num_level0_vars() as u64;
    let free_vars = (solver.num_vars() as u64).saturating_sub(vars_pre_forced);

    if conflict_limit > 0 { solver.set_conflict_limit(conflict_limit); }
    // Pass the partial-boundary cube as assumptions. Empty slice → no cube.
    // This is the cube-and-conquer entrypoint: an outer procedure can
    // shard the boundary space and hand each cube to a worker running
    // `solve_xyzw` independently.
    let result = solver.solve_with_assumptions(partial_boundary);

    let decisions    = solver.num_decisions().saturating_sub(d0);
    let propagations = solver.num_propagations().saturating_sub(p0);
    let cover_micro  = xy_cover_micro(result, decisions, free_vars);
    let stats = XyStats { decisions, propagations, vars_pre_forced, free_vars, cover_micro };

    let xyzw = match result {
        Some(true) => {
            let x = extract_seq(&solver, |i| x_var(i), n);
            let y = extract_seq(&solver, |i| y_var(i), n);
            let z = extract_seq(&solver, |i| z_var(i), n);
            let w = extract_seq(&solver, |i| w_var(i), m);
            Some((x, y, z, w))
        }
        _ => None,
    };
    (xyzw, stats)
}



/// Thin wrapper around the unified runner with `wz_mode = Cross`. Kept
/// for tests and benchmarks that were written before the unification;
/// new code should call `run_mdd_sat_search` directly.
pub(crate) fn run_hybrid_search(cfg: &SearchConfig, verbose: bool) -> SearchReport {
    let problem = cfg.problem;
    let mut tuples = phase_a_tuples(problem, cfg.test_tuple.as_ref());
    // Heuristic tuple ordering depends on problem size.
    if problem.n >= 26 {
        tuples.sort_by_key(|t| ((t.x - t.y).abs(), t.z.abs() + t.w.abs(), t.x.abs() + t.y.abs()));
    } else {
        tuples.sort_by_key(|t| (t.z.abs() + t.w.abs(), (t.x - t.y).abs(), t.x.abs() + t.y.abs()));
    }

    let mut cfg = cfg.clone();
    cfg.wz_mode = Some(WzMode::Cross);
    cfg.wz_together = false;
    // Cross mode historically used k=7 for XY enumeration.
    if cfg.mdd_k == SearchConfig::default().mdd_k {
        cfg.mdd_k = 7;
    }
    let mdd_k = cfg.mdd_k.min((problem.n - 1) / 2).min(problem.m() / 2);
    run_mdd_sat_search(problem, &tuples, &cfg, verbose, mdd_k)
}

