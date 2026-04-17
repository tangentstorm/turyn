//! Legacy stochastic Phase-C search and its SAT encoder.

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
use crate::types::*;
use crate::xy_sat::*;
use crate::SPECTRAL_FREQS;


pub(crate) fn compute_corr(problem: Problem, x: &[i8], y: &[i8], z: &[i8], w: &[i8]) -> Vec<i32> {
    let n = problem.n;
    let m = problem.m();
    let mut corr = vec![0i32; n];
    for s in 1..n {
        let mut c = 0i32;
        for i in 0..(n - s) {
            c += (x[i] as i32) * (x[i + s] as i32)
                + (y[i] as i32) * (y[i + s] as i32)
                + 2 * (z[i] as i32) * (z[i + s] as i32);
        }
        if s < m {
            for i in 0..(m - s) {
                c += 2 * (w[i] as i32) * (w[i + s] as i32);
            }
        }
        corr[s] = c;
    }
    corr
}


pub(crate) fn defect_from_corr(corr: &[i32]) -> i64 {
    corr.iter().skip(1).map(|&c| (c as i64) * (c as i64)).sum()
}


pub(crate) fn stochastic_search(problem: Problem, test_tuple: Option<&SumTuple>, verbose: bool, time_limit_secs: u64) -> SearchReport {
    let run_start = Instant::now();
    let workers = std::thread::available_parallelism()
        .map(|n| n.get()).unwrap_or(1).max(1);
    if verbose {
        println!("TT({}): stochastic search with {} threads", problem.n, workers);
    }
    let time_limit = if time_limit_secs > 0 {
        Some(std::time::Duration::from_secs(time_limit_secs))
    } else {
        None
    };
    let found = Arc::new(AtomicBool::new(false));
    let norm = Arc::new(phase_a_tuples(problem, test_tuple));
    let deadline = time_limit.map(|d| Instant::now() + d);
    let mut handles = Vec::new();
    for tid in 0..workers {
        let found = Arc::clone(&found);
        let norm = Arc::clone(&norm);
        handles.push(std::thread::spawn(move || {
            stochastic_worker(problem, &norm, &found, tid as u64, verbose && tid == 0, deadline)
        }));
    }
    let mut best = SearchReport { stats: SearchStats::default(), elapsed: run_start.elapsed(), found_solution: false };
    for h in handles {
        if let Ok(r) = h.join() {
            best.stats.merge_from(&r.stats);
            if r.found_solution { best.found_solution = true; }
        }
    }
    best.elapsed = run_start.elapsed();
    best
}


pub(crate) fn stochastic_worker(problem: Problem, norm: &[SumTuple], found: &AtomicBool, seed: u64, verbose: bool, deadline: Option<Instant>) -> SearchReport {
    let run_start = Instant::now();
    let mut stats = SearchStats::default();
    let n = problem.n;
    let m = problem.m();
    let mut rng_state: u64 = 0xdeadbeef12345678u64
        ^ seed.wrapping_mul(0x9e3779b97f4a7c15)
        ^ (std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default().as_nanos() as u64);
    let mut rng = || -> u64 { rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; rng_state };
    let rand_seq = |len: usize, rng: &mut dyn FnMut() -> u64| -> Vec<i8> {
        (0..len).map(|_| if rng() & 1 == 0 { 1 } else { -1 }).collect()
    };
    let fix_sum = |seq: &mut [i8], target: i32, rng: &mut dyn FnMut() -> u64, start: usize| {
        let len = seq.len();
        loop {
            let current: i32 = seq.iter().map(|&v| v as i32).sum();
            if current == target { break; }
            let idx = start + ((rng() as usize) % (len - start));
            if current < target && seq[idx] == -1 { seq[idx] = 1; }
            else if current > target && seq[idx] == 1 { seq[idx] = -1; }
        }
    };
    let max_restarts = 10_000_000;
    let max_flips = n * n * 50;
    for restart in 0..max_restarts {
        if found.load(AtomicOrdering::Relaxed) { break; }
        if let Some(dl) = deadline { if Instant::now() >= dl { break; } }
        let tuple = &norm[(rng() as usize) % norm.len()];
        let mut x = rand_seq(n, &mut rng);
        let mut y = rand_seq(n, &mut rng);
        let mut z = rand_seq(n, &mut rng);
        let mut w = rand_seq(m, &mut rng);
        x[0] = 1; y[0] = 1; z[0] = 1; z[n-1] = 1; w[0] = 1;
        fix_sum(&mut x, tuple.x, &mut rng, 1);
        fix_sum(&mut y, tuple.y, &mut rng, 1);
        fix_sum(&mut z[..n-1], tuple.z - 1, &mut rng, 1);
        fix_sum(&mut w, tuple.w, &mut rng, 1);
        let mut corr = compute_corr(problem, &x, &y, &z, &w);
        let mut defect = defect_from_corr(&corr);
        stats.xy_nodes += 1;
        if defect == 0 {
            found.store(true, AtomicOrdering::Relaxed);
            if verbose { println!("Solution found!"); }
            let ok = verify_tt(problem, &PackedSeq::from_values(&x), &PackedSeq::from_values(&y),
                               &PackedSeq::from_values(&z), &PackedSeq::from_values(&w));
            return SearchReport { stats, elapsed: run_start.elapsed(), found_solution: ok };
        }
        let mut temp = (defect as f64).sqrt().max(50.0);
        let cooling = (0.1f64 / temp).powf(1.0 / max_flips as f64).max(0.99);
        let mut delta_corr = vec![0i32; n];
        // Pre-build value-grouped index lists for O(1) partner finding.
        // pos_idx[seq][0] = indices with value +1, pos_idx[seq][1] = indices with value -1
        // Only include mutable indices (skip index 0 for all, skip n-1 for z).
        let mut pos_idx: [Vec<Vec<usize>>; 4] = [vec![vec![], vec![]], vec![vec![], vec![]], vec![vec![], vec![]], vec![vec![], vec![]]];
        let seqs_ref: [&[i8]; 4] = [&x, &y, &z, &w];
        let seq_lens = [n, n, n, m];
        for si in 0..4 {
            let upper = if si == 2 { n - 1 } else { seq_lens[si] };
            for i in 1..upper {
                let vi = if seqs_ref[si][i] == 1 { 0 } else { 1 };
                pos_idx[si][vi].push(i);
            }
        }
        for flip in 0..max_flips {
            if flip % 1000 == 0 && found.load(AtomicOrdering::Relaxed) { break; }
            let seq_idx = (rng() as usize) % 4;
            let seq_len = if seq_idx < 3 { n } else { m };
            let weight: i32 = if seq_idx < 2 { 1 } else { 2 };
            let seq: &mut [i8] = match seq_idx { 0 => &mut x, 1 => &mut y, 2 => &mut z, _ => &mut w };
            let vi_group = if rng() & 1 == 0 { 0usize } else { 1 };
            let group = &pos_idx[seq_idx][vi_group];
            if group.len() < 2 { continue; }
            let pi = (rng() as usize) % group.len();
            let mut qi = (rng() as usize) % (group.len() - 1);
            if qi >= pi { qi += 1; }
            let p = group[pi];
            let q = group[qi];
            let v = seq[p];
            let vi = v as i32;
            let mut new_defect = 0i64;
            // Early termination: in cold phase, reject as soon as partial
            // new_defect exceeds defect (acceptance probability ~0).
            let early_threshold = if temp < 1.0 { defect } else { i64::MAX };
            let mut completed = true;
            for s in 1..n {
                // Swapping two same-value positions: delta = -2*v * (sum of non-overlapping neighbors)
                let mut nb = 0i32;
                if p + s < seq_len && p + s != q { nb += seq[p + s] as i32; }
                if p >= s && p - s != q { nb += seq[p - s] as i32; }
                if q + s < seq_len && q + s != p { nb += seq[q + s] as i32; }
                if q >= s && q - s != p { nb += seq[q - s] as i32; }
                delta_corr[s] = -2 * vi * nb * weight;
                let new_c = corr[s] as i64 + delta_corr[s] as i64;
                new_defect += new_c * new_c;
                if new_defect > early_threshold {
                    completed = false;
                    break;
                }
            }
            stats.xy_nodes += 1;
            if !completed { temp *= cooling; continue; }
            let delta = new_defect - defect;
            let accept = if delta <= 0 { true }
                else if temp > 0.1 { (rng() % 10000) as f64 / 10000.0 < (-delta as f64 / temp).exp() }
                else { false };
            if accept {
                seq[p] = -v; seq[q] = -v;
                // Update pos_idx: move p and q from current group to opposite
                let old_group = vi_group;
                let new_group = 1 - old_group;
                pos_idx[seq_idx][old_group].retain(|&i| i != p && i != q);
                pos_idx[seq_idx][new_group].push(p);
                pos_idx[seq_idx][new_group].push(q);
                for s in 1..n { corr[s] += delta_corr[s]; }
                defect = new_defect;
                if defect == 0 {
                    let _ = seq;
                    found.store(true, AtomicOrdering::Relaxed);
                    let px = PackedSeq::from_values(&x);
                    let py = PackedSeq::from_values(&y);
                    let pz = PackedSeq::from_values(&z);
                    let pw = PackedSeq::from_values(&w);
                    if verbose {
                        print_solution(&format!("TT({}) found (restart {} flip {})", problem.n, restart, flip), &px, &py, &pz, &pw);
                    }
                    let ok = verify_tt(problem, &px, &py, &pz, &pw);
                    return SearchReport { stats, elapsed: run_start.elapsed(), found_solution: ok };
                }
            }
            temp *= cooling;
        }
        if verbose && restart % 5000 == 0 && restart > 0 {
            println!("Restart {}: defect={}, elapsed={:.1?}", restart, defect, run_start.elapsed());
        }
    }
    SearchReport { stats, elapsed: run_start.elapsed(), found_solution: false }
}

// ── SAT-based search using CaDiCaL ──────────────────────────────────────────


/// Variable layout for SAT encoding:
///   X[0..n)   → vars 1..=n
///   Y[0..n)   → vars n+1..=2n
///   Z[0..n)   → vars 2n+1..=3n
///   W[0..m)   → vars 3n+1..=3n+m
/// Additional auxiliary variables start at 3n+m+1.
pub(crate) struct SatEncoder {
    pub(crate) n: usize,
    pub(crate) next_var: i32,
    /// XNOR triples: (aux, a, b) where aux = (a XNOR b)
    pub(crate) xnor_triples: Vec<(i32, i32, i32)>,
}


impl SatEncoder {
    pub(crate) fn new(n: usize) -> Self {
        let m = n - 1;
        Self { n, next_var: (3 * n + m + 1) as i32, xnor_triples: Vec::new() }
    }

    pub(crate) fn x_var(&self, i: usize) -> i32 { (i + 1) as i32 }
    pub(crate) fn y_var(&self, i: usize) -> i32 { (self.n + i + 1) as i32 }
    pub(crate) fn z_var(&self, i: usize) -> i32 { (2 * self.n + i + 1) as i32 }
    pub(crate) fn w_var(&self, i: usize) -> i32 { (3 * self.n + i + 1) as i32 }
    pub(crate) fn fresh(&mut self) -> i32 { let v = self.next_var; self.next_var += 1; v }

    /// Encode XNOR: aux ↔ (a ↔ b). Returns the auxiliary variable.
    /// aux=true means a and b have the same sign (+1,+1 or -1,-1).
    pub(crate) fn encode_xnor(&mut self, solver: &mut impl SatSolver, a: i32, b: i32) -> i32 {
        let aux = self.fresh();
        // aux → (a ↔ b):  aux → (a → b) ∧ (b → a)
        //   ¬aux ∨ ¬a ∨ b, ¬aux ∨ a ∨ ¬b
        // (a ↔ b) → aux:  (¬a ∨ ¬b ∨ aux) ∧ (a ∨ b ∨ aux)
        solver.add_clause([-aux, -a, b]);
        solver.add_clause([-aux, a, -b]);
        solver.add_clause([a, b, aux]);
        solver.add_clause([-a, -b, aux]);
        self.xnor_triples.push((aux, a, b));
        aux
    }

    /// Totalizer encoding (Bailleux & Boufkhad 2003): build a binary tree
    /// that counts how many of `lits` are true, using O(n log n) auxiliary
    /// variables instead of O(n²) for a sequential counter.
    ///
    /// Returns vec r where r[c] (for c in 1..=lits.len()) is a SAT variable
    /// that is true iff at least c of `lits` are true. r[0] is unused.
    pub(crate) fn build_counter(
        &mut self,
        solver: &mut impl SatSolver,
        lits: &[i32],
    ) -> Vec<i32> {
        let n = lits.len();
        if n == 0 {
            return vec![0];
        }
        if n == 1 {
            // Single literal: at-least-1 ↔ lit
            let v = self.fresh();
            solver.add_clause([-lits[0], v]);
            solver.add_clause([lits[0], -v]);
            return vec![0, v];
        }

        // Split into halves and recurse
        let mid = n / 2;
        let left = self.build_counter(solver, &lits[..mid]);
        let right = self.build_counter(solver, &lits[mid..]);
        let left_max = mid;    // left can count 0..=mid
        let right_max = n - mid; // right can count 0..=n-mid

        // Merge: create output variables for counts 1..=n
        let mut out = vec![0i32; n + 1];
        for c in 1..=n {
            out[c] = self.fresh();
        }

        // Merge clauses: out[c] ↔ ∃(a+b=c) left[a] ∧ right[b]
        // Encoded as:
        //   Forward: left[a] ∧ right[b] → out[a+b]  (for all valid a,b)
        //   Backward: out[c] → left[a] ∨ right[c-a]  (for all valid a given c)
        //
        // Using "at-least" semantics (monotone):
        //   left[a] ∧ right[b] → out[a+b]   (forward, ensures out counts enough)
        //   out[c] → left[a] ∨ right[c-a]    (backward, ensures out doesn't overcount)

        for a in 0..=left_max {
            for b in 0..=right_max {
                let c = a + b;
                if c == 0 || c > n { continue; }
                // Forward: left[a] ∧ right[b] → out[c]
                // i.e., ¬left[a] ∨ ¬right[b] ∨ out[c]
                let l = if a == 0 { 0 } else { left[a] };   // 0 means "always true"
                let r = if b == 0 { 0 } else { right[b] };
                match (l, r) {
                    (0, 0) => { solver.add_clause([out[c]]); } // both always true
                    (0, _) => { solver.add_clause([-r, out[c]]); }
                    (_, 0) => { solver.add_clause([-l, out[c]]); }
                    (_, _) => { solver.add_clause([-l, -r, out[c]]); }
                }
            }
        }

        // Backward: out[c] → ∨_{a=max(0,c-right_max)..min(c,left_max)} (left[a] ∨ right[c-a])
        // Simplified: out[c] → left[a] ∨ right[c-a] for each valid split a
        // Actually the standard totalizer backward clause is:
        //   ¬left[a+1] ∧ ¬right[b+1] → ¬out[a+b+1]
        // i.e., out[a+b+1] → left[a+1] ∨ right[b+1]
        for a in 0..=left_max {
            for b in 0..=right_max {
                let c = a + b + 1;
                if c > n { continue; }
                let l_next = if a + 1 <= left_max { left[a + 1] } else { 0 };
                let r_next = if b + 1 <= right_max { right[b + 1] } else { 0 };
                // out[c] → l_next ∨ r_next
                match (l_next, r_next) {
                    (0, 0) => { solver.add_clause([-out[c]]); } // impossible count
                    (0, _) => { solver.add_clause([-out[c], r_next]); }
                    (_, 0) => { solver.add_clause([-out[c], l_next]); }
                    (_, _) => { solver.add_clause([-out[c], l_next, r_next]); }
                }
            }
        }

        out
    }

    /// Encode exactly `target` of `lits` must be true, using the totalizer.
    #[allow(dead_code)] // totalizer-based alternative to PbEq; kept for fallback
    pub(crate) fn encode_cardinality_eq(
        &mut self,
        solver: &mut impl SatSolver,
        lits: &[i32],
        target: usize,
    ) {
        let n = lits.len();
        if n == 0 {
            assert!(target == 0);
            return;
        }
        if target > n {
            solver.add_clause([]); // impossible
            return;
        }
        let ctr = self.build_counter(solver, lits);
        // Enforce at-least target
        if target >= 1 {
            assert!(ctr[target] != 0);
            solver.add_clause([ctr[target]]);
        }
        // Enforce at-most target (i.e., NOT at-least target+1)
        if target + 1 <= n {
            assert!(ctr[target + 1] != 0);
            solver.add_clause([-ctr[target + 1]]);
        }
    }

    /// Encode `xy_count + 2 * zw_count = target` using selectors over two
    /// totalizer counters. Returns false if no valid split exists (infeasible).
    pub(crate) fn encode_weighted_agree_eq(
        &mut self,
        solver: &mut impl SatSolver,
        xy_lits: &[i32],
        zw_lits: &[i32],
        target: usize,
    ) -> bool {
        let xy_ctr = self.build_counter(solver, xy_lits);
        let zw_ctr = self.build_counter(solver, zw_lits);

        let mut selectors = Vec::new();
        for c_zw in 0..=zw_lits.len() {
            let rem = target as isize - 2 * c_zw as isize;
            if rem < 0 || rem as usize > xy_lits.len() { continue; }
            let c_xy = rem as usize;

            let sel = self.fresh();

            if c_xy > 0 {
                if c_xy < xy_ctr.len() && xy_ctr[c_xy] != 0 {
                    solver.add_clause([-sel, xy_ctr[c_xy]]);
                } else {
                    solver.add_clause([-sel]);
                    continue;
                }
            }
            if c_xy + 1 < xy_ctr.len() && xy_ctr[c_xy + 1] != 0 {
                solver.add_clause([-sel, -xy_ctr[c_xy + 1]]);
            }

            if c_zw > 0 {
                if c_zw < zw_ctr.len() && zw_ctr[c_zw] != 0 {
                    solver.add_clause([-sel, zw_ctr[c_zw]]);
                } else {
                    solver.add_clause([-sel]);
                    continue;
                }
            }
            if c_zw + 1 < zw_ctr.len() && zw_ctr[c_zw + 1] != 0 {
                solver.add_clause([-sel, -zw_ctr[c_zw + 1]]);
            }

            selectors.push(sel);
        }

        if selectors.is_empty() {
            solver.add_clause([]);
            false
        } else {
            solver.add_clause(selectors.iter().copied());
            true
        }
    }
}


/// Build the full SAT encoding for a given problem and sum-tuple.
/// Returns (encoder, solver) pair before solving.
pub(crate) fn sat_encode(problem: Problem, tuple: SumTuple) -> (SatEncoder, radical::Solver) {
    let n = problem.n;
    let m = problem.m();
    let mut enc = SatEncoder::new(n);
    let mut solver: radical::Solver = Default::default();

    // Symmetry breaking (BDKR 2012, rule i).  The Turyn symmetry group has
    // four generators:
    //   T1: negate any one of X, Y, Z, W
    //   T2: reverse any one of X, Y, Z, W
    //   T3: alternate all four sequences (a[i] ↦ (-1)^i·a[i] simultaneously)
    //   T4: interchange X ↔ Y
    // Under T1+T2 combined (reverse-then-negate), every orbit has a
    // representative with *both* endpoints of X and of Y equal to +1.  For
    // Z and W, only the first element is pinned here — the full BDKR
    // canonical form for Z/W is controlled by rules (iv)/(v) which break
    // the residual reverse/alternate symmetry and are TODO (see
    // docs/CANONICAL.md).
    solver.add_clause([enc.x_var(0)]);        // x[0]   = +1  (rule i)
    solver.add_clause([enc.y_var(0)]);        // y[0]   = +1  (rule i)
    solver.add_clause([enc.x_var(n - 1)]);    // x[n-1] = +1  (rule i)
    solver.add_clause([enc.y_var(n - 1)]);    // y[n-1] = +1  (rule i)
    solver.add_clause([enc.z_var(0)]);        // z[0]   = +1  (rule i)
    solver.add_clause([enc.w_var(0)]);        // w[0]   = +1  (rule i)

    // BDKR rules (ii)/(iii)/(iv)/(v)/(vi): fold the remaining
    // canonicalisation rules into the SAT encoding.  Aux vars are
    // allocated contiguously above the sequence vars (4n-1 of them)
    // via `enc.fresh()`, so they don't collide with xnor aux.
    let xv = |i: usize| enc.x_var(i);
    let yv = |i: usize| enc.y_var(i);
    let zv = |i: usize| enc.z_var(i);
    let wv = |i: usize| enc.w_var(i);
    let mut next_var = enc.next_var;
    add_palindromic_break(&mut solver, n, xv, /*equality=*/false, 1, &mut next_var);
    add_palindromic_break(&mut solver, n, yv, /*equality=*/false, 1, &mut next_var);
    add_palindromic_break(&mut solver, n, zv, /*equality=*/true,  0, &mut next_var);
    add_alternation_break(&mut solver, m, wv, &mut next_var);
    add_swap_break(&mut solver, xv, yv, n);
    enc.next_var = next_var;

    // Sum constraints via PbSetEq.  Tuples are unsigned (|σ|), so each
    // sequence's sum may land on either +|σ| or −|σ|; rules (ii)..(vi)
    // above resolve which sign is consistent with the canonical form.
    let x_lits: Vec<i32> = (0..n).map(|i| enc.x_var(i)).collect();
    let y_lits: Vec<i32> = (0..n).map(|i| enc.y_var(i)).collect();
    let z_lits: Vec<i32> = (0..n).map(|i| enc.z_var(i)).collect();
    let w_lits: Vec<i32> = (0..m).map(|i| enc.w_var(i)).collect();
    let sum_values = |abs_s: i32, len: usize| -> Vec<u32> {
        if abs_s == 0 {
            sigma_full_to_cnt(0, 0, len).into_iter().collect()
        } else {
            [abs_s, -abs_s].iter().filter_map(|&s| sigma_full_to_cnt(s, 0, len)).collect()
        }
    };
    solver.add_pb_set_eq(&x_lits, &sum_values(tuple.x.abs(), n));
    solver.add_pb_set_eq(&y_lits, &sum_values(tuple.y.abs(), n));
    solver.add_pb_set_eq(&z_lits, &sum_values(tuple.z.abs(), n));
    solver.add_pb_set_eq(&w_lits, &sum_values(tuple.w.abs(), m));

    for k in 1..n {
        let w_overlap = if k < m { m - k } else { 0 };
        let target = 2 * (n - k) + w_overlap;

        let mut xy_lits = Vec::new();
        for i in 0..(n - k) {
            xy_lits.push(enc.encode_xnor(&mut solver, enc.x_var(i), enc.x_var(i + k)));
        }
        for i in 0..(n - k) {
            xy_lits.push(enc.encode_xnor(&mut solver, enc.y_var(i), enc.y_var(i + k)));
        }

        let mut zw_lits = Vec::new();
        for i in 0..(n - k) {
            zw_lits.push(enc.encode_xnor(&mut solver, enc.z_var(i), enc.z_var(i + k)));
        }
        for i in 0..w_overlap {
            zw_lits.push(enc.encode_xnor(&mut solver, enc.w_var(i), enc.w_var(i + k)));
        }

        enc.encode_weighted_agree_eq(&mut solver, &xy_lits, &zw_lits, target);
    }

    (enc, solver)
}


/// Unified quad PB encoding for any combination of fixed/free sequences.
/// Fixed sequences have their agree contributions folded into the constraint targets.
/// Free sequences get PB sum constraints and quad PB autocorrelation terms.
/// Returns None if structurally infeasible (parity mismatch, target out of range).
#[allow(dead_code)]
pub(crate) fn sat_encode_quad_pb_unified(
    problem: Problem,
    tuple: SumTuple,
    x_fixed: Option<&[i8]>,
    y_fixed: Option<&[i8]>,
    z_fixed: Option<&[i8]>,
    w_fixed: Option<&[i8]>,
) -> Option<(SatEncoder, radical::Solver)> {
    let n = problem.n;
    let m = problem.m();
    let enc = SatEncoder::new(n);
    let mut solver = radical::Solver::new();

    // Symmetry breaking for free sequences (BDKR 2012, rule i).  See
    // `sat_encode` for the full T1..T4 group derivation.  For X and Y we
    // can pin *both* endpoints because T1+T2 (reverse-then-negate) lets us
    // fix them independently; for Z and W only the first element is pinned
    // here (rules iv/v are TODO).
    if x_fixed.is_none() {
        solver.add_clause([enc.x_var(0)]);
        solver.add_clause([enc.x_var(n - 1)]);
    }
    if y_fixed.is_none() {
        solver.add_clause([enc.y_var(0)]);
        solver.add_clause([enc.y_var(n - 1)]);
    }
    if z_fixed.is_none() { solver.add_clause([enc.z_var(0)]); }
    if w_fixed.is_none() { solver.add_clause([enc.w_var(0)]); }

    // Helper: check sum parity
    let check_sum = |sum: i32, len: usize| -> Option<u32> {
        if (sum + len as i32) % 2 != 0 { return None; }
        let pos = (sum + len as i32) / 2;
        if pos < 0 || pos as usize > len { return None; }
        Some(pos as u32)
    };

    // For each sequence: if free, add PB sum constraint; if fixed, verify sum
    struct SeqInfo<'a> { fixed: Option<&'a [i8]>, sum: i32, len: usize }
    let seqs = [
        SeqInfo { fixed: x_fixed, sum: tuple.x, len: n },
        SeqInfo { fixed: y_fixed, sum: tuple.y, len: n },
        SeqInfo { fixed: z_fixed, sum: tuple.z, len: n },
        SeqInfo { fixed: w_fixed, sum: tuple.w, len: m },
    ];
    let seq_var = |si: usize, i: usize| -> i32 {
        match si { 0 => enc.x_var(i), 1 => enc.y_var(i), 2 => enc.z_var(i), _ => enc.w_var(i) }
    };

    for (si, seq) in seqs.iter().enumerate() {
        match seq.fixed {
            None => {
                let pos = check_sum(seq.sum, seq.len)?;
                let lits: Vec<i32> = (0..seq.len).map(|i| seq_var(si, i)).collect();
                let ones: Vec<u32> = vec![1; seq.len];
                solver.add_pb_eq(&lits, &ones, pos);
            }
            Some(vals) => {
                let actual_sum: i32 = vals.iter().map(|&v| v as i32).sum();
                if actual_sum != seq.sum { return None; }
                // Fix variables
                for i in 0..seq.len {
                    solver.add_clause([if vals[i] > 0 { seq_var(si,i) } else { -seq_var(si,i) }]);
                }
            }
        }
    }

    // Autocorrelation constraints: agree_x + agree_y + 2*agree_z + 2*agree_w = 2*(n-k) + (m-k)
    // Fixed sequences contribute constant agree counts, subtracted from the target.
    let coeff_weight = [1u32, 1, 2, 2]; // X, Y have weight 1; Z, W have weight 2
    let seq_lens = [n, n, n, m];

    for k in 1..n {
        let w_overlap = if k < m { m - k } else { 0 };
        let full_target = (2 * (n - k) + w_overlap) as i32;
        let mut target_i = full_target;

        // Subtract fixed-sequence agree contributions
        for (si, seq) in seqs.iter().enumerate() {
            if let Some(vals) = seq.fixed {
                let len = seq_lens[si];
                let overlap = if k < len { len - k } else { 0 };
                let agree: i32 = (0..overlap).filter(|&i| vals[i] == vals[i + k]).count() as i32;
                target_i -= coeff_weight[si] as i32 * agree;
            }
        }

        if target_i < 0 { return None; }

        // Build quad PB terms for free sequences
        let mut lits_a = Vec::new();
        let mut lits_b = Vec::new();
        let mut coeffs = Vec::new();

        for (si, seq) in seqs.iter().enumerate() {
            if seq.fixed.is_some() { continue; }
            let len = seq_lens[si];
            let overlap = if k < len { len - k } else { 0 };
            let w = coeff_weight[si];
            for i in 0..overlap {
                lits_a.push(seq_var(si,i)); lits_b.push(seq_var(si,i + k)); coeffs.push(w);
                lits_a.push(-seq_var(si,i)); lits_b.push(-seq_var(si,i + k)); coeffs.push(w);
            }
        }

        if lits_a.is_empty() {
            if target_i != 0 { return None; } // all fixed, must equal 0
        } else {
            let max_val: i32 = coeffs.iter().sum::<u32>() as i32;
            if target_i > max_val { return None; }
            solver.add_quad_pb_eq(&lits_a, &lits_b, &coeffs, target_i as u32);
        }
    }

    Some((enc, solver))
}


