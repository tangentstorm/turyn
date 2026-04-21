//! XY SAT stack: GJ elimination, lag-pair template, break clauses, and per-candidate solver.

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
use crate::types::*;
use crate::SPECTRAL_FREQS;


/// Pre-built SAT template for X/Y solving. Contains the structural clauses
/// (XNOR, totalizer trees, sum constraints) that are shared across all Z/W pairs
/// for a given tuple. Clone and add per-pair cardinality assertions to solve.
#[cfg(not(feature = "cadical"))]
pub(crate) struct SatXYTemplate {
    pub(crate) solver: radical::Solver,
    pub(crate) lag_pairs: Vec<LagPairs>,
    pub(crate) n: usize,
}


#[cfg(feature = "cadical")]
pub(crate) struct SatXYTemplate {
    pub(crate) solver: cadical::Solver,
    pub(crate) lag_pairs: Vec<LagPairs>,
    pub(crate) n: usize,
}


/// Per-candidate GJ elimination: given specific agree targets for each lag,
/// determine which primary variable pairs must be equal/opposite, and
/// propagate these equalities to reduce the problem.
///
/// Returns: vec of (var_a, var_b, equal: bool) pairs — if equal is true,
/// var_a = var_b; otherwise var_a = ¬var_b. Variables are 1-based.
/// GF(2) row: a bitset of variable indices + a constant (0 or 1).
/// Represents the equation: XOR of variables in the set = constant.
#[derive(Clone)]
pub(crate) struct Gf2Row {
    pub(crate) vars: Vec<bool>, // vars[i] = true if variable i participates
    pub(crate) constant: bool,  // right-hand side
}


impl Gf2Row {
    pub(crate) fn new(num_vars: usize) -> Self {
        Self { vars: vec![false; num_vars], constant: false }
    }
    pub(crate) fn xor_with(&mut self, other: &Gf2Row) {
        for i in 0..self.vars.len() {
            self.vars[i] ^= other.vars[i];
        }
        self.constant ^= other.constant;
    }
    /// Find the first set variable (pivot column), or None if all zero.
    pub(crate) fn pivot(&self) -> Option<usize> {
        self.vars.iter().position(|&v| v)
    }
    /// Count set variables.
    pub(crate) fn popcount(&self) -> usize {
        self.vars.iter().filter(|&&v| v).count()
    }
}


/// Compute the XY agree target for a given lag `s`:
/// target_raw = 2*(n-s) - zw_autocorr[s], target = target_raw/2.
/// Returns None if the target is infeasible (negative or wrong parity).
pub(crate) fn xy_agree_target(n: usize, s: usize, zw_autocorr: &[i32]) -> Option<usize> {
    let target_raw = 2 * (n - s) as i32 - zw_autocorr[s];
    if target_raw < 0 || target_raw % 2 != 0 { return None; }
    Some((target_raw / 2) as usize)
}


/// Returns None if a contradiction is detected (UNSAT), otherwise equalities.
pub(crate) fn gj_candidate_equalities(n: usize, candidate: &CandidateZW) -> Option<Vec<(i32, i32, bool)>> {
    let num_vars = 2 * n;
    // Union-find with negation tracking (XOR-union-find)
    let mut parent: Vec<usize> = (0..num_vars).collect();
    let mut rank: Vec<u8> = vec![0; num_vars];
    let mut neg: Vec<bool> = vec![false; num_vars]; // true if node is negated relative to parent

    fn find(parent: &mut [usize], neg: &mut [bool], mut x: usize) -> (usize, bool) {
        let mut path = Vec::new();
        let mut n = false;
        while parent[x] != x {
            path.push(x);
            n ^= neg[x];
            x = parent[x];
        }
        let root = x;
        let mut n2 = false;
        for &p in path.iter().rev() {
            n2 ^= neg[p];
            parent[p] = root;
            neg[p] = n2;
        }
        (root, n)
    }

    // Returns false if a contradiction is detected
    fn union(parent: &mut [usize], rank: &mut [u8], neg: &mut [bool],
             a: usize, b: usize, a_neg_b: bool) -> bool {
        let (ra, na) = find(parent, neg, a);
        let (rb, nb) = find(parent, neg, b);
        if ra == rb {
            // Check consistency: na ^ nb should equal a_neg_b
            return (na ^ nb) == a_neg_b;
        }
        let rel = na ^ nb ^ a_neg_b;
        if rank[ra] < rank[rb] {
            parent[ra] = rb;
            neg[ra] = rel;
        } else if rank[ra] > rank[rb] {
            parent[rb] = ra;
            neg[rb] = rel;
        } else {
            parent[rb] = ra;
            neg[rb] = rel;
            rank[ra] += 1;
        }
        true
    }

    // Process lags where ALL or NO pairs agree.
    // Also process lags where X and Y halves have separate extreme targets.
    for s in 1..n {
        let Some(target) = xy_agree_target(n, s, &candidate.zw_autocorr) else { continue; };
        let x_pairs = n - s;
        let y_pairs = n - s;
        let max_pairs = x_pairs + y_pairs;

        if target == max_pairs {
            // ALL pairs agree
            for i in 0..x_pairs {
                if !union(&mut parent, &mut rank, &mut neg, i, i + s, false) { return None; }
            }
            for i in 0..y_pairs {
                if !union(&mut parent, &mut rank, &mut neg, n + i, n + i + s, false) { return None; }
            }
        } else if target == 0 {
            // NO pairs agree
            for i in 0..x_pairs {
                if !union(&mut parent, &mut rank, &mut neg, i, i + s, true) { return None; }
            }
            for i in 0..y_pairs {
                if !union(&mut parent, &mut rank, &mut neg, n + i, n + i + s, true) { return None; }
            }
        }
    }

    // GF(2) Gauss-Jordan elimination on parity constraints from ALL lags.
    // For each lag s with target T:
    //   parity(agree_count) = T mod 2
    //   agree(x_i, x_{i+s}) = x_i XNOR x_{i+s} = 1 ⊕ x_i ⊕ x_{i+s}
    //   sum of agrees mod 2 = T mod 2
    //   k + sum(x_i ⊕ x_{i+s}) mod 2 = T mod 2   (where k = # pairs)
    //   sum(x_i ⊕ x_{i+s}) mod 2 = (T + k) mod 2
    //
    // sum(x_i ⊕ x_{i+s}) = sum(x_i) + sum(x_{i+s}) mod 2 (for distinct i)
    // Each variable x_v appears in the XOR sum once per occurrence in a pair.
    // Variable x_v appears as first element of pair (v, v+s) if v < n-s,
    // and as second element of pair (v-s, v) if v >= s.
    // So the total parity of a variable in the XOR sum depends on
    // how many times it appears in pairs, which determines its coefficient mod 2.
    {
        let mut rows: Vec<Gf2Row> = Vec::new();
        for s in 1..n {
            let Some(target) = xy_agree_target(n, s, &candidate.zw_autocorr) else { continue; };
            let k = 2 * (n - s); // total pairs (X + Y)

            // Build GF(2) equation: for each pair (i, i+s), x_i and x_{i+s} each
            // appear once. XOR of all these = (T + k) mod 2.
            let mut row = Gf2Row::new(num_vars);
            // X pairs
            for i in 0..(n - s) {
                row.vars[i] ^= true;       // x_i
                row.vars[i + s] ^= true;   // x_{i+s}
            }
            // Y pairs
            for i in 0..(n - s) {
                row.vars[n + i] ^= true;       // y_i
                row.vars[n + i + s] ^= true;   // y_{i+s}
            }
            row.constant = ((target + k) % 2) == 1;
            // Skip trivial rows (all zeros)
            if row.popcount() > 0 {
                rows.push(row);
            }
        }

        // Gauss-Jordan elimination
        let mut pivot_row: Vec<Option<usize>> = vec![None; num_vars];
        for r in 0..rows.len() {
            // Reduce row r against existing pivots
            loop {
                let Some(col) = rows[r].pivot() else { break };
                if let Some(pr) = pivot_row[col] {
                    let pr_row = rows[pr].clone();
                    rows[r].xor_with(&pr_row);
                } else {
                    // This column has no pivot yet — use row r as pivot
                    pivot_row[col] = Some(r);
                    // Reduce all other rows
                    let pivot = rows[r].clone();
                    for r2 in 0..rows.len() {
                        if r2 != r && rows[r2].vars[col] {
                            rows[r2].xor_with(&pivot);
                        }
                    }
                    break;
                }
            }
        }

        // Extract equalities from reduced rows:
        // A row with exactly 1 variable: that variable = constant
        // A row with exactly 2 variables: they are equal (or negated)
        for row in &rows {
            let set_vars: Vec<usize> = row.vars.iter().enumerate()
                .filter(|&(_, &v)| v).map(|(i, _)| i).collect();
            match set_vars.len() {
                0 => {
                    // All-zero row: if constant is 1, contradiction (UNSAT)
                    if row.constant { return None; }
                }
                1 => {
                    // Forced variable: x_v = constant (in GF(2)).
                    // constant=true → x_v has bit 1 → same as x[0] (forced +1) → equal
                    // constant=false → x_v has bit 0 → opposite of x[0] → negated
                    let v = set_vars[0];
                    if !union(&mut parent, &mut rank, &mut neg, v, 0, !row.constant) {
                        return None;
                    }
                }
                2 => {
                    let a = set_vars[0];
                    let b = set_vars[1];
                    if !union(&mut parent, &mut rank, &mut neg, a, b, row.constant) {
                        return None;
                    }
                }
                _ => {}
            }
        }
    }

    // Extract non-trivial equalities
    let mut equalities = Vec::new();
    for v in 0..num_vars {
        let (root, is_neg) = find(&mut parent, &mut neg, v);
        if root != v {
            let a = (v as i32) + 1;
            let b = (root as i32) + 1;
            equalities.push((a, b, !is_neg));
        }
    }

    Some(equalities)
}


/// Pair data for quadratic PB constraints per lag: (lits_a, lits_b) for each lag.
/// agree(x_i, x_{i+s}) = x_i*x_{i+s} + ¬x_i*¬x_{i+s}, so each lag has
/// 4*(n-s) product terms (both-true + both-false for X pairs and Y pairs).
pub(crate) struct LagPairs {
    pub(crate) lits_a: Vec<i32>,
    pub(crate) lits_b: Vec<i32>,
}


/// Encode `aux ↔ (a == b)` (XNOR / agree indicator). Only referenced
/// from the regression test that pins down all four input combinations;
/// the production code path inlines the same four clauses where it
/// builds quadratic-PB lag constraints.
#[cfg(test)]
pub(crate) fn encode_xnor_agree(solver: &mut impl SatSolver, aux: i32, a: i32, b: i32) {
    solver.add_clause([-aux, -a,  b]);
    solver.add_clause([-aux,  a, -b]);
    solver.add_clause([ aux,  a,  b]);
    solver.add_clause([ aux, -a, -b]);
}


pub(crate) fn encode_xor_def(solver: &mut impl SatSolver, d: i32, a: i32, b: i32) {
    solver.add_clause([-d,  a,  b]);
    solver.add_clause([-d, -a, -b]);
    solver.add_clause([ d,  a, -b]);
    solver.add_clause([ d, -a,  b]);
}


/// Allocate fresh aux vars and emit BDKR "first-violation" palindromic-
/// break clauses (rules ii, iii, iv).
///
/// For each valid pair index `j` in `start_j ..= (seq_len - 2) / 2`,
/// introduce `diff_j` aux iff `seq[j] XOR seq[seq_len-1-j]` and add
///
///   clause@i = (∨_{j<i} lit_earlier(diff_j)) ∨ lit_current(diff_i) ∨ seq(i)
///
/// where the `lit_*` helpers select the polarity encoding the rule
/// ("first differ" for equality=false, "first equal" for equality=true).
/// Returns the number of aux vars consumed (so callers can keep
/// `next_var` in sync).
pub(crate) fn add_palindromic_break<F, S>(
    solver: &mut S,
    seq_len: usize,
    seq_var: F,
    equality: bool,
    start_j: usize,
    next_var: &mut i32,
) where F: Fn(usize) -> i32, S: SatSolver {
    if seq_len < 2 { return; }
    let last_j = (seq_len - 2) / 2;
    if start_j > last_j { return; }
    let n_aux = last_j - start_j + 1;
    let base = *next_var;
    *next_var += n_aux as i32;
    let diff = |k: usize| base + (k - start_j) as i32; // diff var for pair index k
    // XOR definitions: diff_k ↔ seq[k] XOR seq[seq_len-1-k].
    for k in start_j..=last_j {
        encode_xor_def(solver, diff(k), seq_var(k), seq_var(seq_len - 1 - k));
    }
    // First-violation clauses.  For equality=false (rule ii/iii) the
    // "violation" literal is diff_k (pair differs); for equality=true
    // (rule iv) it is ¬diff_k (pair is palindromic).
    for i in start_j..=last_j {
        let mut clause: Vec<i32> = Vec::with_capacity(i - start_j + 2);
        for j in start_j..i {
            if equality { clause.push(-diff(j)); } else { clause.push(diff(j)); }
        }
        if equality { clause.push(diff(i)); } else { clause.push(-diff(i)); }
        clause.push(seq_var(i));
        solver.add_clause(clause);
    }
}


/// BDKR rule (v) — alternation-break for W.  Defines `v_k` aux vars via
///    v_k ↔ d[k] XOR d[m-1-k] XOR d[m-1]
/// where `m = seq_len`.  Truth-table shows this `v_k` is `alt_k` — the
/// boolean "the product d[k]·d[m-1-k] equals d[m-1]", i.e. "no
/// violation at k".  The rule wants the *least* k with alt_k = F
/// (violation), so the first-violation chain uses the same polarity
/// as rule (iv): negate earlier and keep current positive.
pub(crate) fn add_alternation_break<F, S>(
    solver: &mut S,
    seq_len: usize,
    seq_var: F,
    next_var: &mut i32,
) where F: Fn(usize) -> i32, S: SatSolver {
    if seq_len < 3 { return; }
    let last_k = (seq_len - 2) / 2;
    let tail = seq_var(seq_len - 1);
    // Allocate v_k aux vars and an inner aux u_k for the two-step XOR.
    let base_v = *next_var;
    *next_var += (last_k + 1) as i32;
    let base_u = *next_var;
    *next_var += (last_k + 1) as i32;
    let v = |k: usize| base_v + k as i32;
    let u = |k: usize| base_u + k as i32;
    for k in 0..=last_k {
        // u_k ↔ d[k] XOR d[m-1-k]
        encode_xor_def(solver, u(k), seq_var(k), seq_var(seq_len - 1 - k));
        // v_k ↔ u_k XOR d[m-1]   (so v_k = alt_k = "no violation at k")
        encode_xor_def(solver, v(k), u(k), tail);
    }
    // First-violation chain (same polarity as rule iv).  Premise at i:
    //   (all j<i have v_j = T, i.e., no earlier violation) AND (v_i = F, violation here)
    // ⇒ d[i] = +1.  CNF clause: (∨_{j<i} ¬v_j) ∨ v_i ∨ d[i].
    for i in 0..=last_k {
        let mut clause: Vec<i32> = Vec::with_capacity(i + 2);
        for j in 0..i { clause.push(-v(j)); }
        clause.push(v(i));
        clause.push(seq_var(i));
        solver.add_clause(clause);
    }
}


/// BDKR rule (vi) — conditional X↔Y swap break (requires n > 2).
///
///   if a[2] != b[2] ⇒ a[2] = +1
///   else           ⇒ a[n-1] = +1 AND b[n-1] = -1
///
/// In 0-indexed vars: `a[2]→x_var(1)`, `a[n-1]→x_var(n-2)` (and same
/// for b).  Encoded as five binary/ternary clauses; see
/// docs/CANONICAL.md.
pub(crate) fn add_swap_break<F, G, S>(
    solver: &mut S,
    x_var: F,
    y_var: G,
    n: usize,
) where F: Fn(usize) -> i32, G: Fn(usize) -> i32, S: SatSolver {
    if n <= 2 { return; }
    let x1 = x_var(1);
    let y1 = y_var(1);
    let x_last = x_var(n - 2);
    let y_last = y_var(n - 2);
    solver.add_clause([x1, -y1]);              // forbid (x[1]=-1 ∧ y[1]=+1)
    solver.add_clause([x1,  x_last]);          // NOT case 2  ⇒  x[n-2] = +1  (i)
    solver.add_clause([-y1, x_last]);          //                             (ii)
    solver.add_clause([x1, -y_last]);          // NOT case 2  ⇒  y[n-2] = -1  (i)
    solver.add_clause([-y1, -y_last]);         //                             (ii)
}


/// XY product-law conjecture (`--conj-xy-product`): enforce
/// `U_i = -U_{n+1-i}` for every 2 <= i <= n-1, where
/// `U_i := x_i * y_i ∈ {±1}` (1-indexed).  Empirically holds on the
/// known Turyn corpus; unproven. See `conjectures/xy-product.md`.
///
/// The BDKR rule (i) symmetry-break already pins `U_1 = U_n = +1` via
/// `x_0 = y_0 = x_{n-1} = y_{n-1} = +1`, so only the pairwise middle
/// equalities need to be emitted here.
///
/// Encoding: `x_j * y_j * x_k * y_k = -1` (where `k = n-1-j`, 0-indexed)
/// is equivalent to odd parity of `{x_j, y_j, x_k, y_k}`, so each
/// distinct middle pair contributes 8 CNF clauses (one per even-parity
/// assignment ruled out).
///
/// Self-paired indices (`j == n-1-j`, only possible for odd `n`) force
/// `U_i * U_i = -1` which is infeasible; in that case we emit a trivial
/// empty clause and the solver returns UNSAT.
pub(crate) fn add_xy_product_law<F, G, S>(
    solver: &mut S,
    x_var: F,
    y_var: G,
    n: usize,
) where F: Fn(usize) -> i32, G: Fn(usize) -> i32, S: SatSolver {
    if n < 2 { return; }
    for j in 1..=((n - 1) / 2) {
        let k = n - 1 - j;
        if j > k { break; }
        if j == k {
            // Infeasible: (x_j*y_j)^2 = +1 ≠ -1. Make it obviously UNSAT.
            solver.add_clause([]);
            return;
        }
        let a = x_var(j);
        let b = y_var(j);
        let c = x_var(k);
        let d = y_var(k);
        // Forbid every even-parity assignment of (a,b,c,d):
        //   0 true, all four 2-true combos, 4 true.
        solver.add_clause([ a,  b,  c,  d]);  // rule out (F,F,F,F)
        solver.add_clause([-a, -b, -c, -d]);  // rule out (T,T,T,T)
        solver.add_clause([-a, -b,  c,  d]);  // rule out (T,T,F,F)
        solver.add_clause([-a,  b, -c,  d]);  // rule out (T,F,T,F)
        solver.add_clause([-a,  b,  c, -d]);  // rule out (T,F,F,T)
        solver.add_clause([ a, -b, -c,  d]);  // rule out (F,T,T,F)
        solver.add_clause([ a, -b,  c, -d]);  // rule out (F,T,F,T)
        solver.add_clause([ a,  b, -c, -d]);  // rule out (F,F,T,T)
    }
}


/// Build SAT XY template with PB constraints for sum constraints
/// and quadratic PB agree pairs per lag. No XNOR auxiliary variables.
/// Multi-tuple variant of `build_sat_xy_clauses`.  Builds V_x and V_y
/// as the union of `{cnt(+|σ|), cnt(-|σ|)}` over the given tuples, so
/// a single XY SAT call covers every unsigned (σ_X, σ_Y) combination
/// in the list.  Rule-(i)..(vi) clauses are unchanged (they're
/// position-level, not tuple-level).  Returns `None` if every tuple is
/// infeasible (parity mismatch on both X and Y).
pub(crate) fn build_sat_xy_clauses_multi(
    problem: Problem,
    tuples: &[SumTuple],
    solver: &mut impl SatSolver,
) -> Option<(Vec<LagPairs>, usize)> {
    build_sat_xy_clauses_multi_opts(problem, tuples, solver, false)
}


/// Like `build_sat_xy_clauses_multi`, but optionally appends the
/// XY product-law conjecture (`U_i = -U_{n+1-i}` pairwise) on top of
/// the canonical rules. See `add_xy_product_law`.
pub(crate) fn build_sat_xy_clauses_multi_opts(
    problem: Problem,
    tuples: &[SumTuple],
    solver: &mut impl SatSolver,
    conj_xy_product: bool,
) -> Option<(Vec<LagPairs>, usize)> {
    let n = problem.n;

    let x_var = |i: usize| -> i32 { (i + 1) as i32 };
    let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };

    // Symmetry breaking (rule i).
    solver.add_clause([x_var(0)]);
    solver.add_clause([y_var(0)]);
    solver.add_clause([x_var(n - 1)]);
    solver.add_clause([y_var(n - 1)]);

    // Rules (ii)/(iii)/(vi): palindromic-break chains + swap break.
    let mut next_var = (2 * n + 1) as i32;
    add_palindromic_break(solver, n, x_var, false, 1, &mut next_var);
    add_palindromic_break(solver, n, y_var, false, 1, &mut next_var);
    add_swap_break(solver, x_var, y_var, n);

    // Optional XY product-law conjecture (toggle: off by default,
    // enabled by `--conj-xy-product`). See conjectures/xy-product.md
    // and `add_xy_product_law` for the encoding.
    if conj_xy_product {
        add_xy_product_law(solver, x_var, y_var, n);
    }

    // Sum constraints via PbSetEq over the union across `tuples`.
    let x_lits: Vec<i32> = (0..n).map(|i| x_var(i)).collect();
    let y_lits: Vec<i32> = (0..n).map(|i| y_var(i)).collect();
    let mut x_values: Vec<u32> = Vec::new();
    let mut y_values: Vec<u32> = Vec::new();
    for t in tuples {
        let abs_x = t.x.abs();
        let abs_y = t.y.abs();
        for &sx in if abs_x == 0 { &[0i32] as &[i32] } else { &[1, -1] } {
            if let Some(c) = sigma_full_to_cnt(sx * abs_x, 0, n) {
                if !x_values.contains(&c) { x_values.push(c); }
            }
        }
        for &sy in if abs_y == 0 { &[0i32] as &[i32] } else { &[1, -1] } {
            if let Some(c) = sigma_full_to_cnt(sy * abs_y, 0, n) {
                if !y_values.contains(&c) { y_values.push(c); }
            }
        }
    }
    if x_values.is_empty() || y_values.is_empty() { return None; }
    x_values.sort_unstable();
    y_values.sort_unstable();
    solver.add_pb_set_eq(&x_lits, &x_values);
    solver.add_pb_set_eq(&y_lits, &y_values);

    // Shared lag-pair construction (same as single-tuple path).
    build_xy_lag_pairs(n)
}


/// Extracted lag-pair construction used by both the single-tuple and
/// multi-tuple XY template builders.
pub(crate) fn build_xy_lag_pairs(n: usize) -> Option<(Vec<LagPairs>, usize)> {
    let x_var = |i: usize| -> i32 { (i + 1) as i32 };
    let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };
    let mut lag_pairs = Vec::with_capacity(n);
    lag_pairs.push(LagPairs { lits_a: Vec::new(), lits_b: Vec::new() });
    for s in 1..n {
        let mut lits_a = Vec::with_capacity(4 * (n - s));
        let mut lits_b = Vec::with_capacity(4 * (n - s));
        for i in 0..(n - s) {
            lits_a.push(x_var(i));
            lits_b.push(x_var(i + s));
            lits_a.push(-x_var(i));
            lits_b.push(-x_var(i + s));
        }
        for i in 0..(n - s) {
            lits_a.push(y_var(i));
            lits_b.push(y_var(i + s));
            lits_a.push(-y_var(i));
            lits_b.push(-y_var(i + s));
        }
        lag_pairs.push(LagPairs { lits_a, lits_b });
    }
    Some((lag_pairs, n))
}


#[allow(dead_code)] // kept as a convenience wrapper (single-tuple = 1-element slice)
pub(crate) fn build_sat_xy_clauses(
    problem: Problem,
    tuple: SumTuple,
    solver: &mut impl SatSolver,
) -> Option<(Vec<LagPairs>, usize)> {
    // Single-tuple path = multi-tuple path with a one-element slice.
    build_sat_xy_clauses_multi(problem, std::slice::from_ref(&tuple), solver)
}


/// Trait abstracting over radical::Solver and cadical::Solver.
#[allow(dead_code)]
pub(crate) trait SatSolver {
    fn add_clause<I: IntoIterator<Item = i32>>(&mut self, lits: I);
    fn add_pb_eq(&mut self, lits: &[i32], coeffs: &[u32], target: u32);
    fn add_pb_set_eq(&mut self, lits: &[i32], values: &[u32]);
    fn add_quad_pb_eq(&mut self, lits_a: &[i32], lits_b: &[i32], coeffs: &[u32], target: u32);
    fn add_xor_constraint(&mut self, aux: i32, a: i32, b: i32);
    fn solve_with_assumptions(&mut self, assumptions: &[i32]) -> Option<bool>;
    fn value(&self, var: i32) -> Option<bool>;
    fn reset(&mut self);
    fn set_conflict_limit(&mut self, limit: u64);
}


impl SatSolver for radical::Solver {
    fn add_clause<I: IntoIterator<Item = i32>>(&mut self, lits: I) {
        self.add_clause(lits);
    }
    fn add_pb_eq(&mut self, lits: &[i32], coeffs: &[u32], target: u32) {
        self.add_pb_eq(lits, coeffs, target);
    }
    fn add_pb_set_eq(&mut self, lits: &[i32], values: &[u32]) {
        self.add_pb_set_eq(lits, values);
    }
    fn add_quad_pb_eq(&mut self, lits_a: &[i32], lits_b: &[i32], coeffs: &[u32], target: u32) {
        self.add_quad_pb_eq(lits_a, lits_b, coeffs, target);
    }
    fn add_xor_constraint(&mut self, aux: i32, a: i32, b: i32) {
        // XNOR: aux = (a ↔ b), i.e., aux ⊕ a ⊕ b = true (odd parity)
        self.add_xor(&[aux, a, b], true);
    }
    fn solve_with_assumptions(&mut self, assumptions: &[i32]) -> Option<bool> {
        self.solve_with_assumptions(assumptions)
    }
    fn value(&self, var: i32) -> Option<bool> {
        self.value(var)
    }
    fn reset(&mut self) {
        self.reset();
    }
    fn set_conflict_limit(&mut self, limit: u64) {
        self.set_conflict_limit(limit);
    }
}


#[cfg(feature = "cadical")]
impl SatSolver for cadical::Solver {
    fn add_clause<I: IntoIterator<Item = i32>>(&mut self, lits: I) {
        self.add_clause(lits);
    }
    fn add_pb_eq(&mut self, _lits: &[i32], _coeffs: &[u32], _target: u32) {
        unimplemented!("CaDiCaL backend uses clause-based encoding, not PB");
    }
    fn add_pb_set_eq(&mut self, _lits: &[i32], _values: &[u32]) {
        unimplemented!("CaDiCaL backend uses clause-based encoding, not PbSetEq");
    }
    fn add_quad_pb_eq(&mut self, _a: &[i32], _b: &[i32], _c: &[u32], _t: u32) {
        unimplemented!("CaDiCaL backend uses clause-based encoding, not quad PB");
    }
    fn add_xor_constraint(&mut self, _aux: i32, _a: i32, _b: i32) {
        // CaDiCaL doesn't support native XOR — clauses handle it
    }
    fn solve_with_assumptions(&mut self, assumptions: &[i32]) -> Option<bool> {
        self.solve_with(assumptions.iter().copied())
    }
    fn value(&self, var: i32) -> Option<bool> {
        self.value(var)
    }
    fn reset(&mut self) {
        // CaDiCaL auto-resets after solve
    }
    fn set_conflict_limit(&mut self, _limit: u64) {
        // CaDiCaL uses its own limit mechanism
    }
}


impl SatXYTemplate {
    pub(crate) fn build(problem: Problem, tuple: SumTuple, sat_config: &radical::SolverConfig) -> Option<Self> {
        Self::build_multi(problem, std::slice::from_ref(&tuple), sat_config)
    }

    /// Multi-tuple template: `PbSetEq` on X and Y unions the ±|σ| counts
    /// across every tuple in `tuples`.  A single solver covers every
    /// unsigned (σ_X, σ_Y) pair in the list — the SAT picks a
    /// rule-(i)..(vi)-consistent sign combination at solve time.
    pub(crate) fn build_multi(problem: Problem, tuples: &[SumTuple], sat_config: &radical::SolverConfig) -> Option<Self> {
        Self::build_multi_opts(problem, tuples, sat_config, false)
    }

    /// Like `build_multi`, but appends the XY product-law conjecture
    /// when `conj_xy_product = true` (see `add_xy_product_law`).
    pub(crate) fn build_multi_opts(
        problem: Problem,
        tuples: &[SumTuple],
        sat_config: &radical::SolverConfig,
        conj_xy_product: bool,
    ) -> Option<Self> {
        #[cfg(not(feature = "cadical"))]
        let mut solver: radical::Solver = { let mut s = radical::Solver::new(); s.config = sat_config.clone(); s };
        #[cfg(feature = "cadical")]
        let mut solver: cadical::Solver = Default::default();

        let (lag_pairs, n) = build_sat_xy_clauses_multi_opts(problem, tuples, &mut solver, conj_xy_product)?;
        #[cfg(not(feature = "cadical"))]
        solver.reserve_for_search(200);
        Some(Self { solver, lag_pairs, n })
    }

    /// Quick feasibility check: are the cardinality targets in range?
    pub(crate) fn is_feasible(&self, candidate: &CandidateZW) -> bool {
        let n = self.n;
        for s in 1..n {
            let Some(target) = xy_agree_target(n, s, &candidate.zw_autocorr) else { return false; };
            let max_pairs = 2 * (n - s);
            if target > max_pairs { return false; }
        }
        true
    }

    /// Clone the template solver and add per-candidate constraints:
    /// GJ equalities, quad PB per lag, and XOR parity constraints.
    /// Returns None if infeasible or GJ detects a contradiction.
    pub(crate) fn prepare_candidate_solver(&self, candidate: &CandidateZW) -> Option<radical::Solver> {
        if !self.is_feasible(candidate) { return None; }
        let n = self.n;
        let Some(equalities) = gj_candidate_equalities(n, candidate) else { return None; };

        let mut solver = self.solver.clone();
        for &(a, b, equal) in &equalities {
            if equal {
                solver.add_clause([-a, b]);
                solver.add_clause([a, -b]);
            } else {
                solver.add_clause([-a, -b]);
                solver.add_clause([a, b]);
            }
        }

        // Add quadratic PB constraints for each lag's agree target
        for s in 1..n {
            let target = xy_agree_target(n, s, &candidate.zw_autocorr).unwrap();
            let lp = &self.lag_pairs[s];
            let ones: Vec<u32> = vec![1; lp.lits_a.len()];
            solver.add_quad_pb_eq(&lp.lits_a, &lp.lits_b, &ones, target as u32);
        }

        // GF(2) XOR constraints: parity of agree count at each lag.
        if solver.config.xor_propagation && n >= 8 {
            for s in 1..n {
                let Some(target) = xy_agree_target(n, s, &candidate.zw_autocorr) else { continue; };
                let k = 2 * (n - s);
                let parity = ((target + k) % 2) == 1;
                let mut in_xor = vec![false; 2 * n];
                for i in 0..(n - s) {
                    in_xor[i] ^= true;
                    in_xor[i + s] ^= true;
                }
                for i in 0..(n - s) {
                    in_xor[n + i] ^= true;
                    in_xor[n + i + s] ^= true;
                }
                let vars: Vec<i32> = in_xor.iter().enumerate()
                    .filter(|&(_, &v)| v)
                    .map(|(i, _)| (i + 1) as i32)
                    .collect();
                if !vars.is_empty() {
                    solver.add_xor(&vars, parity);
                }
            }
        }

        Some(solver)
    }

    /// Extract X/Y solution from a solved SAT solver.
    pub(crate) fn extract_xy(&self, solver: &radical::Solver) -> (PackedSeq, PackedSeq) {
        let n = self.n;
        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };
        (extract_seq(solver, x_var, n), extract_seq(solver, y_var, n))
    }

    /// Solve for X/Y given a specific Z/W candidate.
    /// Solve a single (Z, W) candidate to completion with no conflict
    /// limit. Used by tests and by the `--test-zw` diagnostic path; the
    /// production XY stage goes through `SolveXyPerCandidate` directly.
    pub(crate) fn solve_for(&self, candidate: &CandidateZW) -> Option<(PackedSeq, PackedSeq)> {
        let mut solver = self.prepare_candidate_solver(candidate)?;
        match solver.solve() {
            Some(true) => Some(self.extract_xy(&solver)),
            _ => None,
        }
    }
}


/// BDKR rule (ii)/(iii)/(vi) pre-filter applied to the packed XY
/// boundary bits.  Bits 0..k-1 hold sub-MDD prefix positions (= seq
/// positions 0..k-1); bits k..2k-1 hold the suffix (= seq positions
/// n-k..n-1) with sub-MDD pos `k+i` ↔ seq pos `n-k+i` ↔ mirror bit
/// `2k-1-i` of the pair partner.
pub(crate) fn xy_boundary_passes_rules(x_bits: u32, y_bits: u32, n: usize, k: usize) -> bool {
    // Rule (ii) on X:  first j in [1, k-1] with x[j] ≠ x[n-1-j] must
    // have x[j] = +1.  Both positions are in-boundary for j < k.
    let last_pair = (n - 2) / 2;
    for j in 1..k.min(last_pair + 1) {
        let bit_j = (x_bits >> j) & 1;
        let bit_mirror = (x_bits >> (2 * k - 1 - j)) & 1;
        if bit_j != bit_mirror {
            if bit_j == 0 { return false; }
            break;
        }
    }
    // Rule (iii) on Y.
    for j in 1..k.min(last_pair + 1) {
        let bit_j = (y_bits >> j) & 1;
        let bit_mirror = (y_bits >> (2 * k - 1 - j)) & 1;
        if bit_j != bit_mirror {
            if bit_j == 0 { return false; }
            break;
        }
    }
    // Rule (vi) — requires n > 2 and that n-2 is in the suffix boundary
    // (⇔ k ≥ 2).  Bit mapping: x[1]=bit 1, x[n-2]=bit 2k-2.
    if n > 2 && k >= 2 {
        let x1 = (x_bits >> 1) & 1;
        let y1 = (y_bits >> 1) & 1;
        let bit_nm2 = 2 * k - 2;
        let x_nm2 = (x_bits >> bit_nm2) & 1;
        let y_nm2 = (y_bits >> bit_nm2) & 1;
        if x1 != y1 {
            if x1 == 0 { return false; } // forbid x[1]=-1 ∧ y[1]=+1
        } else {
            // "a[2] = b[2]" branch of rule (vi): a[n-1]=+1 ∧ b[n-1]=-1.
            if x_nm2 == 0 || y_nm2 == 1 { return false; }
        }
    }
    true
}


/// Walk the XY bottom half of the reordered MDD, emitting (x_bits, y_bits)
/// that pass sum compatibility with the given tuple.
pub(crate) fn walk_xy_sub_mdd<F: FnMut(u32, u32)>(
    nid: u32, level: usize, xy_depth: usize,
    x_acc: u32, y_acc: u32,
    pos_order: &[usize], nodes: &[[u32; 4]],
    max_bnd_sum: i32, middle_n: i32, tuples: &[SumTuple],
    callback: &mut F,
) {
    let n_full = middle_n as usize + 2 * xy_depth / 2;
    let k_full = xy_depth / 2;
    // Feasibility test takes ANY tuple in the candidate list — if any
    // one admits this boundary, we pass it to the SAT.  Using a single
    // representative tuple would spuriously reject (x_bits, y_bits)
    // pairs valid for another tuple in the set (e.g., a T4-swap image).
    let feasible = |val: i32, middle_n: i32| -> bool {
        val.abs() <= middle_n && (val + middle_n) % 2 == 0
    };
    walk_mdd_4way(nid, level, xy_depth, x_acc, y_acc, pos_order, nodes,
        &mut |x_bits, y_bits, _nid| {
            let x_bnd_sum = 2 * (x_bits.count_ones() as i32) - max_bnd_sum;
            let y_bnd_sum = 2 * (y_bits.count_ones() as i32) - max_bnd_sum;
            let ok = tuples.iter().any(|t| {
                // Try both signs of σ_X / σ_Y (PbSetEq lets the SAT pick
                // either).
                let x_abs = t.x.abs();
                let y_abs = t.y.abs();
                let x_signs: &[i32] = if x_abs == 0 { &[0] } else { &[1, -1] };
                let y_signs: &[i32] = if y_abs == 0 { &[0] } else { &[1, -1] };
                x_signs.iter().any(|&sx| feasible(sx * x_abs - x_bnd_sum, middle_n))
                    && y_signs.iter().any(|&sy| feasible(sy * y_abs - y_bnd_sum, middle_n))
            });
            if !ok { return; }
            // BDKR rules (ii)/(iii)/(vi) pre-filter on the boundary
            // bits.  The XY SAT still enforces the full rule including
            // middle positions; this catches the boundary-only part
            // cheaply so we skip the SAT call setup entirely.
            if !xy_boundary_passes_rules(x_bits, y_bits, n_full, k_full) { return; }
            callback(x_bits, y_bits);
        });
}


/// Return true iff the XY sub-MDD rooted at `xy_root` has at least one
/// (x_bits, y_bits) leaf compatible with the tuple's sum constraints.
/// Early-exits on the first valid candidate. Used to fail-fast SolveZ
/// items whose boundary can't possibly produce a valid XY completion.
pub(crate) fn any_valid_xy(
    nid: u32, level: usize, xy_depth: usize,
    x_acc: u32, y_acc: u32,
    pos_order: &[usize], nodes: &[[u32; 4]],
    max_bnd_sum: i32, middle_n: i32, tuple: SumTuple,
) -> bool {
    // Magnitude-based feasibility (tries both σ signs, matching walk_xy_sub_mdd).
    let feasible = |val: i32, middle_n: i32| -> bool {
        val.abs() <= middle_n && (val + middle_n) % 2 == 0
    };
    let check_leaf = |x_acc: u32, y_acc: u32| -> bool {
        let x_bnd_sum = 2 * (x_acc.count_ones() as i32) - max_bnd_sum;
        let y_bnd_sum = 2 * (y_acc.count_ones() as i32) - max_bnd_sum;
        let x_abs = tuple.x.abs();
        let y_abs = tuple.y.abs();
        let x_signs: &[i32] = if x_abs == 0 { &[0] } else { &[1, -1] };
        let y_signs: &[i32] = if y_abs == 0 { &[0] } else { &[1, -1] };
        x_signs.iter().any(|&sx| feasible(sx * x_abs - x_bnd_sum, middle_n))
            && y_signs.iter().any(|&sy| feasible(sy * y_abs - y_bnd_sum, middle_n))
    };
    if nid == mdd_reorder::DEAD { return false; }
    if level == xy_depth {
        return check_leaf(x_acc, y_acc);
    }
    if nid == mdd_reorder::LEAF {
        return true;
    }
    let pos = pos_order[level];
    for branch in 0u32..4 {
        let child = nodes[nid as usize][branch as usize];
        if child == mdd_reorder::DEAD { continue; }
        let a_val = (branch >> 0) & 1;
        let b_val = (branch >> 1) & 1;
        if any_valid_xy(
            child, level + 1, xy_depth,
            x_acc | (a_val << pos), y_acc | (b_val << pos),
            pos_order, nodes, max_bnd_sum, middle_n, tuple,
        ) { return true; }
    }
    false
}




pub(crate) struct LagFilter { s: usize, pairs: Vec<(u32, u32)>, max_unknown: i32, num_bnd_pairs: i32 }
pub(crate) struct TermBndInfo { var_a: usize, var_b: usize, neg_a: bool, neg_b: bool, both_bnd: bool }


/// Outcome of `SolveXyPerCandidate::try_candidate` for a single
/// `(x_bits, y_bits)` XY boundary.
pub(crate) enum XyTryResult {
    /// Rejected by the GJ equality or partial-lag autocorrelation filter
    /// — the SAT solver was never invoked.
    Pruned,
    /// SAT solved successfully; the extracted `(X, Y)` is attached.
    Sat(PackedSeq, PackedSeq),
    /// SAT proved UNSAT cleanly.
    Unsat,
    /// SAT hit its conflict limit without deciding.
    Timeout,
}


/// Per-solve search stats captured around `try_candidate`'s SAT call.
/// Zero when the candidate was pruned before invoking SAT.
#[derive(Default, Clone, Copy)]
pub(crate) struct XyStats {
    /// Branching decisions made by the SAT solver during this call.
    pub(crate) decisions: u64,
    /// Variable assignments forced by propagation (clause BCP, PB, quad
    /// PB, XOR, MDD, spectral). Excludes branching decisions.
    pub(crate) propagations: u64,
    /// Variables already forced at decision level 0 BEFORE this SAT call
    /// runs — i.e., pruned by constraint setup + initial propagation.
    /// For XY this captures GJ equalities + quad PB initial unit
    /// propagation; the remaining `free_vars` is the actual search space.
    pub(crate) vars_pre_forced: u64,
    /// Variables free to search (num_vars - vars_pre_forced) at solve
    /// start. Decisions/free_vars indicates how deep the SAT search went
    /// relative to the theoretical sub-problem tree height.
    pub(crate) free_vars: u64,
    /// Cover fraction × 1_000_000. Represents the share of this XY
    /// sub-problem's search space that the solve actually proved or
    /// explored. UNSAT/SAT contribute 1.0 (== 1_000_000); timeouts
    /// contribute the partial fraction `log2(decisions+1)/free_vars`,
    /// clamped to [0, 1].
    pub(crate) cover_micro: u64,
}


/// Compute the cover fraction (× 1_000_000) for a single SAT result.
/// SAT/UNSAT mean the sub-problem is fully accounted for; on timeout,
/// estimate the explored fraction from decisions vs. tree height.
pub(crate) fn xy_cover_micro(result: Option<bool>, decisions: u64, free_vars: u64) -> u64 {
    match result {
        Some(_) => 1_000_000, // SAT or UNSAT — full coverage of this sub-problem
        None => {
            let tree_log2 = (free_vars as f64).max(1.0);
            let explored_log2 = ((decisions as f64) + 1.0).log2();
            let frac = (explored_log2 / tree_log2).clamp(0.0, 1.0);
            (frac * 1_000_000.0) as u64
        }
    }
}










/// Per-(Z,W) prepared state for shared XY SAT solving. Built once per
/// candidate via `SolveXyPerCandidate::new`, consulted via `try_candidate`
/// for each XY boundary `(x_bits, y_bits)` encountered during the
/// sub-MDD walk.
///
/// Owns the cloned template solver with GJ equalities + per-lag quad PB
/// constraints added, plus pre-filter tables (GJ equality list, partial-
/// lag autocorrelation filters, quad PB term info) and scratch buffers
/// for the per-candidate fast path.
pub(crate) struct SolveXyPerCandidate {
    pub(crate) n: usize,
    pub(crate) k: usize,
    pub(crate) solver: radical::Solver,
    pub(crate) equalities: Vec<(i32, i32, bool)>,
    pub(crate) qpb_term_info: Vec<Vec<TermBndInfo>>,
    pub(crate) lag_filters: Vec<LagFilter>,
    pub(crate) targets: Vec<i32>,
    pub(crate) term_state_buf: Vec<u8>,
    pub(crate) configs_tested: usize,
}


impl SolveXyPerCandidate {
    /// Build the per-candidate state. Returns `None` if the (Z,W)
    /// candidate is infeasible or GJ detects a contradiction up front.
    pub(crate) fn new(
        problem: Problem,
        candidate: &CandidateZW,
        template: &SatXYTemplate,
        k: usize,
    ) -> Option<Self> {
        let n = problem.n;
        if !template.is_feasible(candidate) { return None; }
        let equalities = gj_candidate_equalities(n, candidate)?;

        // Clone the template solver once per (Z,W) pair and add the
        // per-pair constraints (GJ equalities + full per-lag quad PB).
        let mut solver = template.solver.clone();
        for &(a, b, equal) in &equalities {
            if equal { solver.add_clause([-a, b]); solver.add_clause([a, -b]); }
            else { solver.add_clause([-a, -b]); solver.add_clause([a, b]); }
        }
        for s in 1..n {
            let target = xy_agree_target(n, s, &candidate.zw_autocorr).unwrap();
            let lp = &template.lag_pairs[s];
            let ones: Vec<u32> = vec![1; lp.lits_a.len()];
            solver.add_quad_pb_eq(&lp.lits_a, &lp.lits_b, &ones, target as u32);
        }
        solver.skip_backtrack_quad_pb = true;

        // Per-quad-PB term info: precompute which terms are both-in-boundary.
        let is_bnd = |pos: usize| -> bool { pos < k || pos >= n - k };
        let num_qpb = solver.num_quad_pb();
        let mut qpb_term_info: Vec<Vec<TermBndInfo>> = Vec::with_capacity(num_qpb);
        for qi in 0..num_qpb {
            let nt = solver.quad_pb_num_terms(qi);
            let mut infos = Vec::with_capacity(nt);
            for ti in 0..nt {
                let (va, vb, na, nb) = solver.quad_pb_term_info(qi, ti);
                let pa = va % n; let pb = vb % n;
                infos.push(TermBndInfo { var_a: va, var_b: vb, neg_a: na, neg_b: nb, both_bnd: is_bnd(pa) && is_bnd(pb) });
            }
            qpb_term_info.push(infos);
        }

        // Partial-lag autocorrelation filter (cheap bitwise pre-filter).
        let pos_to_bit = |pos: usize| -> u32 {
            if pos < k { pos as u32 } else { (k + pos - (n - k)) as u32 }
        };
        let targets: Vec<i32> = (0..n).map(|s| if s == 0 { 0 } else { -candidate.zw_autocorr[s] }).collect();
        let mut lag_filters: Vec<LagFilter> = Vec::new();
        for s in 1..n {
            let mut pairs = Vec::new();
            let mut unk = 0i32;
            for i in 0..n - s {
                if is_bnd(i) && is_bnd(i + s) {
                    pairs.push((pos_to_bit(i), pos_to_bit(i + s)));
                } else { unk += 2; }
            }
            if !pairs.is_empty() && unk > 0 {
                lag_filters.push(LagFilter { s, pairs: pairs.clone(), max_unknown: unk, num_bnd_pairs: 2 * pairs.len() as i32 });
            }
        }
        lag_filters.sort_by_key(|f| f.max_unknown);

        let max_terms = qpb_term_info.iter().map(|v| v.len()).max().unwrap_or(0);
        let term_state_buf = vec![0u8; max_terms];

        Some(Self {
            n, k, solver, equalities, qpb_term_info, lag_filters, targets,
            term_state_buf, configs_tested: 0,
        })
    }

    /// Try one XY boundary `(x_bits, y_bits)`: run the GJ + lag pre-
    /// filters, inject the quad PB term state, then SAT-solve with the
    /// boundary literals as assumptions. Returns the outcome plus
    /// per-solve search stats (zeroed on pre-filter pruning).
    pub(crate) fn try_candidate(&mut self, x_bits: u32, y_bits: u32) -> (XyTryResult, XyStats) {
        let n = self.n;
        let k = self.k;
        let is_bnd = |pos: usize| -> bool { pos < k || pos >= n - k };
        let pos_to_bit = |pos: usize| -> u32 {
            if pos < k { pos as u32 } else { (k + pos - (n - k)) as u32 }
        };
        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };

        // GJ equality pre-filter on boundary bits.
        for &(a, b, equal) in &self.equalities {
            let va = (a.unsigned_abs() as usize) - 1;
            let vb = (b.unsigned_abs() as usize) - 1;
            let pa = va % n; let pb = vb % n;
            if !is_bnd(pa) || !is_bnd(pb) { continue; }
            let ba = if va < n { (x_bits >> pos_to_bit(pa)) & 1 } else { (y_bits >> pos_to_bit(pa)) & 1 };
            let bb = if vb < n { (x_bits >> pos_to_bit(pb)) & 1 } else { (y_bits >> pos_to_bit(pb)) & 1 };
            let need_xor = (a < 0) as u32 ^ (b < 0) as u32 ^ (!equal) as u32;
            if (ba ^ bb) != need_xor { return (XyTryResult::Pruned, XyStats::default()); }
        }
        // Partial-lag autocorrelation pre-filter.
        for lf in &self.lag_filters {
            let mut disagree = 0u32;
            for &(bi, bj) in &lf.pairs {
                disagree += ((x_bits >> bi) ^ (x_bits >> bj)) & 1;
                disagree += ((y_bits >> bi) ^ (y_bits >> bj)) & 1;
            }
            let kn = lf.num_bnd_pairs - 2 * disagree as i32;
            if (self.targets[lf.s] - kn).abs() > lf.max_unknown { return (XyTryResult::Pruned, XyStats::default()); }
        }

        // Expand boundary bits and inject quad PB term states.
        let mut xv = [0i8; 64]; let mut yv = [0i8; 64];
        let (xp, xs) = expand_boundary_bits(x_bits, k);
        let (yp, ys) = expand_boundary_bits(y_bits, k);
        xv[..k].copy_from_slice(&xp); xv[n-k..n].copy_from_slice(&xs);
        yv[..k].copy_from_slice(&yp); yv[n-k..n].copy_from_slice(&ys);
        let mut bnd_vals = [0i8; 128];
        for i in 0..k { bnd_vals[i] = xv[i]; bnd_vals[n-k+i] = xv[n-k+i]; }
        for i in 0..k { bnd_vals[n+i] = yv[i]; bnd_vals[n+n-k+i] = yv[n-k+i]; }

        let num_qpb = self.qpb_term_info.len();
        for qi in 0..num_qpb {
            let infos = &self.qpb_term_info[qi];
            let mut st = 0i32; let mut sm = 0i32;
            for (ti, info) in infos.iter().enumerate() {
                if info.both_bnd {
                    let a_val = bnd_vals[info.var_a];
                    let b_val = bnd_vals[info.var_b];
                    let a_true = (a_val == 1 && !info.neg_a) || (a_val == -1 && info.neg_a);
                    let b_true = (b_val == 1 && !info.neg_b) || (b_val == -1 && info.neg_b);
                    if a_true && b_true {
                        self.term_state_buf[ti] = 2; st += 1;
                    } else {
                        let a_false = (a_val == 1 && info.neg_a) || (a_val == -1 && !info.neg_a);
                        let b_false = (b_val == 1 && info.neg_b) || (b_val == -1 && !info.neg_b);
                        if a_false || b_false {
                            self.term_state_buf[ti] = 0;
                        } else {
                            self.term_state_buf[ti] = 1; sm += 1;
                        }
                    }
                } else {
                    self.term_state_buf[ti] = 1; sm += 1;
                }
            }
            self.solver.reset_quad_pb_state(qi, &self.term_state_buf[..infos.len()], st, sm);
        }

        // Assumptions for boundary variables.
        let mut assumptions = Vec::with_capacity(4 * k);
        for i in 0..k {
            assumptions.push(if xv[i] == 1 { x_var(i) } else { -x_var(i) });
            assumptions.push(if yv[i] == 1 { y_var(i) } else { -y_var(i) });
        }
        for i in 0..k {
            let p = n-k+i;
            assumptions.push(if xv[p] == 1 { x_var(p) } else { -x_var(p) });
            assumptions.push(if yv[p] == 1 { y_var(p) } else { -y_var(p) });
        }
        // Snapshot solver search stats before this SAT call. The pre-solve
        // level-0 count captures vars already forced by constraint setup
        // (GJ equalities + quad PB initial propagation); free_vars is the
        // remaining search space the SAT solver actually navigates.
        let d0 = self.solver.num_decisions();
        let p0 = self.solver.num_propagations();
        let vars_pre_forced = self.solver.num_level0_vars() as u64;
        let free_vars = (self.solver.num_vars() as u64).saturating_sub(vars_pre_forced);

        let result = self.solver.solve_with_assumptions(&assumptions);

        let stats = {
            let decisions    = self.solver.num_decisions().saturating_sub(d0);
            let propagations = self.solver.num_propagations().saturating_sub(p0);
            let cover_micro  = xy_cover_micro(result, decisions, free_vars);
            XyStats { decisions, propagations, vars_pre_forced, free_vars, cover_micro }
        };

        let outcome = match result {
            Some(true) => {
                let x = extract_seq(&self.solver, x_var, n);
                let y = extract_seq(&self.solver, y_var, n);
                XyTryResult::Sat(x, y)
            }
            Some(false) => {
                self.configs_tested += 1;
                if self.configs_tested % 8 == 0 {
                    self.solver.clear_learnt();
                }
                XyTryResult::Unsat
            }
            None => {
                self.configs_tested += 1;
                if self.configs_tested % 8 == 0 {
                    self.solver.clear_learnt();
                }
                XyTryResult::Timeout
            }
        };
        (outcome, stats)
    }
}


/// **Prototype (XY_MDD=1)**: solve the XY sub-tree for a given (Z, W)
/// candidate as ONE SAT call using the native MDD propagator, instead
/// of externally walking the sub-MDD and calling `try_candidate` for
/// each leaf.
///
/// Returns a vector of (x_bits, y_bits, x, y) tuples — one per SAT
/// solution found under the provided conflict budget — plus aggregate
/// stats. On UNSAT returns empty vec. Each call after the first uses
/// a blocking clause to enumerate additional solutions.
#[allow(clippy::too_many_arguments)]
pub(crate) fn try_candidate_via_mdd(
    problem: Problem,
    candidate: &CandidateZW,
    template: &SatXYTemplate,
    k: usize,
    xy_root: u32,
    nodes: &[[u32; 4]],
    pos_order: &[usize],
    conflict_limit: u64,
) -> (Option<(PackedSeq, PackedSeq)>, XyStats) {
    let n = problem.n;
    if !template.is_feasible(candidate) {
        return (None, XyStats::default());
    }
    let Some(equalities) = gj_candidate_equalities(n, candidate) else {
        return (None, XyStats::default());
    };

    // Same template clone as SolveXyPerCandidate::new.
    let mut solver = template.solver.clone();
    for &(a, b, equal) in &equalities {
        if equal { solver.add_clause([-a, b]); solver.add_clause([a, -b]); }
        else { solver.add_clause([-a, -b]); solver.add_clause([a, b]); }
    }
    for s in 1..n {
        let target = xy_agree_target(n, s, &candidate.zw_autocorr).unwrap();
        let lp = &template.lag_pairs[s];
        let ones: Vec<u32> = vec![1; lp.lits_a.len()];
        solver.add_quad_pb_eq(&lp.lits_a, &lp.lits_b, &ones, target as u32);
    }
    solver.skip_backtrack_quad_pb = true;

    // MDD level → (X var, Y var). Packed-bit b → actual position:
    //   b < k      → position b     (prefix)
    //   b >= k     → position n - 2k + b  (suffix, expand_boundary_bits-compatible)
    let xy_depth = 2 * k;
    let mut level_x: Vec<i32> = Vec::with_capacity(xy_depth);
    let mut level_y: Vec<i32> = Vec::with_capacity(xy_depth);
    for l in 0..xy_depth {
        let b = pos_order[l];
        let actual_pos = if b < k { b } else { n - 2 * k + b };
        level_x.push((actual_pos + 1) as i32);
        level_y.push((n + actual_pos + 1) as i32);
    }
    solver.add_mdd_constraint(nodes, xy_root, xy_depth, &level_x, &level_y);

    let d0 = solver.num_decisions();
    let p0 = solver.num_propagations();
    let vars_pre_forced = solver.num_level0_vars() as u64;
    let free_vars = (solver.num_vars() as u64).saturating_sub(vars_pre_forced);

    if conflict_limit > 0 { solver.set_conflict_limit(conflict_limit); }
    let result = solver.solve_with_assumptions(&[]);

    let decisions    = solver.num_decisions().saturating_sub(d0);
    let propagations = solver.num_propagations().saturating_sub(p0);
    let cover_micro  = xy_cover_micro(result, decisions, free_vars);
    let stats = XyStats { decisions, propagations, vars_pre_forced, free_vars, cover_micro };

    let xy = match result {
        Some(true) => {
            let x = extract_seq(&solver, |i| (i + 1) as i32, n);
            let y = extract_seq(&solver, |i| (n + i + 1) as i32, n);
            Some((x, y))
        }
        _ => None,
    };
    (xy, stats)
}

