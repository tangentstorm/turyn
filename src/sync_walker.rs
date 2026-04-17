//! Synchronized 4-sequence heuristic walker over the bouncing-order
//! boundary MDD, constructed on the fly, with a persistent CDCL SAT
//! solver that absorbs canonical clauses and the full Turyn identity
//! as per-lag quad PB.
//!
//! Each level pins one boundary position across all four sequences:
//! X[p], Y[p], Z[p], W[p] (W only when p < n-1). Bouncing position
//! order interleaves prefix and suffix: pos_order = [0, n-1, 1, n-2, ...].
//!
//! Pruning is two-layered:
//!   1. Walker-side: per-lag running sum `S(s) = N_X(s) + N_Y(s) + 2N_Z(s)
//!      + 2N_W(s)` with capacity bound `|S(s)| <= max_remaining[level][s]`.
//!      Rejects capacity violations before any SAT call.
//!   2. SAT-side: canonicalization rules (BDKR i..vi) as Tseitin clauses
//!      + per-lag quad PB identity. Propagation fires on walker's unit
//!      assumptions; conflicts learn clauses that persist across the whole
//!      walk (CDCL-driven nogoods for free).
//!
//! Search is DFS with score-ordered siblings. Memoization on
//! (level, sums, forced-bit-signature) skips revisits across the DAG.

#![allow(unused_imports)]

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering as AtomicOrdering};
use std::time::Instant;

use rustc_hash::FxHashMap;

use crate::types::{PackedSeq, Problem};
use crate::legacy_search::{SearchReport, SearchStats};

/// Config slice the walker needs. Pulled from `SearchConfig` at dispatch.
#[derive(Clone)]
pub(crate) struct SyncConfig {
    pub sat_secs: u64,
    pub sat_config: radical::SolverConfig,
    pub conflict_limit: u64,
    /// Per-worker random-ordering seed. Worker 0 uses best-first
    /// (score-ordered) siblings; workers 1.. use random ordering with
    /// this seed so each explores a different region of the tree.
    pub random_seed: Option<u64>,
    /// Shared cancel flag for parallel multi-start workers.
    pub cancel: Option<Arc<AtomicBool>>,
}

/// Immutable context computed once per search.
struct Ctx {
    n: usize,
    m: usize,
    depth: usize,
    /// Bouncing position order: [0, n-1, 1, n-2, ...].
    pos_order: Vec<usize>,
    /// `pos_to_level[p]` = level at which position `p` is pinned.
    pos_to_level: Vec<usize>,
    /// Events that fire when a lag pair closes at this level.
    /// `closure_events[level] = [(lag, kind, pos_a, pos_b, abs_coeff), ...]`.
    closure_events: Vec<Vec<PairEvent>>,
    /// Capacity bound per (level, lag): max `|S(s)|` achievable from
    /// pairs not yet closed after reaching `level`.
    max_remaining: Vec<Vec<i32>>,
    /// Seed mixed into the sibling-shuffle LCG. Worker 0 uses seed 0
    /// and falls back to score-ordered siblings; workers 1.. use
    /// random ordering seeded by their worker id.
    seed: u64,
    /// Shared cancel flag for parallel multi-start: any worker that
    /// finds a solution sets it so the others bail out promptly.
    cancel: Option<Arc<AtomicBool>>,
    /// Wall-clock start of this worker's search; used to stamp
    /// `time_to_first_leaf`.
    start: Instant,
}

#[derive(Copy, Clone, Debug)]
struct PairEvent {
    lag: usize,
    /// 0=X, 1=Y, 2=Z, 3=W.
    kind: u8,
    pos_a: usize,
    pos_b: usize,
    /// 1 for X/Y, 2 for Z/W. Sign comes from the bit product.
    abs_coeff: i16,
}

#[derive(Clone)]
struct State {
    /// Current walker level in 0..depth.
    level: usize,
    /// Running `S(s) = N_X(s) + N_Y(s) + 2*N_Z(s) + 2*N_W(s)` per lag,
    /// indexed by `s` (index 0 unused). Partial over closed pairs only.
    sums: Vec<i16>,
    /// Bit per (kind, pos): 0 = unknown, 1 = +1, 2 = -1. Kind ordering
    /// matches `PairEvent::kind`. Size `4 * n`.
    bits: Vec<u8>,
    /// Assumption literals passed to `solve_with_assumptions`, accumulated
    /// as we descend.
    assumptions: Vec<i32>,
    /// BDKR canonical-rule firing bitmask.
    ///   bit 0 = rule (ii) fired on X
    ///   bit 1 = rule (iii) fired on Y
    ///   bit 2 = rule (iv) fired on Z
    ///   bit 3 = rule (v) fired on W
    rule_state: u8,
}

// Rule-fired bits.
const RULE_II: u8  = 1 << 0;
const RULE_III: u8 = 1 << 1;
const RULE_IV: u8  = 1 << 2;
const RULE_V: u8   = 1 << 3;

impl State {
    fn new(n: usize) -> Self {
        Self {
            level: 0,
            sums: vec![0; n + 1],
            bits: vec![0; 4 * n],
            assumptions: Vec::with_capacity(4 * n),
            rule_state: 0,
        }
    }

    fn bit(&self, kind: u8, pos: usize) -> u8 {
        self.bits[(kind as usize) * self.n_from_bits_len() + pos]
    }

    fn n_from_bits_len(&self) -> usize {
        self.bits.len() / 4
    }

    fn set_bit(&mut self, kind: u8, pos: usize, sign: i8) {
        let n = self.n_from_bits_len();
        self.bits[(kind as usize) * n + pos] = if sign > 0 { 1 } else { 2 };
    }
}

fn kind_coeff(kind: u8) -> i16 {
    match kind {
        0 | 1 => 1,  // X, Y
        2 | 3 => 2,  // Z, W
        _ => unreachable!(),
    }
}

fn kind_xy_len(kind: u8, n: usize, m: usize) -> usize {
    match kind {
        0 | 1 | 2 => n,
        3 => m,
        _ => unreachable!(),
    }
}

fn build_ctx_seeded(problem: Problem, seed: u64, cancel: Option<Arc<AtomicBool>>, start: Instant) -> Ctx {
    let mut ctx = build_ctx(problem);
    ctx.seed = seed;
    ctx.cancel = cancel;
    ctx.start = start;
    ctx
}

fn build_ctx(problem: Problem) -> Ctx {
    let n = problem.n;
    let m = problem.m();
    let k_max = n / 2;
    // Bouncing order: [0, n-1, 1, n-2, ...]
    let mut pos_order = Vec::with_capacity(2 * k_max);
    for j in 0..k_max {
        pos_order.push(j);
        pos_order.push(n - 1 - j);
    }
    let depth = pos_order.len();
    let mut pos_to_level = vec![depth; n];
    for (lvl, &p) in pos_order.iter().enumerate() {
        pos_to_level[p] = lvl;
    }

    let mut closure_events: Vec<Vec<PairEvent>> = vec![Vec::new(); depth];
    // max_remaining[level][lag]: sum over pairs *not yet closed* at `level`.
    // Pair closes at close_level = max(pos_to_level[a], pos_to_level[b]).
    // It is "not yet closed" at levels 0..=close_level.
    let mut max_remaining: Vec<Vec<i32>> = vec![vec![0; n + 1]; depth + 1];

    for s in 1..n {
        // X and Y: pairs (i, i+s) for i in 0..n-s.
        for i in 0..n.saturating_sub(s) {
            for kind in [0u8, 1, 2] {
                let coeff = kind_coeff(kind);
                let a = i;
                let b = i + s;
                let la = pos_to_level[a];
                let lb = pos_to_level[b];
                let close = la.max(lb);
                if close < depth {
                    closure_events[close].push(PairEvent {
                        lag: s, kind, pos_a: a, pos_b: b, abs_coeff: coeff,
                    });
                }
                // Contributes to max_remaining at all levels where at
                // least one endpoint is still unplaced.
                let end_lvl = close.min(depth);
                for lvl in 0..=end_lvl {
                    max_remaining[lvl][s] += coeff as i32;
                }
            }
        }
        // W: pairs (i, i+s) for i in 0..m-s.
        for i in 0..m.saturating_sub(s) {
            let kind = 3u8;
            let coeff = kind_coeff(kind);
            let a = i;
            let b = i + s;
            let la = pos_to_level[a];
            let lb = pos_to_level[b];
            let close = la.max(lb);
            if close < depth {
                closure_events[close].push(PairEvent {
                    lag: s, kind, pos_a: a, pos_b: b, abs_coeff: coeff,
                });
            }
            let end_lvl = close.min(depth);
            for lvl in 0..=end_lvl {
                max_remaining[lvl][s] += coeff as i32;
            }
        }
    }

    Ctx {
        n, m, depth,
        pos_order, pos_to_level,
        closure_events, max_remaining,
        seed: 0, cancel: None, start: Instant::now(),
    }
}

/// Build the persistent SAT solver with canonical clauses + Turyn identity
/// as per-lag quad PB. No MDD constraint (walker provides the boundary
/// traversal), no sum PB (implied by the per-lag quad PBs).
fn build_solver(problem: Problem, sat_config: &radical::SolverConfig) -> radical::Solver {
    let n = problem.n;
    let m = problem.m();
    let x_var = |i: usize| -> i32 { (i + 1) as i32 };
    let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };
    let z_var = |i: usize| -> i32 { (2 * n + i + 1) as i32 };
    let w_var = |i: usize| -> i32 { (3 * n + i + 1) as i32 };

    let mut solver = radical::Solver::new();
    solver.config = sat_config.clone();

    // BDKR Canonical1: X[0]=X[n-1]=Y[0]=Y[n-1]=Z[0]=W[0]=+1.
    solver.add_clause([x_var(0)]);
    solver.add_clause([x_var(n - 1)]);
    solver.add_clause([y_var(0)]);
    solver.add_clause([y_var(n - 1)]);
    solver.add_clause([z_var(0)]);
    solver.add_clause([w_var(0)]);

    // BDKR Canonical6 (XY swap tie-break).
    //   (A[1] ≠ B[1]) → A[1] = +1
    //   (A[1]  = B[1]) → A[n-2] = +1 AND B[n-2] = -1
    // Encoded as five 2-literal clauses (CANONICAL.md §rule (vi)): the
    // two-variable form both forbids the (A[1]=-1, B[1]=+1) combo AND
    // derives the A[n-2]/B[n-2] constraint in the A[1]=B[1] case via
    // CNF distribution `(a ∨ z) ∧ (b ∨ z) ≡ (a ∧ b) ∨ z`.
    if n >= 4 {
        let a1 = x_var(1);
        let b1 = y_var(1);
        let aam = x_var(n - 2);
        let bbm = y_var(n - 2);
        solver.add_clause([a1, -b1]);       // forbid A[1]=-1 AND B[1]=+1
        solver.add_clause([a1, aam]);       // A[1]=-1 → A[n-2]=+1
        solver.add_clause([-b1, aam]);      // B[1]=+1 → A[n-2]=+1
        solver.add_clause([a1, -bbm]);      // A[1]=-1 → B[n-2]=-1
        solver.add_clause([-b1, -bbm]);     // B[1]=+1 → B[n-2]=-1
    }

    // BDKR Canonical2..5 via Tseitin eq / prod chains.
    let mut next_aux: i32 = (3 * n + m + 1) as i32;

    // (ii) A lex-min under reversal: eq_a[j] = (X[j]=X[n-1-j]); chain.
    let mut eq_a: Vec<Option<i32>> = vec![None; n];
    for j in 1..n {
        let mirror = n - 1 - j;
        if mirror <= j { break; }
        let a = x_var(j);
        let b = x_var(mirror);
        let y = next_aux; next_aux += 1;
        solver.add_clause([-y, -a, b]);
        solver.add_clause([-y, a, -b]);
        solver.add_clause([y, a, b]);
        solver.add_clause([y, -a, -b]);
        eq_a[j] = Some(y);
        eq_a[mirror] = Some(y);
    }
    for i in 1..n {
        let mirror = n - 1 - i;
        if mirror <= i { break; }
        let mut clause: Vec<i32> = Vec::with_capacity(i + 1);
        for j in 1..i { if let Some(y) = eq_a[j] { clause.push(-y); } }
        if let Some(y) = eq_a[i] { clause.push(y); }
        clause.push(x_var(i));
        solver.add_clause(clause);
    }

    // (iii) B lex-min — mirror of (ii) on Y.
    let mut eq_b: Vec<Option<i32>> = vec![None; n];
    for j in 1..n {
        let mirror = n - 1 - j;
        if mirror <= j { break; }
        let a = y_var(j);
        let b = y_var(mirror);
        let y = next_aux; next_aux += 1;
        solver.add_clause([-y, -a, b]);
        solver.add_clause([-y, a, -b]);
        solver.add_clause([y, a, b]);
        solver.add_clause([y, -a, -b]);
        eq_b[j] = Some(y);
        eq_b[mirror] = Some(y);
    }
    for i in 1..n {
        let mirror = n - 1 - i;
        if mirror <= i { break; }
        let mut clause: Vec<i32> = Vec::with_capacity(i + 1);
        for j in 1..i { if let Some(y) = eq_b[j] { clause.push(-y); } }
        if let Some(y) = eq_b[i] { clause.push(y); }
        clause.push(y_var(i));
        solver.add_clause(clause);
    }

    // (iv) C anti-symmetric lex-min — flipped eq polarity on Z.
    let mut eq_c: Vec<Option<i32>> = vec![None; n];
    for j in 1..n {
        let mirror = n - 1 - j;
        if mirror <= j { break; }
        let a = z_var(j);
        let b = z_var(mirror);
        let y = next_aux; next_aux += 1;
        solver.add_clause([-y, -a, b]);
        solver.add_clause([-y, a, -b]);
        solver.add_clause([y, a, b]);
        solver.add_clause([y, -a, -b]);
        eq_c[j] = Some(y);
        eq_c[mirror] = Some(y);
    }
    for i in 1..n {
        let mirror = n - 1 - i;
        if mirror <= i { break; }
        let mut clause: Vec<i32> = Vec::with_capacity(i + 1);
        for j in 1..i { if let Some(y) = eq_c[j] { clause.push(y); } }
        if let Some(y) = eq_c[i] { clause.push(-y); }
        clause.push(z_var(i));
        solver.add_clause(clause);
    }

    // (v) D triple-product — XNOR3(W[j], W[m-1-j], W[m-1]) chain.
    let mlen = m;
    let d_last = w_var(mlen - 1);
    let mut prod_d: Vec<Option<i32>> = vec![None; mlen];
    for j in 1..mlen {
        let mirror = mlen - 1 - j;
        if mirror <= j { break; }
        let a = w_var(j);
        let b = w_var(mirror);
        let c = d_last;
        let y = next_aux; next_aux += 1;
        solver.add_clause([-y, a, b, -c]);
        solver.add_clause([-y, a, -b, c]);
        solver.add_clause([-y, -a, b, c]);
        solver.add_clause([-y, -a, -b, -c]);
        solver.add_clause([y, a, b, c]);
        solver.add_clause([y, a, -b, -c]);
        solver.add_clause([y, -a, b, -c]);
        solver.add_clause([y, -a, -b, c]);
        prod_d[j] = Some(y);
        prod_d[mirror] = Some(y);
    }
    // Main clause for rule (v) at index i:
    //   (∃ j<i, premise(j) holds) ∨ ¬premise(i) ∨ W[i]=+1
    // where premise(j) = prod_d[j] = (W[j]*W[m-1-j]*W[m-1] = -1) as a
    // boolean via the XNOR3 aux var above. Positive prod_d[j] in the
    // clause for j<i, NEGATIVE for j=i.
    for i in 1..mlen {
        let mirror = mlen - 1 - i;
        if mirror <= i { break; }
        let mut clause: Vec<i32> = Vec::with_capacity(i + 1);
        for j in 1..i { if let Some(y) = prod_d[j] { clause.push(y); } }
        if let Some(y) = prod_d[i] { clause.push(-y); }
        clause.push(w_var(i));
        solver.add_clause(clause);
    }
    let _ = next_aux;

    // Per-lag quad PB: the full Turyn identity.
    for s in 1..n {
        let mut lits_a: Vec<i32> = Vec::new();
        let mut lits_b: Vec<i32> = Vec::new();
        let mut coeffs: Vec<u32> = Vec::new();
        for i in 0..(n - s) {
            lits_a.push(x_var(i)); lits_b.push(x_var(i + s)); coeffs.push(1);
            lits_a.push(-x_var(i)); lits_b.push(-x_var(i + s)); coeffs.push(1);
            lits_a.push(y_var(i)); lits_b.push(y_var(i + s)); coeffs.push(1);
            lits_a.push(-y_var(i)); lits_b.push(-y_var(i + s)); coeffs.push(1);
            lits_a.push(z_var(i)); lits_b.push(z_var(i + s)); coeffs.push(2);
            lits_a.push(-z_var(i)); lits_b.push(-z_var(i + s)); coeffs.push(2);
        }
        if s < m {
            for i in 0..(m - s) {
                lits_a.push(w_var(i)); lits_b.push(w_var(i + s)); coeffs.push(2);
                lits_a.push(-w_var(i)); lits_b.push(-w_var(i + s)); coeffs.push(2);
            }
        }
        let target = if s < m {
            (3 * n as i32 - 3 * s as i32 - 1) as u32
        } else {
            (2 * (n - s)) as u32
        };
        solver.add_quad_pb_eq(&lits_a, &lits_b, &coeffs, target);
    }

    solver
}

fn var_for(kind: u8, pos: usize, n: usize) -> i32 {
    match kind {
        0 => (pos + 1) as i32,              // X
        1 => (n + pos + 1) as i32,          // Y
        2 => (2 * n + pos + 1) as i32,      // Z
        3 => (3 * n + pos + 1) as i32,      // W
        _ => unreachable!(),
    }
}

/// Harvest all boundary bit values currently forced by the solver.
/// Writes into `state.bits`; returns `true` if any new bit became forced
/// since this state was constructed.
fn harvest_forced(solver: &radical::Solver, state: &mut State, ctx: &Ctx) {
    for kind in 0u8..4 {
        let xy_len = kind_xy_len(kind, ctx.n, ctx.m);
        for pos in 0..xy_len {
            if state.bit(kind, pos) != 0 { continue; }
            let var = var_for(kind, pos, ctx.n);
            if let Some(b) = solver.value(var) {
                state.set_bit(kind, pos, if b { 1 } else { -1 });
            }
        }
    }
}

/// Apply per-lag sum updates for every pair whose SECOND endpoint became
/// known at the current descent step. Runs over all closure events at
/// levels 0..=state.level so freshly-forced bits (from SAT propagation or
/// the current placement) are accounted for.
fn rebuild_sums(state: &mut State, ctx: &Ctx) {
    state.sums.iter_mut().for_each(|v| *v = 0);
    for lvl in 0..=state.level.min(ctx.depth - 1) {
        for ev in &ctx.closure_events[lvl] {
            let a_sign = state.bit(ev.kind, ev.pos_a);
            let b_sign = state.bit(ev.kind, ev.pos_b);
            if a_sign == 0 || b_sign == 0 {
                // Pair nominally closes at this level but one end is
                // unforced (SAT propagation may not have pinned it yet).
                // Treat as not-yet-contributing — capacity check uses
                // `max_remaining` which already accounts for this pair.
                continue;
            }
            let a = if a_sign == 1 { 1i16 } else { -1 };
            let b = if b_sign == 1 { 1i16 } else { -1 };
            state.sums[ev.lag] += (a * b) * ev.abs_coeff;
        }
    }
}

/// Walker-side BDKR rule check for pairs that just closed at this level.
/// Returns Err(()) on rule violation; Ok(new_rule_state) otherwise.
///
/// Checks palindromic pair events only:
///   - X/Y/Z pair (j, n-1-j): rules (ii)/(iii)/(iv).
///   - W pair (j, m-1-j): rule (v), requires W[m-1] already known.
///
/// Rule (ii)/(iii): least i with A[i]≠A[n-1-i] forces A[i]=+1.
///   At pair j, if rule not yet fired and A[j]≠A[n-1-j]:
///     require A[j]=+1, set rule_fired bit.
/// Rule (iv): least i with C[i]=C[n-1-i] forces C[i]=+1.
///   At pair j, if rule not yet fired and Z[j]=Z[n-1-j]:
///     require Z[j]=+1, set rule_fired bit.
/// Rule (v): least i with W[i]·W[m-1-i]·W[m-1] = -1 forces W[i]=+1.
///   At pair j, if rule not yet fired, W[m-1] known, and product=-1:
///     require W[j]=+1, set rule_fired bit.
///
/// A candidate that violates any rule is pruned *before* the SAT call.
fn check_rules(state: &State, ctx: &Ctx, level: usize) -> Result<u8, ()> {
    let n = ctx.n;
    let m = ctx.m;
    let mut rs = state.rule_state;

    for ev in &ctx.closure_events[level] {
        // Rule events only involve palindromic pairs: pos_a + pos_b == n-1
        // for X/Y/Z (length n), or == m-1 for W (length m=n-1).
        let is_palindromic = match ev.kind {
            0 | 1 | 2 => ev.pos_a + ev.pos_b == n - 1,
            3 => ev.pos_a + ev.pos_b == m - 1,
            _ => false,
        };
        if !is_palindromic { continue; }

        let sa = state.bit(ev.kind, ev.pos_a);
        let sb = state.bit(ev.kind, ev.pos_b);
        if sa == 0 || sb == 0 { continue; }
        let sa_sign: i8 = if sa == 1 { 1 } else { -1 };
        let sb_sign: i8 = if sb == 1 { 1 } else { -1 };
        // By symmetry pos_a < pos_b (bouncing order pins low first).
        // Rule forces the "i" position, which is the lower index = pos_a.
        let early_bit = sa_sign;

        match ev.kind {
            0 => {  // X: rule (ii)
                if rs & RULE_II == 0 && sa_sign != sb_sign {
                    if early_bit != 1 { return Err(()); }
                    rs |= RULE_II;
                }
            }
            1 => {  // Y: rule (iii)
                if rs & RULE_III == 0 && sa_sign != sb_sign {
                    if early_bit != 1 { return Err(()); }
                    rs |= RULE_III;
                }
            }
            2 => {  // Z: rule (iv) — note equality polarity
                if rs & RULE_IV == 0 && sa_sign == sb_sign {
                    if early_bit != 1 { return Err(()); }
                    rs |= RULE_IV;
                }
            }
            3 => {  // W: rule (v), needs W[m-1]
                let w_last = state.bit(3, m - 1);
                if w_last == 0 { continue; }
                let w_last_sign: i8 = if w_last == 1 { 1 } else { -1 };
                // premise: W[j] * W[m-1-j] * W[m-1] == -1
                let product = sa_sign * sb_sign * w_last_sign;
                if rs & RULE_V == 0 && product == -1 {
                    if early_bit != 1 { return Err(()); }
                    rs |= RULE_V;
                }
            }
            _ => {}
        }
    }
    Ok(rs)
}

/// Return true if any lag's running sum blows past its remaining capacity.
/// At level `state.level`, max_remaining applies to pairs not yet closed.
fn capacity_violated(state: &State, ctx: &Ctx) -> bool {
    let lvl = state.level.min(ctx.depth);
    let caps = &ctx.max_remaining[lvl];
    for s in 1..ctx.n {
        // Target is 0; remaining capacity must cover |sums[s]|.
        if (state.sums[s] as i32).unsigned_abs() as i32 > caps[s] {
            return true;
        }
    }
    false
}

/// Heuristic score for sibling ordering. Lower = more promising.
///
/// Sum over lags of (S(s)^2 / cap[s]^2) scaled, where cap is the
/// remaining capacity at the current post-placement level. Measures
/// "tightness" of the sums relative to how much the future can push
/// them: low = close to target 0 with slack to spare, high = already
/// saturating.
fn score_state(state: &State, ctx: &Ctx) -> i64 {
    let lvl = state.level.min(ctx.depth);
    let caps = &ctx.max_remaining[lvl];
    let mut total: i64 = 0;
    for s in 1..ctx.n {
        let v = state.sums[s] as i64;
        let c = (caps[s] as i64).max(1);
        total += (v * v * 1024) / (c * c);
    }
    total
}

fn compute_signature(state: &State, ctx: &Ctx) -> u64 {
    // The walker's "state" at a given level is determined by:
    //   - current level
    //   - running per-lag sums S(s)
    //   - walker-placed bits at positions already visited (pos_order[..level])
    //   - rule-fired bitmask
    //
    // NOTE: we deliberately exclude bits beyond the walker frontier
    // (positions pinned purely via harvest_forced from SAT propagation).
    // Those are deterministic functions of the walker prefix + the
    // solver's clause database, so including them makes the signature
    // vary by clause-DB state and prevents memo hits across branches
    // that converge to the same walker state through different routes.
    use std::hash::Hasher;
    let mut h = rustc_hash::FxHasher::default();
    h.write_usize(state.level);
    for s in 1..ctx.n {
        h.write_i16(state.sums[s]);
    }
    // Only include bits at walker-visited positions (pos_order[..level]).
    for (lvl, &pos) in ctx.pos_order.iter().enumerate() {
        if lvl >= state.level { break; }
        for kind in 0u8..4 {
            if pos >= kind_xy_len(kind, ctx.n, ctx.m) { continue; }
            h.write_u8(state.bit(kind, pos));
        }
    }
    h.write_u8(state.rule_state);
    h.finish()
}

#[derive(Clone)]
pub(crate) struct SyncStats {
    pub nodes_visited: u64,
    pub memo_hits: u64,
    pub capacity_rejects: u64,
    pub rule_rejects: u64,
    pub sat_unsat: u64,
    pub leaves_reached: u64,
    pub learned_clauses_final: u64,
    pub max_level_reached: u64,
    /// Count of dfs() calls per level. With DFS the tree's shape at
    /// early levels stabilises once fully explored; later levels are
    /// partial. Used for TTC projection.
    pub nodes_by_level: Vec<u64>,
    /// Count of surviving candidates (post capacity + rule) summed
    /// across all internal nodes. `children_total / internal_nodes`
    /// is the measured effective branching factor b_eff.
    pub children_total: u64,
    /// Count of internal (non-leaf) dfs() calls — parents of children.
    pub internal_nodes: u64,
    /// Elapsed seconds until the walker first hit state.level == depth
    /// (any leaf, solution or not). `None` if no leaf was reached.
    pub time_to_first_leaf: Option<f64>,
}

pub(crate) fn search_sync(
    problem: Problem,
    cfg: &SyncConfig,
    verbose: bool,
) -> (Option<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>, SyncStats, std::time::Duration) {
    let start = Instant::now();
    // Always parallel: one worker per available CPU. Worker 0 runs
    // best-first (score-sorted) siblings; workers 1.. each get a
    // different LCG seed for randomised sibling ordering so they
    // explore independent regions of the tree. Workers do NOT share
    // learnt clauses (Solver isn't Clone/Send for its bulk state);
    // the parallelism benefit is exploration diversity. First worker
    // to find a solution cancels the others via a shared AtomicBool.
    let n_workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
        .max(1);
    search_sync_parallel(problem, cfg, verbose, n_workers, start)
}

fn search_sync_parallel(
    problem: Problem,
    cfg: &SyncConfig,
    verbose: bool,
    n_workers: usize,
    start: Instant,
) -> (Option<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>, SyncStats, std::time::Duration) {
    use std::sync::Mutex;
    use std::thread;

    let cancel = Arc::new(AtomicBool::new(false));
    let result: Arc<Mutex<Option<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>>> =
        Arc::new(Mutex::new(None));
    let stats_agg: Arc<Mutex<SyncStats>> = Arc::new(Mutex::new(SyncStats {
        nodes_visited: 0, memo_hits: 0, capacity_rejects: 0,
        rule_rejects: 0, sat_unsat: 0, leaves_reached: 0,
        learned_clauses_final: 0, max_level_reached: 0,
        nodes_by_level: Vec::new(), children_total: 0, internal_nodes: 0,
        time_to_first_leaf: None,
    }));

    thread::scope(|s| {
        for worker_id in 0..n_workers {
            let cfg = cfg.clone();
            let cancel = Arc::clone(&cancel);
            let result = Arc::clone(&result);
            let stats_agg = Arc::clone(&stats_agg);
            s.spawn(move || {
                // Worker 0: seed=0 → score-sorted best-first siblings.
                // Worker k>0: seed=k → randomised ordering distinct
                // from every other worker.
                let worker_cfg = SyncConfig {
                    random_seed: Some(worker_id as u64),
                    cancel: Some(Arc::clone(&cancel)),
                    ..cfg
                };
                let (sol, stats, _) = search_sync_serial(problem, &worker_cfg, false, start);
                let mut agg = stats_agg.lock().unwrap();
                agg.nodes_visited += stats.nodes_visited;
                agg.memo_hits += stats.memo_hits;
                agg.capacity_rejects += stats.capacity_rejects;
                agg.rule_rejects += stats.rule_rejects;
                agg.sat_unsat += stats.sat_unsat;
                agg.leaves_reached += stats.leaves_reached;
                agg.max_level_reached = agg.max_level_reached.max(stats.max_level_reached);
                if let Some(t) = stats.time_to_first_leaf {
                    agg.time_to_first_leaf = Some(match agg.time_to_first_leaf {
                        Some(cur) => cur.min(t),
                        None => t,
                    });
                }
                agg.children_total += stats.children_total;
                agg.internal_nodes += stats.internal_nodes;
                if agg.nodes_by_level.len() < stats.nodes_by_level.len() {
                    agg.nodes_by_level.resize(stats.nodes_by_level.len(), 0);
                }
                for (i, &c) in stats.nodes_by_level.iter().enumerate() {
                    agg.nodes_by_level[i] += c;
                }
                drop(agg);
                if let Some(s) = sol {
                    let mut r = result.lock().unwrap();
                    if r.is_none() {
                        *r = Some(s);
                        cancel.store(true, AtomicOrdering::Release);
                    }
                }
            });
        }
    });

    let elapsed = start.elapsed();
    let stats = stats_agg.lock().unwrap().clone();
    let found = result.lock().unwrap().clone();
    if verbose {
        eprintln!(
            "sync_walker(parallel x{}): nodes={} cap_rejects={} rule_rejects={} sat_unsat={} leaves={} max_lvl={} elapsed={:?} time_to_first_leaf={}",
            n_workers, stats.nodes_visited, stats.capacity_rejects, stats.rule_rejects, stats.sat_unsat, stats.leaves_reached, stats.max_level_reached, elapsed,
            stats.time_to_first_leaf.map(|t| format!("{:.3}s", t)).unwrap_or_else(|| "(never)".into()),
        );
        let ttc = project_ttc(&stats, problem.n, elapsed.as_secs_f64(), n_workers);
        eprintln!("{}", ttc);
    }
    (found, stats, elapsed)
}

/// Project TTC (time-to-cover) from measured per-level branching + rate.
///
/// Method: take the measured per-level `nodes_by_level[L]` counts from
/// the (partial or full) run. Divide by the number of DFS entries per
/// level (each parent spawns up to b_eff children, each child is a
/// dfs call at level L+1). That gives a measured effective branching
/// factor `b_eff(L) = nodes_by_level[L+1] / nodes_by_level[L]` for
/// levels where `nodes_by_level[L] > 0`.
///
/// Full-cover tree size (for the canonical-post-pruning space):
///   N_total = Σ_{L=0..depth} Π_{ℓ=0..L} b_eff(ℓ)
///           = Π_{ℓ=0..depth-1} b_eff(ℓ)   (with geometric sum ≈ leading term when b>1)
///
/// TTC_serial  = N_total / rate,   TTC_parallel = TTC_serial / n_workers
/// where rate = nodes_visited / elapsed (aggregate across workers in
/// parallel mode, so this is already a parallel rate).
fn project_ttc(stats: &SyncStats, n: usize, elapsed_secs: f64, n_workers: usize) -> String {
    let depth = n;  // bouncing-order depth = n for even n
    let levels = stats.nodes_by_level.len();
    if levels < 2 || elapsed_secs <= 0.0 || stats.nodes_visited == 0 {
        return format!("TTC projection: insufficient data");
    }
    // Measured effective branching per level. Only levels that have
    // been EXITED (finished exploration) give a stable estimate —
    // in DFS early levels stabilise first. For partial runs, use the
    // deepest level where both L and L+1 have at least one visit.
    let mut b_eff: Vec<f64> = Vec::with_capacity(depth);
    for l in 0..depth.min(levels - 1) {
        let parent = stats.nodes_by_level[l];
        let child = stats.nodes_by_level[l + 1];
        if parent == 0 {
            b_eff.push(0.0);
        } else {
            b_eff.push(child as f64 / parent as f64);
        }
    }
    // Projected total tree size assuming measured b_eff(L) holds at
    // every level. For levels where we have no data (L >= max depth
    // reached), use the geometric mean of measured levels as a best
    // guess; clamp below 1.0 to avoid divergence on sparse leaves.
    let measured_avg: f64 = if b_eff.is_empty() { 1.0 } else {
        let log_prod: f64 = b_eff.iter().filter(|&&b| b > 0.0).map(|b| b.ln()).sum();
        let count = b_eff.iter().filter(|&&b| b > 0.0).count().max(1);
        (log_prod / count as f64).exp()
    };
    let mut projected_nodes = 1.0_f64;
    let mut running_product = 1.0_f64;
    for l in 0..depth {
        let b = b_eff.get(l).copied().filter(|&b| b > 0.0).unwrap_or(measured_avg);
        running_product *= b;
        projected_nodes += running_product;
    }
    let rate = stats.nodes_visited as f64 / elapsed_secs;
    let ttc_parallel = projected_nodes / rate;
    let ttc_serial = ttc_parallel * n_workers as f64;
    format!(
        "TTC projection: b_eff per level = [{}]\n\
         TTC projection: measured b_eff geo mean = {:.3}, projected nodes to cover = {:.3e}\n\
         TTC projection: rate = {:.0} nodes/s ({} workers, aggregate),\n\
         TTC projection: TTC_parallel ≈ {:.1}s, TTC_serial ≈ {:.1}s",
        b_eff.iter().map(|b| format!("{:.2}", b)).collect::<Vec<_>>().join(", "),
        measured_avg, projected_nodes, rate, n_workers, ttc_parallel, ttc_serial,
    )
}

fn search_sync_serial(
    problem: Problem,
    cfg: &SyncConfig,
    verbose: bool,
    start: Instant,
) -> (Option<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>, SyncStats, std::time::Duration) {
    let seed = cfg.random_seed.unwrap_or(0);
    let ctx = build_ctx_seeded(problem, seed, cfg.cancel.clone(), start);
    let mut solver = build_solver(problem, &cfg.sat_config);
    if cfg.conflict_limit > 0 {
        solver.set_conflict_limit(cfg.conflict_limit);
    }

    // Initial propagate to fire C1 units + Tseitin chains + quad PBs at level 0.
    // `propagate_only` drains the propagation queue without making decisions,
    // so this is O(n) instead of a full SAT solve.
    if solver.propagate_only(&[]) != Some(true) {
        eprintln!("sync_walker: base solver UNSAT — canonical constraints inconsistent");
        return (None, SyncStats {
            nodes_visited: 0, memo_hits: 0, capacity_rejects: 0,
            rule_rejects: 0, sat_unsat: 0, leaves_reached: 0, learned_clauses_final: 0, max_level_reached: 0,
            nodes_by_level: Vec::new(), children_total: 0, internal_nodes: 0,
            time_to_first_leaf: None,
        }, start.elapsed());
    }

    let mut state = State::new(ctx.n);
    harvest_forced(&solver, &mut state, &ctx);

    let mut memo: FxHashMap<u64, ()> = FxHashMap::default();
    let mut stats = SyncStats {
        nodes_visited: 0, memo_hits: 0, capacity_rejects: 0,
        rule_rejects: 0, sat_unsat: 0, leaves_reached: 0,
        learned_clauses_final: 0, max_level_reached: 0,
        nodes_by_level: vec![0; ctx.depth + 1],
        children_total: 0, internal_nodes: 0,
        time_to_first_leaf: None,
    };

    let deadline = if cfg.sat_secs > 0 {
        Some(start + std::time::Duration::from_secs(cfg.sat_secs))
    } else { None };

    let mut found: Option<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)> = None;
    dfs(&mut solver, &mut state, &ctx, &mut memo, &mut stats, deadline, &mut found);

    let elapsed = start.elapsed();
    if verbose {
        eprintln!(
            "sync_walker: nodes={} memo_hits={} cap_rejects={} rule_rejects={} sat_unsat={} leaves={} max_lvl={} elapsed={:?}",
            stats.nodes_visited, stats.memo_hits, stats.capacity_rejects, stats.rule_rejects, stats.sat_unsat, stats.leaves_reached, stats.max_level_reached, elapsed,
        );
    }
    (found, stats, elapsed)
}

/// DFS descent. Returns true if a solution was found (short-circuits up the stack).
fn dfs(
    solver: &mut radical::Solver,
    state: &mut State,
    ctx: &Ctx,
    memo: &mut FxHashMap<u64, ()>,
    stats: &mut SyncStats,
    deadline: Option<Instant>,
    found: &mut Option<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>,
) -> bool {
    if found.is_some() { return true; }
    if let Some(d) = deadline {
        if Instant::now() >= d { return false; }
    }
    if let Some(c) = &ctx.cancel {
        if c.load(AtomicOrdering::Acquire) { return false; }
    }
    stats.nodes_visited += 1;
    if state.level < stats.nodes_by_level.len() {
        stats.nodes_by_level[state.level] += 1;
    }
    if state.level as u64 > stats.max_level_reached {
        stats.max_level_reached = state.level as u64;
    }

    if state.level >= ctx.depth {
        stats.leaves_reached += 1;
        if stats.time_to_first_leaf.is_none() {
            stats.time_to_first_leaf = Some(ctx.start.elapsed().as_secs_f64());
        }
        // All boundary positions visited. Every bit should be pinned;
        // running sums must all equal 0 (target of Turyn identity).
        let sums_all_zero = (1..ctx.n).all(|s| state.sums[s] == 0);
        if !sums_all_zero {
            return false;
        }
        // Validate with SAT: also enforces BDKR canonical rule Tseitin chains.
        let sat = solver.solve_with_assumptions(&state.assumptions);
        if sat == Some(true) {
            let sol = extract_solution(solver, ctx);
            *found = Some(sol);
            return true;
        }
        return false;
    }

    let pos = ctx.pos_order[state.level];
    // For each of the (up to) 16 placements at this position, enumerate
    // bit choices for X, Y, Z, W. Skip bits for sequences without a
    // position here (W at pos == n-1).
    let has_w = pos < ctx.m;

    // Build child candidates with their scores.
    struct Cand { assum: Vec<i32>, placed_signs: [(u8, usize, i8); 4], num_placed: u8, score: i64, rule_state: u8 }
    let mut candidates: Vec<Cand> = Vec::with_capacity(16);

    for choice in 0u8..16 {
        if !has_w && (choice & 1) != 0 { continue; }  // W bit must be 0 (ignored)
        let bx = if (choice >> 3) & 1 == 0 { 1i8 } else { -1 };
        let by = if (choice >> 2) & 1 == 0 { 1i8 } else { -1 };
        let bz = if (choice >> 1) & 1 == 0 { 1i8 } else { -1 };
        let bw = if choice & 1 == 0 { 1i8 } else { -1 };

        let mut placed = [(0u8, 0usize, 0i8); 4];
        let mut np: u8 = 0;
        let mut consistent = true;
        let mut new_assums: Vec<i32> = Vec::with_capacity(4);

        for (kind, sign) in [(0u8, bx), (1, by), (2, bz), (3, bw)] {
            let xy_len = kind_xy_len(kind, ctx.n, ctx.m);
            if pos >= xy_len { continue; }
            let existing = state.bit(kind, pos);
            if existing != 0 {
                let existing_sign = if existing == 1 { 1i8 } else { -1 };
                if existing_sign != sign { consistent = false; break; }
                // Already forced; don't add to assumptions.
                continue;
            }
            placed[np as usize] = (kind, pos, sign);
            np += 1;
            let var = var_for(kind, pos, ctx.n);
            new_assums.push(if sign > 0 { var } else { -var });
        }
        if !consistent { continue; }

        // Speculatively update sums for pairs closing at this level
        // using the placed bits. We don't call the solver yet — capacity
        // check first (cheap).
        let saved_bits: Vec<(u8, usize, u8)> = (0..np as usize)
            .map(|k| {
                let (ki, pi, _) = placed[k];
                (ki, pi, state.bit(ki, pi))
            })
            .collect();
        for k in 0..np as usize {
            let (ki, pi, si) = placed[k];
            state.set_bit(ki, pi, si);
        }
        let saved_level = state.level;
        state.level += 1;
        rebuild_sums(state, ctx);
        let violated = capacity_violated(state, ctx);
        // Walker-side BDKR rule check: prune rule-violating placements
        // before calling the SAT solver. Saves a propagate_only per
        // rejected candidate and keeps CDCL from learning clauses about
        // non-canonical-but-otherwise-feasible branches.
        let rule_check = if !violated {
            check_rules(state, ctx, state.level - 1)
        } else {
            Err(())
        };
        let score = if !violated && rule_check.is_ok() {
            score_state(state, ctx)
        } else {
            i64::MAX
        };

        // Rollback speculative state.
        state.level = saved_level;
        for (ki, pi, old_sign) in &saved_bits {
            state.bits[(*ki as usize) * ctx.n + pi] = *old_sign;
        }
        // Rebuild sums to the parent state after rollback.
        rebuild_sums(state, ctx);

        if violated {
            stats.capacity_rejects += 1;
            continue;
        }
        let new_rule_state = match rule_check {
            Ok(rs) => rs,
            Err(()) => {
                stats.rule_rejects += 1;
                continue;
            }
        };

        // Build full assumption list for this child.
        let mut full_assum = state.assumptions.clone();
        full_assum.extend_from_slice(&new_assums);
        candidates.push(Cand {
            assum: full_assum,
            placed_signs: placed,
            num_placed: np,
            score,
            rule_state: new_rule_state,
        });
    }
    stats.internal_nodes += 1;
    stats.children_total += candidates.len() as u64;

    // Score-ordered siblings: ascending score (low pressure first).
    // Sibling ordering: worker 0 (seed=0) walks best-first by ascending
    // score; workers 1.. shuffle by an LCG keyed on (worker seed, walker
    // prefix) so each explores an independent region of the tree.
    if ctx.seed == 0 {
        candidates.sort_by_key(|c| c.score);
    } else {
        use std::hash::Hasher;
        let mut h = rustc_hash::FxHasher::default();
        h.write_u64(ctx.seed);
        for &lit in &state.assumptions { h.write_i32(lit); }
        let s = h.finish();
        let mut rng = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        for i in (1..candidates.len()).rev() {
            rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let j = (rng >> 32) as usize % (i + 1);
            candidates.swap(i, j);
        }
    }

    // Snapshot the ENTIRE state.bits vector before trying candidates.
    // harvest_forced during a candidate's SAT call may write bits far
    // beyond the walker's placed position (rule propagation reaches into
    // the middle). Those writes MUST be rolled back before the next
    // sibling tries its SAT call, otherwise siblings see stale forced
    // bits from the previous candidate's SAT state.
    let saved_all_bits = state.bits.clone();
    let saved_sums = state.sums.clone();
    let saved_assum_len = state.assumptions.len();
    let saved_rule_state = state.rule_state;

    for cand in candidates {
        if found.is_some() { return true; }
        if let Some(d) = deadline {
            if Instant::now() >= d { return false; }
        }

        // Restore state.bits to the parent snapshot before each sibling.
        state.bits.copy_from_slice(&saved_all_bits);
        state.sums.copy_from_slice(&saved_sums);
        state.assumptions.truncate(saved_assum_len);
        state.rule_state = saved_rule_state;

        for k in 0..cand.num_placed as usize {
            let (ki, pi, si) = cand.placed_signs[k];
            state.set_bit(ki, pi, si);
        }
        state.assumptions = cand.assum.clone();
        state.level += 1;
        state.rule_state = cand.rule_state;
        rebuild_sums(state, ctx);

        // Memo check on the post-placement (pre-SAT) state.
        let sig = compute_signature(state, ctx);
        let memo_hit = memo.contains_key(&sig);
        if memo_hit {
            stats.memo_hits += 1;
        } else {
            // Per-level SAT call: propagate_only (no CDCL decisions,
            // so cost is proportional to new propagation work). On
            // UNSAT the solver installs a full-assumption nogood that
            // short-circuits future calls with the same prefix.
            let sat = solver.propagate_only(&state.assumptions);
            if sat == Some(true) {
                harvest_forced(solver, state, ctx);
                rebuild_sums(state, ctx);
                if !capacity_violated(state, ctx) {
                    memo.insert(sig, ());
                    if dfs(solver, state, ctx, memo, stats, deadline, found) {
                        return true;
                    }
                }
            } else {
                stats.sat_unsat += 1;
            }
            memo.entry(sig).or_insert(());
        }

        // Rollback level only; state.bits, sums, assumptions get
        // fully restored at the top of the next iteration (or the
        // caller's rollback if no next iteration).
        state.level -= 1;
    }

    // Final rollback to leave state as caller expected.
    state.bits.copy_from_slice(&saved_all_bits);
    state.sums.copy_from_slice(&saved_sums);
    state.assumptions.truncate(saved_assum_len);
    state.rule_state = saved_rule_state;

    false
}

fn extract_solution(
    solver: &radical::Solver,
    ctx: &Ctx,
) -> (PackedSeq, PackedSeq, PackedSeq, PackedSeq) {
    let n = ctx.n;
    let m = ctx.m;
    let mut x_vals = vec![0i8; n];
    let mut y_vals = vec![0i8; n];
    let mut z_vals = vec![0i8; n];
    let mut w_vals = vec![0i8; m];
    for i in 0..n {
        x_vals[i] = if solver.value((i + 1) as i32).unwrap_or(true) { 1 } else { -1 };
        y_vals[i] = if solver.value((n + i + 1) as i32).unwrap_or(true) { 1 } else { -1 };
        z_vals[i] = if solver.value((2 * n + i + 1) as i32).unwrap_or(true) { 1 } else { -1 };
    }
    for i in 0..m {
        w_vals[i] = if solver.value((3 * n + i + 1) as i32).unwrap_or(true) { 1 } else { -1 };
    }
    (
        PackedSeq::from_values(&x_vals),
        PackedSeq::from_values(&y_vals),
        PackedSeq::from_values(&z_vals),
        PackedSeq::from_values(&w_vals),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn propagate_only_accepts_canonical_tt6() {
        let problem = Problem::new(6);
        let sat_cfg = radical::SolverConfig::default();
        let mut solver = build_solver(problem, &sat_cfg);
        // Initial propagate (drain level-0 unit clauses).
        assert_eq!(solver.propagate_only(&[]), Some(true), "base UNSAT");
        // Canonical TT(6): X=+++--+, Y=+-++-+, Z=+-+++-, W=++++-.
        let x = [1, 1, 1, -1, -1, 1i8];
        let y = [1, -1, 1, 1, -1, 1];
        let z = [1, -1, 1, 1, 1, -1];
        let w = [1, 1, 1, 1, -1];
        let n = 6;
        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };
        let z_var = |i: usize| -> i32 { (2 * n + i + 1) as i32 };
        let w_var = |i: usize| -> i32 { (3 * n + i + 1) as i32 };
        let mut assums: Vec<i32> = Vec::new();
        for (i, &v) in x.iter().enumerate() { assums.push(if v > 0 { x_var(i) } else { -x_var(i) }); }
        for (i, &v) in y.iter().enumerate() { assums.push(if v > 0 { y_var(i) } else { -y_var(i) }); }
        for (i, &v) in z.iter().enumerate() { assums.push(if v > 0 { z_var(i) } else { -z_var(i) }); }
        for (i, &v) in w.iter().enumerate() { assums.push(if v > 0 { w_var(i) } else { -w_var(i) }); }
        let result = solver.propagate_only(&assums);
        assert_eq!(result, Some(true), "canonical TT(6) rejected by propagate_only");
    }

    #[test]
    fn propagate_only_rejects_boundary_prefix() {
        let problem = Problem::new(6);
        let sat_cfg = radical::SolverConfig::default();
        let mut solver = build_solver(problem, &sat_cfg);
        assert_eq!(solver.propagate_only(&[]), Some(true));
        // Just the first two position placements of the canonical solution.
        // Should still be satisfiable (many completions exist).
        let x0 = 1; let y0 = 7; let z0 = 13; let w0 = 19; // vars for position 0
        let x5 = 6; let y5 = 12; let z5 = 18; // vars for position 5 (no W[5])
        let assums = vec![x0, y0, z0, w0, x5, y5, -z5]; // Z[5]=-1, others +1
        let result = solver.propagate_only(&assums);
        assert_eq!(result, Some(true), "partial boundary rejected");
    }

    #[test]
    fn propagate_only_matches_solve_with_assumptions_on_tt8_prefix() {
        // Walker-like prefix of canonical TT(8): X=++-++-++, Y=+------+,
        // Z=+--++++-, W=+++-++- (from known_solutions.txt).
        let problem = Problem::new(8);
        let n = 8;
        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };
        let z_var = |i: usize| -> i32 { (2 * n + i + 1) as i32 };
        let w_var = |i: usize| -> i32 { (3 * n + i + 1) as i32 };

        // known_solutions.txt: 8 ++-++-++ ++-+-+-+ ++++-+-- +++--++
        let x: [i8; 8] = [1, 1, -1, 1, 1, -1, 1, 1];
        let y: [i8; 8] = [1, 1, -1, 1, -1, 1, -1, 1];
        let z: [i8; 8] = [1, 1, 1, 1, -1, 1, -1, -1];
        let w: [i8; 7] = [1, 1, 1, -1, -1, 1, 1];

        // Pin each bouncing-order prefix length and check consistency.
        for prefix_len in 0..=n {
            let mut assums: Vec<i32> = Vec::new();
            for level in 0..prefix_len {
                let pos = if level % 2 == 0 { level / 2 } else { n - 1 - level / 2 };
                assums.push(if x[pos] > 0 { x_var(pos) } else { -x_var(pos) });
                assums.push(if y[pos] > 0 { y_var(pos) } else { -y_var(pos) });
                assums.push(if z[pos] > 0 { z_var(pos) } else { -z_var(pos) });
                if pos < 7 {
                    assums.push(if w[pos] > 0 { w_var(pos) } else { -w_var(pos) });
                }
            }
            let sat_cfg = radical::SolverConfig::default();
            let mut prop_solver = build_solver(problem, &sat_cfg);
            assert_eq!(prop_solver.propagate_only(&[]), Some(true));
            let prop_result = prop_solver.propagate_only(&assums);
            let mut full_solver = build_solver(problem, &sat_cfg);
            let full_result = full_solver.solve_with_assumptions(&assums);
            if prop_result != Some(true) && full_result == Some(true) {
                panic!("prefix_len={}: propagate_only={:?} but full SAT says {:?} — propagate_only rejected a valid partial!",
                    prefix_len, prop_result, full_result);
            }
        }
    }

    #[test]
    fn canonical_tt18_bouncing_prefixes_all_accepted() {
        // For every bouncing-order prefix length of canonical TT(18),
        // check that propagate_only accepts the prefix. If any level
        // rejects, the walker can never reach the canonical leaf.
        let n: usize = 18;
        let m = n - 1;
        let problem = Problem::new(n);
        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };
        let z_var = |i: usize| -> i32 { (2 * n + i + 1) as i32 };
        let w_var = |i: usize| -> i32 { (3 * n + i + 1) as i32 };
        let parse = |s: &str| -> Vec<i8> { s.chars().map(|c| if c == '+' { 1i8 } else { -1 }).collect() };
        let x = parse("++-+++++++++-+--++");
        let y = parse("++----++-+---+-+-+");
        let z = parse("++-+++----+-+-++--");
        let w = parse("++----+--+--+++-+");

        // Bouncing order
        let mut pos_order = Vec::with_capacity(n);
        for j in 0..n/2 { pos_order.push(j); pos_order.push(n - 1 - j); }

        for prefix_len in 0..=pos_order.len() {
            let sat_cfg = radical::SolverConfig::default();
            let mut solver = build_solver(problem, &sat_cfg);
            assert_eq!(solver.propagate_only(&[]), Some(true));

            let mut assums: Vec<i32> = Vec::new();
            for &pos in &pos_order[..prefix_len] {
                assums.push(if x[pos] > 0 { x_var(pos) } else { -x_var(pos) });
                assums.push(if y[pos] > 0 { y_var(pos) } else { -y_var(pos) });
                assums.push(if z[pos] > 0 { z_var(pos) } else { -z_var(pos) });
                if pos < m { assums.push(if w[pos] > 0 { w_var(pos) } else { -w_var(pos) }); }
            }
            let result = solver.propagate_only(&assums);
            assert_eq!(result, Some(true),
                "canonical TT(18) rejected at walker prefix_len={}", prefix_len);
        }
    }

    #[test]
    fn canonical_tt18_propagate_only() {
        // known_solutions.txt: 18 ++-+++++++++-+--++ ++----++-+---+-+-+ ++-+++----+-+-++-- ++----+--+--+++-+
        let problem = Problem::new(18);
        let n = 18;
        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };
        let z_var = |i: usize| -> i32 { (2 * n + i + 1) as i32 };
        let w_var = |i: usize| -> i32 { (3 * n + i + 1) as i32 };

        let parse = |s: &str| -> Vec<i8> { s.chars().map(|c| if c == '+' { 1i8 } else { -1 }).collect() };
        let x = parse("++-+++++++++-+--++");
        let y = parse("++----++-+---+-+-+");
        let z = parse("++-+++----+-+-++--");
        let w = parse("++----+--+--+++-+");

        let sat_cfg = radical::SolverConfig::default();
        let mut solver = build_solver(problem, &sat_cfg);
        solver.propagate_only(&[]);
        let mut assums: Vec<i32> = Vec::new();
        for (i, &v) in x.iter().enumerate() { assums.push(if v > 0 { x_var(i) } else { -x_var(i) }); }
        for (i, &v) in y.iter().enumerate() { assums.push(if v > 0 { y_var(i) } else { -y_var(i) }); }
        for (i, &v) in z.iter().enumerate() { assums.push(if v > 0 { z_var(i) } else { -z_var(i) }); }
        for (i, &v) in w.iter().enumerate() { assums.push(if v > 0 { w_var(i) } else { -w_var(i) }); }
        let result = solver.propagate_only(&assums);
        assert_eq!(result, Some(true), "canonical TT(18) rejected by propagate_only");
    }
}
