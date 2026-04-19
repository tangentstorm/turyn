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

use crate::types::{PackedSeq, Problem, SumTuple};
use crate::enumerate::enumerate_sum_tuples;
use crate::legacy_search::{SearchReport, SearchStats};

/// Shared clause exchange between parallel workers.  Each worker
/// appends its newly-learnt nogood and periodically pulls unread
/// peers' clauses into its own solver.  `seq` is monotonically
/// increasing; a worker's local `read_idx` tracks the next
/// unread index.
pub(crate) struct ClauseExchange {
    pub clauses: std::sync::Mutex<Vec<Vec<i32>>>,
}

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
    /// Shared learnt-clause exchange. `None` for single-worker mode.
    pub exchange: Option<Arc<ClauseExchange>>,
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
    /// Sorted by `kind` ascending so per-kind ranges are contiguous; see
    /// `closure_events_kind_ranges`.
    closure_events: Vec<Vec<PairEvent>>,
    /// Per-(level, kind) [start, end) range into `closure_events[level]`.
    /// Used by `apply_sum_delta_at` to skip kinds not in `newly_placed`
    /// without per-event branching.
    closure_events_kind_ranges: Vec<[(u32, u32); 4]>,
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
    /// All signed (σ_X, σ_Y, σ_Z, σ_W) tuples satisfying the Turyn
    /// energy identity σ²_X + σ²_Y + 2σ²_Z + 2σ²_W = 6n-2 with parity
    /// constraints.  Used by the walker's `tuple_reachable` check to
    /// prune branches where no valid final sum tuple is reachable from
    /// the current partial sums + remaining free-bit budgets.
    valid_tuples: Vec<SumTuple>,
    /// Cross-worker clause exchange (shared across all parallel
    /// workers).  Each worker publishes newly-learnt nogoods on
    /// propagate_only UNSAT and pulls peer clauses periodically.
    exchange: Option<Arc<ClauseExchange>>,
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
    /// Solver trail size at decision level 0 (after the initial
    /// `propagate_only(&[])` has drained unit clauses + Tseitin chains).
    /// Used to compute "forced by propagation above what we assumed":
    /// `forced = solver.num_assigned() - trail0_size - assumptions.len()`.
    trail0_size: usize,
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
            trail0_size: 0,
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

fn build_ctx_seeded(
    problem: Problem,
    seed: u64,
    cancel: Option<Arc<AtomicBool>>,
    exchange: Option<Arc<ClauseExchange>>,
    start: Instant,
) -> Ctx {
    let mut ctx = build_ctx(problem);
    ctx.seed = seed;
    ctx.cancel = cancel;
    ctx.exchange = exchange;
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

    // Precompute all signed sum tuples. Phase-A-style:
    //   σ²_X + σ²_Y + 2σ²_Z + 2σ²_W = 6n - 2, with the parity required
    // for length-n ±1 sequences (σ ≡ n mod 2).  The walker's
    // `tuple_reachable` check uses this at every level for early
    // hopelessness detection.
    let valid_tuples = enumerate_sum_tuples(problem);

    // Sort each level's events by kind ascending and record per-kind
    // ranges so `apply_sum_delta_at` can skip whole kind blocks when
    // `newly_placed[k]` is false.
    for events in closure_events.iter_mut() {
        events.sort_by_key(|e| e.kind);
    }
    let mut closure_events_kind_ranges: Vec<[(u32, u32); 4]> =
        Vec::with_capacity(depth);
    for events in &closure_events {
        let mut ranges = [(0u32, 0u32); 4];
        let mut start = 0usize;
        let len = events.len();
        for k in 0u8..4 {
            // Find end of contiguous run of events with this kind.
            let mut end = start;
            while end < len && events[end].kind == k {
                end += 1;
            }
            ranges[k as usize] = (start as u32, end as u32);
            start = end;
        }
        closure_events_kind_ranges.push(ranges);
    }

    Ctx {
        n, m, depth,
        pos_order, pos_to_level,
        closure_events, closure_events_kind_ranges, max_remaining,
        seed: 0, cancel: None, start: Instant::now(),
        valid_tuples,
        exchange: None,
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
    // R2: sync's propagate_only-dominated workload benefits from the
    // dedicated binary-watch fast path (−6.8 % TTC measured on n=26).
    // Apart/together regress ~8 % because they clone the template
    // solver per candidate and GJ-equality binaries cross the
    // bin/general watch split, so we opt in from sync specifically
    // rather than flipping the default.
    solver.config.bin_watch_fastpath = true;

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

    // Phase-A sum constraints: each sequence's sum must land in the
    // set of valid σ values from enumerate_sum_tuples.  PbSetEq is
    // exact: Σ x_var[i] ∈ V where V = {(σ + len) / 2 : σ is a valid
    // sum for this sequence}.  Makes the solver aware of the global
    // σ-budget, fills in where walker-side tuple_reachable can't
    // reach (deep inside propagate_only when partial sums tighten
    // after harvest_forced).
    let tuples = enumerate_sum_tuples(problem);
    let sum_set = |seq_len: usize, pick: fn(&SumTuple) -> i32| -> Vec<u32> {
        let mut vs: Vec<u32> = tuples.iter()
            .filter_map(|t| {
                let s = pick(t);
                let count_plus = s + seq_len as i32;
                if count_plus < 0 || count_plus > 2 * seq_len as i32 || count_plus & 1 != 0 {
                    None
                } else {
                    Some((count_plus / 2) as u32)
                }
            })
            .collect();
        vs.sort_unstable();
        vs.dedup();
        vs
    };
    let x_lits: Vec<i32> = (0..n).map(x_var).collect();
    let y_lits: Vec<i32> = (0..n).map(y_var).collect();
    let z_lits: Vec<i32> = (0..n).map(z_var).collect();
    let w_lits: Vec<i32> = (0..m).map(w_var).collect();
    let x_vals = sum_set(n, |t| t.x);
    let y_vals = sum_set(n, |t| t.y);
    let z_vals = sum_set(n, |t| t.z);
    let w_vals = sum_set(m, |t| t.w);
    if !x_vals.is_empty() { solver.add_pb_set_eq(&x_lits, &x_vals); }
    if !y_vals.is_empty() { solver.add_pb_set_eq(&y_lits, &y_vals); }
    if !z_vals.is_empty() { solver.add_pb_set_eq(&z_lits, &z_vals); }
    if !w_vals.is_empty() { solver.add_pb_set_eq(&w_lits, &w_vals); }

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

    // SCC equivalence preprocessing on the binary implication graph.
    // Strongly-connected components in the implication graph are
    // logically-equivalent literals; substituting them out shrinks
    // the formula. radical exposes this but neither sync nor any
    // other entry point currently calls it.
    let _scc_eliminated = solver.preprocess_scc_equivalences();

    // BVE preprocessing — eliminate Tseitin aux vars where possible,
    // but protect walker vars (1..=4n) since they're used as
    // assumption literals in push_assume_frame.
    let protected: Vec<usize> = (0..4 * n).collect();  // 0-based var idx
    let _bve_eliminated = solver.preprocess_bve_with_protection(&protected);

    // Compact the clause arena after preprocessing. BVE / SCC leave
    // holes in `clause_lits` + `clause_meta` as clauses get marked
    // deleted; compaction physically removes them and shrinks the
    // per-literal watch lists. One-time cost; frees memory in the
    // template solver that would otherwise be re-cloned per worker.
    // Typical reduction on n=26: ~53 clauses freed of ~290 (18 %).
    let _compacted = solver.compact_arena();

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
/// Pull SAT-forced walker-var values from the solver into `state.bits`.
/// Returns the number of bits newly set (caller can use this to skip
/// `rebuild_sums` when zero — state.sums remains consistent in that
/// case).
fn harvest_forced(solver: &radical::Solver, state: &mut State, ctx: &Ctx) -> usize {
    let mut newly_set = 0usize;
    for kind in 0u8..4 {
        let xy_len = kind_xy_len(kind, ctx.n, ctx.m);
        for pos in 0..xy_len {
            if state.bit(kind, pos) != 0 { continue; }
            let var = var_for(kind, pos, ctx.n);
            if let Some(b) = solver.value(var) {
                state.set_bit(kind, pos, if b { 1 } else { -1 });
                newly_set += 1;
            }
        }
    }
    newly_set
}

/// Apply ONLY the per-lag sum delta contributed by pairs closing at
/// `level` whose kind is in `newly_placed`. Assumes `state.sums`
/// already reflects contributions for closure_events[`level`] events
/// whose kind was NOT newly placed at this iteration (those were
/// already counted in the parent rebuild, e.g. if harvest_forced set
/// the bit before this level). O(|closure_events[level]|) —
/// avoids the full O(total events) rebuild per candidate.
///
/// Soundness invariant (debug_assert'd): when `newly_placed[kind]` is
/// true, every event in `closure_events[level]` of that kind has both
/// endpoints set in `state.bits`. The "max-level" endpoint is
/// `pos_order[level]` (just placed by us), and the "earlier" endpoint
/// is at some level < `level` (placed by an ancestor or harvested).
fn apply_sum_delta_at(
    state: &mut State,
    ctx: &Ctx,
    level: usize,
    newly_placed: &[bool; 4],
) {
    if level >= ctx.depth { return; }
    let events = &ctx.closure_events[level];
    let ranges = &ctx.closure_events_kind_ranges[level];
    for k in 0u8..4 {
        if !newly_placed[k as usize] { continue; }
        let (start, end) = ranges[k as usize];
        // Slice over the contiguous run for this kind.
        for ev in &events[start as usize .. end as usize] {
            let a_sign = state.bit(ev.kind, ev.pos_a);
            let b_sign = state.bit(ev.kind, ev.pos_b);
            debug_assert!(
                a_sign != 0 && b_sign != 0,
                "apply_sum_delta_at: unset endpoint at level={} kind={} pos_a={} pos_b={}",
                level, ev.kind, ev.pos_a, ev.pos_b,
            );
            let a = if a_sign == 1 { 1i16 } else { -1 };
            let b = if b_sign == 1 { 1i16 } else { -1 };
            state.sums[ev.lag] += (a * b) * ev.abs_coeff;
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

/// Compute `(σ_X, σ_Y, σ_Z, σ_W, free_X, free_Y, free_Z, free_W)` from
/// current `state.bits`.  σ = Σ of placed ±1 values per sequence;
/// free = count of still-unplaced positions per sequence.
fn compute_sigma(state: &State, ctx: &Ctx) -> (i32, i32, i32, i32, usize, usize, usize, usize) {
    let mut sigma = [0i32; 4];
    let mut free = [ctx.n, ctx.n, ctx.n, ctx.m];
    for kind in 0u8..4 {
        let xy_len = kind_xy_len(kind, ctx.n, ctx.m);
        for pos in 0..xy_len {
            match state.bit(kind, pos) {
                1 => { sigma[kind as usize] += 1; free[kind as usize] -= 1; }
                2 => { sigma[kind as usize] -= 1; free[kind as usize] -= 1; }
                _ => {}
            }
        }
    }
    (sigma[0], sigma[1], sigma[2], sigma[3], free[0], free[1], free[2], free[3])
}

/// Can any valid Phase-A tuple be reached from the current partial sums?
/// Returns `true` if at least one tuple is reachable; `false` means
/// the prefix is hopeless and can be pruned without any further search.
///
/// Reachability per sequence: `|target - σ| ≤ free` (budget) and
/// `(target - σ) ≡ free (mod 2)` (each remaining ±1 flips σ by 2).
fn tuple_reachable(state: &State, ctx: &Ctx) -> bool {
    let (sx, sy, sz, sw, fx, fy, fz, fw) = compute_sigma(state, ctx);
    tuple_reachable_args(ctx, sx, sy, sz, sw, fx, fy, fz, fw)
}

/// Same as `tuple_reachable` but takes pre-computed sigma/free directly.
/// Used by the candidate-building speculative loop to avoid the
/// O(4n) `compute_sigma` scan per choice (S6 — caller maintains
/// parent sigma + applies a 4-element delta).
#[inline]
fn tuple_reachable_args(
    ctx: &Ctx,
    sx: i32, sy: i32, sz: i32, sw: i32,
    fx: usize, fy: usize, fz: usize, fw: usize,
) -> bool {
    let dx_max = fx as i32; let px = fx & 1;
    let dy_max = fy as i32; let py = fy & 1;
    let dz_max = fz as i32; let pz = fz & 1;
    let dw_max = fw as i32; let pw = fw & 1;
    for t in &ctx.valid_tuples {
        let dx = (t.x - sx).abs();
        let dy = (t.y - sy).abs();
        let dz = (t.z - sz).abs();
        let dw = (t.w - sw).abs();
        if dx > dx_max || dy > dy_max || dz > dz_max || dw > dw_max { continue; }
        if (dx as usize & 1) != px { continue; }
        if (dy as usize & 1) != py { continue; }
        if (dz as usize & 1) != pz { continue; }
        if (dw as usize & 1) != pw { continue; }
        return true;
    }
    false
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

#[derive(Clone)]
pub(crate) struct SyncStats {
    pub nodes_visited: u64,
    pub memo_hits: u64,
    pub capacity_rejects: u64,
    pub rule_rejects: u64,
    pub tuple_rejects: u64,
    pub sat_unsat: u64,
    pub leaves_reached: u64,
    pub learned_clauses_final: u64,
    pub max_level_reached: u64,
    pub nodes_by_level: Vec<u64>,
    /// Per-level sum of `candidates.len()` — i.e. the children that
    /// survived cap/tuple/rule pruning at that level and became
    /// candidates for SAT / descent. `children_by_level[L] /
    /// nodes_by_level[L]` is the true per-level branching factor
    /// (independent of DFS partial-run bias that contaminates the
    /// ratio `nodes_by_level[L+1] / nodes_by_level[L]`).
    pub children_by_level: Vec<u64>,
    pub children_total: u64,
    pub internal_nodes: u64,
    pub time_to_first_leaf: Option<f64>,
    /// Sum of nogood clause lengths learnt from conflict analysis.
    /// `nogood_len_sum / sat_unsat` = avg learnt clause size.
    pub nogood_len_sum: u64,
    /// Sum of "full assumption length at conflict time" — the size
    /// the nogood WOULD be if we just negated every assumption.
    /// `full_nogood_len_sum / sat_unsat` = avg full-nogood size;
    /// the ratio `nogood_len_sum / full_nogood_len_sum` shows how
    /// effective 1-UIP analysis is at shrinking.
    pub full_nogood_len_sum: u64,
    /// Worker's local index into the shared clause exchange; count of
    /// peer clauses it has already imported.
    pub peer_clauses_read: u64,
    /// Count of peer clauses this worker has added to its own solver.
    pub peer_clauses_imported: u64,
    /// Per-level sum of "vars the SAT solver forced via propagation
    /// beyond the walker's own assumption at this level". Each forced
    /// var trims 2^1 from the subtree that the walker would otherwise
    /// have had to explore; k forced vars at this level mean the
    /// walker got a "free" 2^k prune of the sub-cube below.
    /// `forced_by_level[L]` accumulates over every propagate_only call
    /// made while the walker was at level L (across every sub-cube
    /// traversed). `sum(forced_by_level) / sat_unsat` ≈ avg forced per
    /// call; `2^forced_by_level[L]` estimates total subtree nodes
    /// pruned at that level.
    pub forced_by_level: Vec<u64>,
    /// Per-level wall-clock time (seconds) accumulated across all dfs()
    /// calls at that level — i.e. "how long did the walker spend
    /// traversing sub-cubes rooted at depth L, including descendants".
    /// Divided by `nodes_by_level[L]` gives avg sub-cube time at depth L,
    /// which — combined with `forced_by_level[L]` — tells us the
    /// marginal cost/benefit of each decision at that depth.
    pub sub_cube_time_by_level: Vec<f64>,
    /// Per-level sum of `candidates_processed`: how many of each frame's
    /// generated candidates (up to `candidates.len()`) actually went
    /// through the propagate_only call before the frame returned.
    /// Equals `children_by_level[L]` if every frame at L fully iterated
    /// its sibling list; less if some frames bailed early (deadline hit,
    /// solution found, or cancel signal). The ratio
    /// `children_processed_by_level[L] / children_by_level[L]` is the
    /// work-weighted "coverage fraction" at level L — a direct measure
    /// of how much of each sub-cube we actually did. The PRODUCT of
    /// coverages down the tree (starting from level 0) = fraction of
    /// the total root sub-cube covered so far, which gives a direct
    /// TTC formula: `TTC = elapsed / root_coverage_product`.
    pub children_processed_by_level: Vec<u64>,
    /// Per-propagator forced-variable totals (sum of deltas over every
    /// `propagate_only` call). Indexed by `radical::PropKind as usize`.
    /// Tells you which feature of the SAT solver did the most work:
    /// `clause` (CNF BCP) / `pb` / `quadpb` (Turyn identity) / `xor`
    /// (Tseitin chains) / `spect` (spectral DFT) / `mdd` / `pbseteq`.
    pub prop_by_kind_total: [u64; radical::PropKind::COUNT],
    /// Per-(walker level, propagator) forcing counts. `[L][k]` = total
    /// variables forced by propagator `k` across every `propagate_only`
    /// call made while the walker was at level L. Reveals *where* in the
    /// walker's DFS each SAT feature is doing work (e.g. is quadpb hot
    /// near the root while clause BCP dominates near the leaves?).
    pub forced_by_level_kind: Vec<[u64; radical::PropKind::COUNT]>,
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
        rule_rejects: 0, tuple_rejects: 0, sat_unsat: 0, leaves_reached: 0,
        learned_clauses_final: 0, max_level_reached: 0,
        nodes_by_level: Vec::new(), children_by_level: Vec::new(),
        children_total: 0, internal_nodes: 0,
        time_to_first_leaf: None,
        nogood_len_sum: 0, full_nogood_len_sum: 0,
        peer_clauses_read: 0, peer_clauses_imported: 0,
        forced_by_level: Vec::new(),
        sub_cube_time_by_level: Vec::new(),
        children_processed_by_level: Vec::new(),
        prop_by_kind_total: [0; radical::PropKind::COUNT],
        forced_by_level_kind: Vec::new(),
    }));
    let exchange = Arc::new(ClauseExchange {
        clauses: std::sync::Mutex::new(Vec::new()),
    });

    thread::scope(|s| {
        for worker_id in 0..n_workers {
            let cfg = cfg.clone();
            let cancel = Arc::clone(&cancel);
            let result = Arc::clone(&result);
            let stats_agg = Arc::clone(&stats_agg);
            let exchange = Arc::clone(&exchange);
            s.spawn(move || {
                // Worker 0: seed=0 → score-sorted best-first siblings.
                // Worker k>0: seed=k → randomised ordering distinct
                // from every other worker.
                let worker_cfg = SyncConfig {
                    random_seed: Some(worker_id as u64),
                    cancel: Some(Arc::clone(&cancel)),
                    exchange: Some(Arc::clone(&exchange)),
                    ..cfg
                };
                let (sol, stats, _) = search_sync_serial(problem, &worker_cfg, false, start);
                let mut agg = stats_agg.lock().unwrap();
                agg.nodes_visited += stats.nodes_visited;
                agg.memo_hits += stats.memo_hits;
                agg.capacity_rejects += stats.capacity_rejects;
                agg.rule_rejects += stats.rule_rejects;
                agg.tuple_rejects += stats.tuple_rejects;
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
                agg.nogood_len_sum += stats.nogood_len_sum;
                agg.full_nogood_len_sum += stats.full_nogood_len_sum;
                agg.peer_clauses_imported += stats.peer_clauses_imported;
                agg.internal_nodes += stats.internal_nodes;
                if agg.nodes_by_level.len() < stats.nodes_by_level.len() {
                    agg.nodes_by_level.resize(stats.nodes_by_level.len(), 0);
                }
                for (i, &c) in stats.nodes_by_level.iter().enumerate() {
                    agg.nodes_by_level[i] += c;
                }
                if agg.children_by_level.len() < stats.children_by_level.len() {
                    agg.children_by_level.resize(stats.children_by_level.len(), 0);
                }
                for (i, &c) in stats.children_by_level.iter().enumerate() {
                    agg.children_by_level[i] += c;
                }
                if agg.forced_by_level.len() < stats.forced_by_level.len() {
                    agg.forced_by_level.resize(stats.forced_by_level.len(), 0);
                }
                for (i, &c) in stats.forced_by_level.iter().enumerate() {
                    agg.forced_by_level[i] += c;
                }
                if agg.sub_cube_time_by_level.len() < stats.sub_cube_time_by_level.len() {
                    agg.sub_cube_time_by_level.resize(stats.sub_cube_time_by_level.len(), 0.0);
                }
                for (i, &t) in stats.sub_cube_time_by_level.iter().enumerate() {
                    agg.sub_cube_time_by_level[i] += t;
                }
                if agg.children_processed_by_level.len() < stats.children_processed_by_level.len() {
                    agg.children_processed_by_level.resize(stats.children_processed_by_level.len(), 0);
                }
                for (i, &c) in stats.children_processed_by_level.iter().enumerate() {
                    agg.children_processed_by_level[i] += c;
                }
                for (i, &c) in stats.prop_by_kind_total.iter().enumerate() {
                    agg.prop_by_kind_total[i] += c;
                }
                if agg.forced_by_level_kind.len() < stats.forced_by_level_kind.len() {
                    agg.forced_by_level_kind.resize(
                        stats.forced_by_level_kind.len(),
                        [0; radical::PropKind::COUNT],
                    );
                }
                for (l, row) in stats.forced_by_level_kind.iter().enumerate() {
                    for (k, &c) in row.iter().enumerate() {
                        agg.forced_by_level_kind[l][k] += c;
                    }
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
            "sync_walker(parallel x{}): nodes={} cap_rejects={} tuple_rejects={} rule_rejects={} sat_unsat={} leaves={} max_lvl={} elapsed={:?} time_to_first_leaf={} avg_nogood={:.1}/{:.1} ({:.2}x shrink) peer_imports={}",
            n_workers, stats.nodes_visited, stats.capacity_rejects, stats.tuple_rejects, stats.rule_rejects, stats.sat_unsat, stats.leaves_reached, stats.max_level_reached, elapsed,
            stats.time_to_first_leaf.map(|t| format!("{:.3}s", t)).unwrap_or_else(|| "(never)".into()),
            if stats.sat_unsat > 0 { stats.nogood_len_sum as f64 / stats.sat_unsat as f64 } else { 0.0 },
            if stats.sat_unsat > 0 { stats.full_nogood_len_sum as f64 / stats.sat_unsat as f64 } else { 0.0 },
            if stats.nogood_len_sum > 0 { stats.full_nogood_len_sum as f64 / stats.nogood_len_sum as f64 } else { 1.0 },
            stats.peer_clauses_imported,
        );
        let ttc = project_ttc(&stats, problem.n, elapsed.as_secs_f64(), n_workers);
        eprintln!("{}", ttc);
        let per_level = format_per_level_telemetry_with_ttc(
            &stats,
            elapsed.as_secs_f64(),
            n_workers,
        );
        eprintln!("{}", per_level);
    }
    (found, stats, elapsed)
}

/// Per-level forced-prune and timer telemetry.
///
/// For each walker level L, reports:
/// - `nodes`: dfs visits at level L (cumulative across all workers).
/// - `forced`: walker-var forcings by SAT propagation AT THIS LEVEL
///   (incremental: new assumptions at L minus everything above L).
///   Divide by nodes to get "avg free prunes per sub-cube at level L";
///   `2^(forced/nodes)` is the multiplicative sub-cube shrink factor.
/// - `time`: cumulative wall-seconds spent in dfs frames rooted at L
///   (includes descendants). Divided by nodes gives avg sub-cube time.
/// - `implied_pruned_2^…`: log2 estimate of how many walker sub-cubes
///   at the DEEPEST level were eliminated by SAT work at level L.
fn format_per_level_telemetry_with_ttc(stats: &SyncStats, elapsed_secs: f64, n_workers: usize) -> String {
    let base = format_per_level_telemetry(stats);
    // Compute coverage product over levels with generated candidates.
    let mut coverage_product: f64 = 1.0;
    let levels = stats.nodes_by_level.len().max(stats.children_by_level.len());
    for l in 0..levels {
        let children = stats.children_by_level.get(l).copied().unwrap_or(0);
        let processed = stats.children_processed_by_level.get(l).copied().unwrap_or(0);
        if children > 0 {
            coverage_product *= processed as f64 / children as f64;
        }
    }
    let kind_summary = format_prop_by_kind_summary(stats);
    let kind_per_level = format_per_level_kind_table(stats);
    if coverage_product > 0.0 && elapsed_secs > 0.0 {
        let ttc_parallel = elapsed_secs / coverage_product;
        let ttc_serial = ttc_parallel * n_workers as f64;
        format!(
            "{}{}{}Per-level: direct TTC (from coverage product) ≈ {:.3e}s parallel, {:.3e}s serial\n",
            base, kind_summary, kind_per_level, ttc_parallel, ttc_serial,
        )
    } else {
        format!("{}{}{}", base, kind_summary, kind_per_level)
    }
}

/// Per-(walker level, propagator) table. Only shows propagator columns
/// that have at least one non-zero count across all levels (keeps the
/// table compact — in sync mode XOR/spectral/MDD are all zero).
/// Answer to "which level is quadpb hottest at, and where does clause
/// BCP take over?"
fn format_per_level_kind_table(stats: &SyncStats) -> String {
    if stats.forced_by_level_kind.is_empty() { return String::new(); }
    let active_kinds: Vec<radical::PropKind> = radical::PropKind::ALL
        .iter()
        .copied()
        .filter(|k| stats.forced_by_level_kind.iter().any(|row| row[*k as usize] > 0))
        .collect();
    if active_kinds.is_empty() { return String::new(); }
    let mut out = String::from("Per-level forcings by feature: lvl");
    for k in &active_kinds { out.push_str(&format!(" | {:>10}", k.label())); }
    out.push('\n');
    for (l, row) in stats.forced_by_level_kind.iter().enumerate() {
        let row_total: u64 = active_kinds.iter().map(|k| row[*k as usize]).sum();
        if row_total == 0 { continue; }
        out.push_str(&format!("Per-level forcings by feature: {:3}", l));
        for k in &active_kinds {
            out.push_str(&format!(" | {:>10}", row[*k as usize]));
        }
        out.push('\n');
    }
    out
}

/// One-line summary of where the SAT solver spent its propagation work,
/// broken out by propagator family. Sums to `num_propagations` (modulo
/// rounding from the per-call delta tracking). Use to identify the
/// dominant feature: e.g. "quadpb=72.3%" means the Turyn quad PB is
/// doing most of the propagation; "spect=45%" means spectral is hot.
fn format_prop_by_kind_summary(stats: &SyncStats) -> String {
    let total: u64 = stats.prop_by_kind_total.iter().sum();
    if total == 0 { return String::new(); }
    let mut parts: Vec<String> = Vec::with_capacity(radical::PropKind::COUNT);
    for kind in radical::PropKind::ALL {
        let c = stats.prop_by_kind_total[kind as usize];
        if c == 0 { continue; }
        let pct = c as f64 / total as f64 * 100.0;
        parts.push(format!("{}={} ({:.1}%)", kind.label(), c, pct));
    }
    format!("Per-feature forcings (total {}): {}\n", total, parts.join("  "))
}

fn format_per_level_telemetry(stats: &SyncStats) -> String {
    let mut out = String::from("Per-level: lvl |   nodes |  children | proc'd | cov% |   forced | f/node |   time(s) |  t/node\n");
    let levels = stats
        .nodes_by_level.len()
        .max(stats.forced_by_level.len())
        .max(stats.sub_cube_time_by_level.len());
    let mut total_forced: u64 = 0;
    let mut total_time: f64 = 0.0;
    // Cumulative "fraction of root sub-cube that has been fully
    // covered" — product of per-level coverages. For deepest levels
    // the product dominates because most work is there.
    let mut coverage_product: f64 = 1.0;
    for l in 0..levels {
        let nodes = stats.nodes_by_level.get(l).copied().unwrap_or(0);
        let children = stats.children_by_level.get(l).copied().unwrap_or(0);
        let processed = stats.children_processed_by_level.get(l).copied().unwrap_or(0);
        let forced = stats.forced_by_level.get(l).copied().unwrap_or(0);
        let tsec = stats.sub_cube_time_by_level.get(l).copied().unwrap_or(0.0);
        total_forced += forced;
        total_time += tsec;
        if nodes == 0 && forced == 0 && tsec == 0.0 { continue; }
        let fpn = if nodes > 0 { forced as f64 / nodes as f64 } else { 0.0 };
        let tpn = if nodes > 0 { tsec / nodes as f64 } else { 0.0 };
        let cov = if children > 0 { processed as f64 / children as f64 } else { 1.0 };
        if children > 0 { coverage_product *= cov; }
        out.push_str(&format!(
            "Per-level: {:>3} | {:>7} | {:>9} | {:>6} | {:>4.1} | {:>8} | {:>6.2} | {:>9.3} | {:>7.6}\n",
            l, nodes, children, processed, cov * 100.0, forced, fpn, tsec, tpn,
        ));
    }
    out.push_str(&format!(
        "Per-level: cumulative root-coverage (∏ cov) = {:.3e}  →  direct TTC = elapsed / coverage\n",
        coverage_product,
    ));
    // Cumulative (over the whole run) log2-prune budget and weighted
    // mean pruning factor. `total_forced` is Σ_calls(forced_at_call),
    // which equals Σ_calls log2(sub-cube shrink factor). Dividing by
    // sat-call count gives the geometric-mean shrink: the "typical"
    // propagate_only trims 2^avg_forced walker sub-cubes.
    let sat_calls = stats.sat_unsat + stats.nodes_visited.saturating_sub(stats.leaves_reached);
    let avg_forced_per_call = if sat_calls > 0 {
        total_forced as f64 / sat_calls as f64
    } else { 0.0 };
    // Per-level time columns are INCLUSIVE of descendants, so summing
    // across levels double-counts. We suppress the "total" to avoid
    // that confusion; the level-0 column already shows total aggregate
    // (sum of wall-time across workers).
    let _ = total_time;
    out.push_str(&format!(
        "Per-level: total walker-var forcings = {} (avg 2^{:.2} shrink per propagate call)",
        total_forced, avg_forced_per_call,
    ));
    out
}

/// Project TTC (time-to-cover) from measured per-level branching + rate.
///
/// Method: for each level L, compute the true per-parent branching
/// factor `b_eff(L) = children_by_level[L] / nodes_by_level[L]` —
/// i.e. "out of every parent visited at depth L, how many children
/// survived cap/tuple/rule pruning and became candidates for SAT /
/// descent". This ratio is INDEPENDENT of DFS completion: even if the
/// run ends after visiting only 3 parents at level L=20, each of those
/// 3 parents still gives an unbiased estimate of the true per-parent
/// branching.
///
/// Contrast with the old (buggy) estimator
///   b_eff(L) = nodes_by_level[L+1] / nodes_by_level[L]
/// which is massively downward-biased on a partial run: the DFS
/// leaves many parents at level L with their children unexplored, so
/// nodes_by_level[L+1] counts far fewer than b*nodes_by_level[L].
///
/// Full-cover tree size:
///   N_total = 1 + Σ_{L=0..depth-1} Π_{ℓ=0..L} b_eff(ℓ)
///
/// For levels with too few samples (MIN_SAMPLES) we fall back to the
/// median of the reliably-sampled levels — a conservative estimate
/// that avoids both the "exactly zero" cliff and the "one weird
/// sample" cliff.
///
/// TTC_serial  = N_total / rate,   TTC_parallel = TTC_serial / n_workers
/// where rate = nodes_visited / elapsed (aggregate across workers in
/// parallel mode, so this is already a parallel rate).
fn project_ttc(stats: &SyncStats, n: usize, elapsed_secs: f64, n_workers: usize) -> String {
    const NOISY_THRESHOLD: u64 = 32;
    let depth = n;  // bouncing-order depth = n for even n
    if elapsed_secs <= 0.0 || stats.nodes_visited == 0 {
        return "TTC projection: insufficient data".to_string();
    }
    // Per-level true branching factor. `sampled` = we have at least
    // one parent at this level, so the ratio has meaning.
    // `noisy` = sample count below NOISY_THRESHOLD, printed with `?`
    // but still USED in the projection (early levels have near-zero
    // variance because every worker sees the same root-level
    // branching — 1 sample is effectively exact there).
    struct Bee { b: f64, sampled: bool, noisy: bool }
    let mut b_eff: Vec<Bee> = Vec::with_capacity(depth);
    for l in 0..depth {
        let parent = stats.nodes_by_level.get(l).copied().unwrap_or(0);
        let child = stats.children_by_level.get(l).copied().unwrap_or(0);
        if parent == 0 {
            b_eff.push(Bee { b: 0.0, sampled: false, noisy: false });
        } else {
            b_eff.push(Bee {
                b: child as f64 / parent as f64,
                sampled: true,
                noisy: parent < NOISY_THRESHOLD,
            });
        }
    }
    // Fallback for un-SAMPLED levels (no data at all): median of
    // well-sampled levels (noisy excluded). Median resists outliers.
    let mut clean_bs: Vec<f64> =
        b_eff.iter().filter(|x| x.sampled && !x.noisy).map(|x| x.b).collect();
    clean_bs.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let fallback = if clean_bs.is_empty() {
        1.0
    } else {
        clean_bs[clean_bs.len() / 2]
    };
    let geo_mean = if clean_bs.is_empty() {
        fallback
    } else {
        let log_sum: f64 = clean_bs.iter().map(|b| b.max(1e-9).ln()).sum();
        (log_sum / clean_bs.len() as f64).exp()
    };
    // Build the full-cover projection. Use each SAMPLED level's
    // measurement as-is (noisy or not). Only fall back to median for
    // truly unsampled levels (zero parents ever visited).
    let mut projected_nodes = 1.0_f64;
    let mut running_product = 1.0_f64;
    for l in 0..depth {
        let b = match b_eff.get(l) {
            Some(Bee { b, sampled: true, .. }) => *b,
            _ => fallback,
        };
        running_product *= b;
        projected_nodes += running_product;
        if !running_product.is_finite() { break; }
    }
    let rate = stats.nodes_visited as f64 / elapsed_secs;
    let ttc_parallel = projected_nodes / rate;
    let ttc_serial = ttc_parallel * n_workers as f64;
    let unsampled = b_eff.iter().filter(|x| !x.sampled).count();
    let noisy_count = b_eff.iter().filter(|x| x.sampled && x.noisy).count();
    format!(
        "TTC projection: b_eff per level = [{}] ({} clean, {} noisy?, {} unsampled→median={:.3})\n\
         TTC projection: clean geo mean = {:.3}, projected nodes to cover = {:.3e}\n\
         TTC projection: rate = {:.0} nodes/s ({} workers, aggregate),\n\
         TTC projection: TTC_parallel ≈ {:.1}s, TTC_serial ≈ {:.1}s",
        b_eff.iter()
            .map(|x| if !x.sampled { "-".into() }
                     else if x.noisy { format!("{:.2}?", x.b) }
                     else { format!("{:.2}", x.b) })
            .collect::<Vec<_>>().join(", "),
        clean_bs.len(), noisy_count, unsampled, fallback,
        geo_mean, projected_nodes, rate, n_workers, ttc_parallel, ttc_serial,
    )
}

fn search_sync_serial(
    problem: Problem,
    cfg: &SyncConfig,
    verbose: bool,
    start: Instant,
) -> (Option<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>, SyncStats, std::time::Duration) {
    let seed = cfg.random_seed.unwrap_or(0);
    let ctx = build_ctx_seeded(problem, seed, cfg.cancel.clone(), cfg.exchange.clone(), start);
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
            rule_rejects: 0, tuple_rejects: 0, sat_unsat: 0, leaves_reached: 0, learned_clauses_final: 0, max_level_reached: 0,
            nodes_by_level: Vec::new(), children_by_level: Vec::new(),
            children_total: 0, internal_nodes: 0,
            time_to_first_leaf: None,
        nogood_len_sum: 0, full_nogood_len_sum: 0,
        peer_clauses_read: 0, peer_clauses_imported: 0,
        forced_by_level: Vec::new(),
        sub_cube_time_by_level: Vec::new(),
        children_processed_by_level: Vec::new(),
        prop_by_kind_total: [0; radical::PropKind::COUNT],
        forced_by_level_kind: Vec::new(),
        }, start.elapsed());
    }

    let mut state = State::new(ctx.n);
    // Record walker-var count at decision-level-0 (before any
    // assumptions). "Walker vars" = the 4n sign-choice vars at IDs
    // 1..=4n; higher IDs are Tseitin/XOR auxiliary vars. Forcing an
    // aux var doesn't prune walker-tree space, only walker-var forcings
    // halve the remaining sub-cube.
    state.trail0_size = solver.num_assigned_in_range(4 * ctx.n);
    harvest_forced(&solver, &mut state, &ctx);

    let mut stats = SyncStats {
        nodes_visited: 0, memo_hits: 0, capacity_rejects: 0,
        rule_rejects: 0, tuple_rejects: 0, sat_unsat: 0, leaves_reached: 0,
        learned_clauses_final: 0, max_level_reached: 0,
        nodes_by_level: vec![0; ctx.depth + 1],
        children_by_level: vec![0; ctx.depth + 1],
        children_total: 0, internal_nodes: 0,
        time_to_first_leaf: None,
        nogood_len_sum: 0, full_nogood_len_sum: 0,
        peer_clauses_read: 0, peer_clauses_imported: 0,
        forced_by_level: vec![0; ctx.depth + 1],
        sub_cube_time_by_level: vec![0.0; ctx.depth + 1],
        children_processed_by_level: vec![0; ctx.depth + 1],
        prop_by_kind_total: [0; radical::PropKind::COUNT],
        forced_by_level_kind: vec![[0; radical::PropKind::COUNT]; ctx.depth + 1],
    };

    let deadline = if cfg.sat_secs > 0 {
        Some(start + std::time::Duration::from_secs(cfg.sat_secs))
    } else { None };

    let mut found: Option<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)> = None;
    dfs(&mut solver, &mut state, &ctx, &mut stats, deadline, &mut found);

    let elapsed = start.elapsed();
    if verbose {
        eprintln!(
            "sync_walker: nodes={} memo_hits={} cap_rejects={} rule_rejects={} sat_unsat={} leaves={} max_lvl={} elapsed={:?}",
            stats.nodes_visited, stats.memo_hits, stats.capacity_rejects, stats.rule_rejects, stats.sat_unsat, stats.leaves_reached, stats.max_level_reached, elapsed,
        );
    }
    (found, stats, elapsed)
}

/// DFS descent. Thin wrapper around `dfs_body` that records wall-time
/// spent traversing the sub-cube rooted at the current level, so we
/// can report per-level "sub-cube traversal time" telemetry.
fn dfs(
    solver: &mut radical::Solver,
    state: &mut State,
    ctx: &Ctx,
    stats: &mut SyncStats,
    deadline: Option<Instant>,
    found: &mut Option<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>,
) -> bool {
    let entry_level = state.level;
    let t_enter = Instant::now();
    let result = dfs_body(solver, state, ctx, stats, deadline, found);
    if entry_level >= stats.sub_cube_time_by_level.len() {
        stats.sub_cube_time_by_level.resize(entry_level + 1, 0.0);
    }
    stats.sub_cube_time_by_level[entry_level] += t_enter.elapsed().as_secs_f64();
    result
}

/// Actual DFS body — see `dfs` for the timing wrapper.
/// Returns true if a solution was found (short-circuits up the stack).
fn dfs_body(
    solver: &mut radical::Solver,
    state: &mut State,
    ctx: &Ctx,
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

    // Cumulative count of walker-var propagations at this frame's
    // entry: the solver has just finished propagate_only(&parent_assums)
    // and the trail contains (trail0 walker-vars) + (parent assumption
    // lits) + (propagated walker-vars) + (propagated aux vars). We
    // subtract trail0 + assumption count to get only "walker vars
    // forced by propagation since level 0". Each subsequent child's
    // propagate_only can only make this number grow monotonically
    // (more assumptions → more forcings), and the per-level delta is
    // what we credit to `forced_by_level[child_level]`.
    let parent_walker_forced: usize = solver
        .num_assigned_in_range(4 * ctx.n)
        .saturating_sub(state.trail0_size + state.assumptions.len());

    // Pull peer clauses from the shared exchange every 256 nodes.
    // R10: peer-clause import via add_clause_deferred — safe at any
    // decision level (no immediate propagation, dropped on
    // unit-conflict). Restores per-depth peer-sharing that R1's
    // current_decision_level() == 0 gate had to suppress.
    if stats.nodes_visited & 0xFF == 0 {
        if let Some(ex) = &ctx.exchange {
            let local_next = stats.peer_clauses_read as usize;
            if let Ok(v) = ex.clauses.lock() {
                if v.len() > local_next {
                    // Clone the new clauses out so we can drop the lock.
                    let pending: Vec<Vec<i32>> = v[local_next..].to_vec();
                    stats.peer_clauses_read = v.len() as u64;
                    drop(v);
                    for clause in pending {
                        solver.add_clause_deferred(&clause);
                        stats.peer_clauses_imported += 1;
                    }
                }
            }
        }
    }
    // Periodically reduce the learnt clause DB so it doesn't grow
    // unbounded under sync's many push_assume_frame UNSATs (which
    // each install a learnt nogood when filtered.len() ≥ 2).
    // Trigger every 4096 nodes — well above the per-node cost.
    if stats.nodes_visited & 0xFFF == 0 {
        solver.reduce_db();
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
    //
    // `new_assums` / `num_new_assums` store only the NEW literals added at
    // this level (≤4). The full assumption list is reconstructed at child
    // entry via `state.assumptions.truncate(parent_len) +
    // extend_from_slice(&cand.new_assums)`, avoiding a per-candidate Vec
    // clone of the ancestor list (typically 4*level lits).
    struct Cand {
        new_assums: [i32; 4],
        num_new_assums: u8,
        placed_signs: [(u8, usize, i8); 4],
        num_placed: u8,
        score: i64,
        rule_state: u8,
    }
    let mut candidates: Vec<Cand> = Vec::with_capacity(16);

    // R8: capture the parent sums once before the speculative choice
    // loop. Each choice's "advance to level+1" is represented as
    // `apply_sum_delta_at(level)` on top of the parent sums, and the
    // rollback is a cheap `copy_from_slice(&parent_sums)` instead of a
    // full `rebuild_sums` over all prior levels' closure events.
    let spec_parent_sums = state.sums.clone();

    for choice in 0u8..16 {
        if !has_w && (choice & 1) != 0 { continue; }  // W bit must be 0 (ignored)
        let bx = if (choice >> 3) & 1 == 0 { 1i8 } else { -1 };
        let by = if (choice >> 2) & 1 == 0 { 1i8 } else { -1 };
        let bz = if (choice >> 1) & 1 == 0 { 1i8 } else { -1 };
        let bw = if choice & 1 == 0 { 1i8 } else { -1 };

        let mut placed = [(0u8, 0usize, 0i8); 4];
        let mut np: u8 = 0;
        let mut consistent = true;
        let mut new_assums: [i32; 4] = [0; 4];
        let mut num_new: u8 = 0;

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
            new_assums[num_new as usize] = if sign > 0 { var } else { -var };
            num_new += 1;
        }
        if !consistent { continue; }

        // Speculatively update sums for pairs closing at this level
        // using the placed bits. We don't call the solver yet — capacity
        // check first (cheap).
        // Stack-allocated saved bits (≤4 placements per choice — fits
        // in the same pattern as `placed` itself). Avoids the
        // per-choice Vec allocation that the choice loop's high
        // iteration count would otherwise pay 16× per node.
        let mut saved_bits: [(u8, usize, u8); 4] = [(0, 0, 0); 4];
        for k in 0..np as usize {
            let (ki, pi, _) = placed[k];
            saved_bits[k] = (ki, pi, state.bit(ki, pi));
        }
        // R8: kinds whose bit at pos_order[level] was 0 before this
        // choice — i.e. newly placed NOW. The parent's rebuild_sums
        // already counted closure_events[saved_level] events for kinds
        // whose bit was set by harvest (not in placed[]); this set
        // filters out those so we don't double-count.
        let mut newly_placed = [false; 4];
        for k in 0..np as usize {
            let (ki, _, _) = placed[k];
            newly_placed[ki as usize] = true;
        }
        for k in 0..np as usize {
            let (ki, pi, si) = placed[k];
            state.set_bit(ki, pi, si);
        }
        let saved_level = state.level;
        state.level += 1;
        // R8: delta on advance (only for newly-placed kinds), restore
        // parent sums from snapshot on rollback.
        apply_sum_delta_at(state, ctx, saved_level, &newly_placed);
        let violated = capacity_violated(state, ctx);
        // Early hopelessness: no valid Phase-A tuple is reachable from
        // the partial sums + remaining free-bit budget. Independent of
        // the per-lag capacity check — it constrains σ_final ranges
        // rather than N(s).
        let sigma_unreachable = !violated && !tuple_reachable(state, ctx);
        // Walker-side BDKR rule check: prune rule-violating placements
        // before calling the SAT solver. Saves a propagate_only per
        // rejected candidate and keeps CDCL from learning clauses about
        // non-canonical-but-otherwise-feasible branches.
        let rule_check = if !violated && !sigma_unreachable {
            check_rules(state, ctx, state.level - 1)
        } else {
            Err(())
        };
        let score = if !violated && !sigma_unreachable && rule_check.is_ok() {
            score_state(state, ctx)
        } else {
            i64::MAX
        };

        // Rollback speculative state.
        state.level = saved_level;
        for k in 0..np as usize {
            let (ki, pi, old_sign) = saved_bits[k];
            state.bits[(ki as usize) * ctx.n + pi] = old_sign;
        }
        // R8: restore parent sums from the pre-loop snapshot
        // (O(n)) instead of a full rebuild (O(total events)).
        state.sums.copy_from_slice(&spec_parent_sums);

        if violated {
            stats.capacity_rejects += 1;
            continue;
        }
        if sigma_unreachable {
            stats.tuple_rejects += 1;
            continue;
        }
        let new_rule_state = match rule_check {
            Ok(rs) => rs,
            Err(()) => {
                stats.rule_rejects += 1;
                continue;
            }
        };

        candidates.push(Cand {
            new_assums,
            num_new_assums: num_new,
            placed_signs: placed,
            num_placed: np,
            score,
            rule_state: new_rule_state,
        });
    }
    stats.internal_nodes += 1;
    stats.children_total += candidates.len() as u64;
    if state.level >= stats.children_by_level.len() {
        stats.children_by_level.resize(state.level + 1, 0);
    }
    stats.children_by_level[state.level] += candidates.len() as u64;

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

    // Capture the entry level for the "candidates processed" counter:
    // the sibling loop may break before we decrement state.level, so
    // we must stash the level we started at.
    let entry_level = state.level;
    // Count of candidates that actually reached propagate_only (as
    // opposed to being skipped by an early break for `found`,
    // `deadline`, or `cancel`). Divided by `candidates.len()` this
    // gives the frame's coverage fraction; averaged across frames at a
    // given depth, it yields the level's coverage fraction and hence
    // the direct TTC formula `TTC = elapsed / root_coverage_product`.
    let total_candidates = candidates.len() as u64;
    let mut processed_count: u64 = 0;
    // Stored break-out result so we can hit the coverage accumulator
    // before returning (otherwise the loop's multiple exits would
    // bypass it).
    let mut result_override: Option<bool> = None;

    for cand in candidates {
        if found.is_some() { result_override = Some(true); break; }
        if let Some(d) = deadline {
            if Instant::now() >= d { result_override = Some(false); break; }
        }
        if let Some(c) = &ctx.cancel {
            if c.load(AtomicOrdering::Acquire) { result_override = Some(false); break; }
        }

        // Restore state.bits to the parent snapshot before each sibling.
        state.bits.copy_from_slice(&saved_all_bits);
        state.sums.copy_from_slice(&saved_sums);
        state.assumptions.truncate(saved_assum_len);
        state.rule_state = saved_rule_state;

        // R8b: collect newly-placed kinds (same logic as candidate
        // building) so the post-set_bit delta-apply doesn't double
        // count events whose kind was set by harvest_forced before
        // this dfs_body entry (those contributions are already in
        // saved_sums).
        let mut sib_newly_placed = [false; 4];
        for k in 0..cand.num_placed as usize {
            let (ki, _, _) = cand.placed_signs[k];
            sib_newly_placed[ki as usize] = true;
        }
        for k in 0..cand.num_placed as usize {
            let (ki, pi, si) = cand.placed_signs[k];
            state.set_bit(ki, pi, si);
        }
        state.assumptions.extend_from_slice(&cand.new_assums[..cand.num_new_assums as usize]);
        let sib_saved_level = state.level;
        state.level += 1;
        state.rule_state = cand.rule_state;
        // R8b: delta replaces full rebuild_sums(state, ctx) here.
        // state.sums starts at saved_sums (post-harvest at entry
        // level); the only events that newly fire at level
        // sib_saved_level are those involving kinds we just placed.
        apply_sum_delta_at(state, ctx, sib_saved_level, &sib_newly_placed);
        processed_count += 1;

        // R1: Incremental assumption propagation.
        //
        // Instead of calling `propagate_only(&state.assumptions)` —
        // which backtracks the solver to level 0 and re-enqueues every
        // ancestor lit per sibling — we push only this sibling's new
        // lits as a fresh decision level on top of the existing frame
        // stack. Ancestor frames' propagation work carries over
        // unchanged. On UNSAT, `push_assume_frame` has already
        // backtracked to the parent level and installed the learnt
        // nogood; on SAT, we must pair with `pop_assume_frame` after
        // recursion.
        //
        // Invariant: at every dfs_body entry, `solver.current_decision_
        // level() == state.level` (and state.assumptions length
        // agrees).
        let mut pre_kind = [0u64; radical::PropKind::COUNT];
        for kind in radical::PropKind::ALL {
            pre_kind[kind as usize] = solver.propagations_by_kind(kind);
        }
        let new_lits = &cand.new_assums[..cand.num_new_assums as usize];
        let sat = solver.push_assume_frame(new_lits);
        if state.level >= stats.forced_by_level_kind.len() {
            stats.forced_by_level_kind.resize(
                state.level + 1,
                [0; radical::PropKind::COUNT],
            );
        }
        for kind in radical::PropKind::ALL {
            let post = solver.propagations_by_kind(kind);
            let delta = post - pre_kind[kind as usize];
            stats.prop_by_kind_total[kind as usize] += delta;
            stats.forced_by_level_kind[state.level][kind as usize] += delta;
        }
        if sat == Some(true) {
            // Count walker-var forcings that THIS level's new assumptions
            // caused. `child_walker_forced` is cumulative across levels
            // 0..=state.level; `parent_walker_forced` (captured at dfs
            // entry) is cumulative across 0..=state.level-1. The delta
            // is the "2^delta sub-cubes pruned" that we get for free at
            // this walker level.
            let child_walker_forced: usize = solver
                .num_assigned_in_range(4 * ctx.n)
                .saturating_sub(state.trail0_size + state.assumptions.len());
            let delta = child_walker_forced.saturating_sub(parent_walker_forced);
            if state.level >= stats.forced_by_level.len() {
                stats.forced_by_level.resize(state.level + 1, 0);
            }
            stats.forced_by_level[state.level] += delta as u64;

            // R8c: skip the full rebuild_sums when harvest_forced
            // didn't set any new walker bits (state.sums is already
            // consistent with state.bits in that case). At shallow
            // levels harvest typically finds 0-1 new bits; this skip
            // saves an O(L * events) scan per accepted candidate.
            //
            // R8d (rejected): also gating harvest itself on `delta > 0`
            // regressed TTC by ~4% — harvest's pre-set state.bits is
            // used by the next dfs_body's candidate-building loop to
            // reject choices that would conflict with SAT-forced bits;
            // skipping harvest pushes that work into more expensive
            // push_assume_frame conflicts.
            let n_harvested = harvest_forced(solver, state, ctx);
            if n_harvested > 0 {
                rebuild_sums(state, ctx);
            }
            // After harvest: many bits beyond the walker frontier
            // may now be set (via rule propagation into the
            // middle). Use the tighter dynamic capacity check
            // which accounts for pairs already fully determined.
            let found_solution = !capacity_violated(state, ctx)
                && dfs(solver, state, ctx, stats, deadline, found);
            // Pop this sibling's frame before moving to the next
            // sibling. Must be paired with the Some(true) push above.
            solver.pop_assume_frame();
            if found_solution {
                result_override = Some(true);
                break;
            }
        } else {
            stats.sat_unsat += 1;
            let (ng, full) = solver.last_nogood_stats();
            stats.nogood_len_sum += ng as u64;
            stats.full_nogood_len_sum += full as u64;
            // Publish the just-learnt nogood to peer workers, but
            // only if it's small enough to be useful. R10: with
            // mid-search peer import enabled (add_clause_deferred),
            // import volume scales with how aggressively we share.
            // Restrict to very short clauses (Glucose tier-1 proxy)
            // so watch lists stay lean.
            const MAX_SHARED_LEN: usize = 2;
            if let Some(ex) = &ctx.exchange {
                if let Some(clause) = solver.take_last_learnt_clause() {
                    if clause.len() <= MAX_SHARED_LEN {
                        if let Ok(mut v) = ex.clauses.lock() {
                            v.push(clause);
                        }
                    }
                }
            }
        }

        // Rollback level only; state.bits, sums, assumptions get
        // fully restored at the top of the next iteration (or the
        // caller's rollback if no next iteration).
        state.level -= 1;
    }

    // Record coverage at this frame's level. `total_candidates` was
    // already added to `children_by_level` before the loop; this is
    // the matching "actually processed" numerator.
    if entry_level >= stats.children_processed_by_level.len() {
        stats.children_processed_by_level.resize(entry_level + 1, 0);
    }
    stats.children_processed_by_level[entry_level] += processed_count;
    let _ = total_candidates;  // silence unused if only for debugging

    // Final rollback to leave state as caller expected.
    state.bits.copy_from_slice(&saved_all_bits);
    state.sums.copy_from_slice(&saved_sums);
    state.assumptions.truncate(saved_assum_len);
    state.rule_state = saved_rule_state;
    // Restore state.level if the loop broke with state.level bumped.
    state.level = entry_level;

    if let Some(v) = result_override { return v; }
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
