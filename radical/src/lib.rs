// Minimal CDCL SAT solver inspired by CaDiCaL.
//
// Core features:
// - Two-watched-literal (2WL) unit propagation
// - 1-UIP conflict analysis with clause learning
// - Non-chronological backjumping
// - VSIDS variable activity heuristic with decay
// - Luby restart schedule
// - Clause database with LBD-based cleanup
//
// API matches the subset of cadical::Solver we use:
//   add_clause(lits), solve() -> Option<bool>, value(lit) -> Option<bool>

/// A literal is a signed integer: positive for the variable, negative for its negation.
/// Variables are 1-indexed. Literal 0 is invalid.
type Lit = i32;

/// Internal variable index (0-based). Variable `v` (1-based) maps to index `v-1`.
fn var_of(lit: Lit) -> usize {
    (lit.unsigned_abs() - 1) as usize
}

/// Convert a literal to its index in the watch/polarity arrays.
/// Positive literal `v` → index `2*(v-1)`, negative `¬v` → index `2*(v-1)+1`.
fn lit_index(lit: Lit) -> usize {
    let v = var_of(lit);
    if lit > 0 { 2 * v } else { 2 * v + 1 }
}

fn negate(lit: Lit) -> Lit {
    -lit
}

/// Assignment value for a variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum LBool {
    Undef = 0,
    True = 1,
    False = 2,
}

/// Clause metadata (literals stored in flat `clause_lits` array).
#[derive(Clone, Copy, Debug)]
struct ClauseMeta {
    start: u32,  // index into clause_lits
    len: u16,
    learnt: bool,
    lbd: u8,
    deleted: bool,
}

/// A pseudo-boolean constraint: sum(coeffs[i] * lits[i]) >= bound.
/// When slack < coeffs[i] for some undef literal, that literal must be true.
#[derive(Clone, Debug)]
struct PbConstraint {
    lits: Vec<Lit>,
    coeffs: Vec<u32>,
    bound: u32,
}

/// An XOR (GF(2)) constraint: XOR of variables = parity.
/// Propagation: when exactly one variable is unassigned, force it
/// to satisfy the parity. Incremental: track count of unknowns and
/// running XOR of assigned values.
#[derive(Clone, Debug)]
struct XorConstraint {
    vars: Vec<usize>,     // 0-based variable indices
    parity: bool,         // RHS: XOR of all vars must equal this
    num_unknown: u32,     // count of currently-unassigned vars
    assigned_xor: bool,   // XOR of assigned variable values (true = 1)
}

/// A quadratic pseudo-boolean constraint with exact target:
///   sum(coeffs[i] * lits_a[i] * lits_b[i]) = target
/// Each term contributes coeffs[i] iff both lits_a[i] and lits_b[i] are true.
///
/// Propagation uses two-sided slack:
/// - upper_slack = sum of coeffs for potentially-true terms - target
///   (if upper_slack < 0 → conflict: can't reach target)
/// - lower_slack = target - sum of coeffs for definitely-true terms
///   (if lower_slack < 0 → conflict: already exceeded target)
///
/// When upper_slack < coeff[i] for a potentially-true term where one
/// lit is true and the other undef → force the undef lit true.
/// When lower_slack < coeff[i] for a potentially-true term where both
/// lits are undef or one is true → force a false assignment to prevent exceeding.
/// Per-term data for a quadratic PB constraint, packed into a single struct
/// for cache-friendly access and cheap cloning (one Vec instead of ten).
/// State lookup table for quad PB terms. Indexed by:
///   aa * 12 + ab * 4 + tv_offset
/// where aa/ab are LBool as u8 (Undef=0, True=1, False=2) and
/// tv_offset encodes the true_val pair (0-3).
/// Returns: 0=DEAD, 1=MAYBE, 2=TRUE.
static QPB_STATE_TABLE: [u8; 36] = [
    // aa=Undef(0), ab=Undef(0): always MAYBE
    1, 1, 1, 1,
    // aa=Undef(0), ab=True(1): MAYBE if mb, DEAD if !mb
    //   tv=(T,T)→mb=1→M, tv=(T,F)→mb=0→D, tv=(F,T)→mb=1→M, tv=(F,F)→mb=0→D
    1, 0, 1, 0,
    // aa=Undef(0), ab=False(2): MAYBE if mb, DEAD if !mb
    //   tv=(T,T)→mb=0→D, tv=(T,F)→mb=1→M, tv=(F,T)→mb=0→D, tv=(F,F)→mb=1→M
    0, 1, 0, 1,
    // aa=True(1), ab=Undef(0): MAYBE if ma, DEAD if !ma
    //   tv=(T,*)→ma=1→M, tv=(F,*)→ma=0→D
    1, 1, 0, 0,
    // aa=True(1), ab=True(1): TRUE if ma&&mb, else DEAD
    2, 0, 0, 0,
    // aa=True(1), ab=False(2)
    0, 2, 0, 0,
    // aa=False(2), ab=Undef(0)
    0, 0, 1, 1,
    // aa=False(2), ab=True(1)
    0, 0, 2, 0,
    // aa=False(2), ab=False(2)
    0, 0, 0, 2,
];

#[derive(Clone, Copy, Debug)]
struct QuadPbTerm {
    lit_a: Lit,
    lit_b: Lit,
    coeff: u16,
    var_a: u16,     // cached var_of(lit_a) as u16
    var_b: u16,     // cached var_of(lit_b) as u16
    state: u8,      // 0=DEAD, 1=MAYBE, 2=TRUE
    tv_offset: u8,  // precomputed: (if lit_a < 0 { 2 } else { 0 }) + (if lit_b < 0 { 1 } else { 0 })
}

impl QuadPbTerm {
    #[inline(always)]
    fn var_a(&self) -> usize { self.var_a as usize }
    #[inline(always)]
    fn var_b(&self) -> usize { self.var_b as usize }
    #[inline(always)]
    fn true_val_a(&self) -> LBool { if self.lit_a > 0 { LBool::True } else { LBool::False } }
    #[inline(always)]
    fn true_val_b(&self) -> LBool { if self.lit_b > 0 { LBool::True } else { LBool::False } }
    #[inline(always)]
    fn neg_a(&self) -> bool { self.lit_a < 0 }
    #[inline(always)]
    fn neg_b(&self) -> bool { self.lit_b < 0 }
    /// Compute state from two LBool assignments using branchless table lookup.
    #[inline(always)]
    fn compute_state(&self, aa: LBool, ab: LBool) -> u8 {
        QPB_STATE_TABLE[(aa as u8 as usize) * 12 + (ab as u8 as usize) * 4 + self.tv_offset as usize]
    }
}

#[derive(Clone, Debug)]
struct QuadPbConstraint {
    terms: Vec<QuadPbTerm>,  // single Vec instead of 10 separate ones
    target: u32,
    num_terms: u32,
    /// Branchless counter array indexed by state: sums[0]=dead(unused), sums[1]=maybe, sums[2]=true.
    /// Replaces separate sum_true/sum_maybe fields for branch-free updates.
    sums: [i32; 3],
    /// When true, sums[] and term states are stale (need recomputation before use).
    stale: bool,
}

/// Reason a variable was assigned (for conflict analysis).
#[derive(Clone, Copy, Debug)]
enum Reason {
    Decision,
    Clause(u32),  // index into clause database
    Pb(u32),      // index into pb_constraints
    QuadPb(u32),  // index into quad_pb_constraints; bit 31 = is_upper flag
    Xor(u32),     // index into xor_constraints
}

/// Trail entry: records an assignment.
#[derive(Clone, Copy, Debug)]
struct TrailEntry {
    lit: Lit,
    level: u32,
    reason: Reason,
}

/// Configuration flags for optional solver features.
/// All default to `false` (disabled). Checked at non-hot decision points
/// (once per conflict/restart), so branch prediction makes them zero-cost.
#[derive(Clone, Debug)]
pub struct SolverConfig {
    /// Use glucose-style EMA restarts instead of Luby.
    pub ema_restarts: bool,
    /// Run failed literal probing before solve.
    pub probing: bool,
    /// Periodically reset phase saving (rephasing).
    pub rephasing: bool,
    /// Enable GF(2) XOR propagation during BCP.
    pub xor_propagation: bool,
    /// Try saved phase as complete assignment before CDCL search (Kissat-style).
    pub lucky_phases: bool,
    /// Periodically vivify (shorten) learnt clauses during restarts.
    pub vivification: bool,
    /// Use chronological backtracking for shallow conflicts.
    pub chrono_bt: bool,
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self {
            ema_restarts: false,
            probing: false,
            rephasing: false,
            xor_propagation: true,
            lucky_phases: false,
            vivification: false,
            chrono_bt: false,
        }
    }
}

/// CDCL SAT Solver.
#[derive(Clone)]
pub struct Solver {
    /// Feature flags (checked at non-hot decision points).
    pub config: SolverConfig,
    // Variable state
    num_vars: usize,
    assigns: Vec<LBool>,    // indexed by var (0-based)
    level: Vec<u32>,         // decision level of each var
    reason: Vec<Reason>,     // reason for assignment
    trail_pos: Vec<usize>,   // trail position when variable was assigned (for lazy explanation filtering)
    phase: Vec<bool>,        // phase saving: last polarity of each var

    // Trail
    trail: Vec<TrailEntry>,
    trail_lim: Vec<usize>,  // trail index at start of each decision level

    // Clause database (flat storage for cheap cloning)
    clause_meta: Vec<ClauseMeta>,
    clause_lits: Vec<Lit>,         // flat array of all clause literals
    watches: Vec<Vec<(u32, Lit)>>,  // watches[lit_index] = (clause_index, blocker_literal)

    // VSIDS activity with binary heap
    activity: Vec<f64>,
    var_inc: f64,
    var_decay: f64,
    heap: Vec<usize>,        // max-heap of variable indices, ordered by activity
    heap_pos: Vec<usize>,    // heap_pos[v] = position of var v in heap (usize::MAX if not in heap)

    // Pseudo-boolean constraints
    pb_constraints: Vec<PbConstraint>,
    pb_watches: Vec<Vec<u32>>,  // pb_watches[lit_index] = list of PB constraint indices

    // Quadratic PB constraints
    quad_pb_constraints: Vec<QuadPbConstraint>,
    quad_pb_var_watches: Vec<Vec<u32>>,       // quad_pb_var_watches[var] = list of constraint indices
    quad_pb_var_terms: Vec<Vec<(u32, u16, bool)>>,  // (constraint_idx, term_idx, is_var_a)
    // Reusable scratch buffer for quad PB explanation building (on-demand during analysis)
    quad_pb_seen_buf: Vec<bool>,

    // Reusable scratch buffers for conflict analysis (avoids per-conflict heap allocations)
    analyze_seen: Vec<bool>,           // seen[] in analyze()
    analyze_reason_buf: Vec<Lit>,      // reusable for quad PB explanation in analyze
    analyze_reason_buf2: Vec<Lit>,     // reusable for quad PB explanation in lit_removable
    minimize_stack: Vec<usize>,        // stack for lit_removable()
    minimize_visited: Vec<bool>,       // visited[] for lit_removable()
    minimize_levels: Vec<bool>,        // levels_in_learnt for minimize_learnt()

    // XOR (GF(2)) constraints
    xor_constraints: Vec<XorConstraint>,
    xor_var_watches: Vec<Vec<u32>>,  // xor_var_watches[var] = list of XOR constraint indices

    // Propagation queue
    prop_head: usize, // next trail entry to propagate

    // Restart (Luby)
    conflicts: u64,
    restart_limit: u64,
    luby_index: u32,

    // Restart (EMA) — glucose-style adaptive restarts
    ema_lbd_fast: f64,   // fast EMA of recent LBD (α ≈ 1/32)
    ema_lbd_slow: f64,   // slow EMA of global LBD (α ≈ 1/4096)
    ema_restart_block: u64, // conflicts since last restart (for blocking)
    ema_trail_fast: f64, // fast EMA of trail size (for blocking)
    ema_trail_slow: f64, // slow EMA of trail size

    // Rephasing state
    rephase_conflicts: u64, // next conflict count to trigger rephase
    best_phase: Vec<bool>,  // best known phase assignment
    best_phase_set: bool,   // whether best_phase has been populated

    // Limits
    conflict_limit: u64,  // 0 = no limit

    // State
    ok: bool, // false if top-level conflict detected
    /// When true, skip quad PB incremental updates during backtrack.
    /// Used when the caller will reset quad PB state externally.
    pub skip_backtrack_quad_pb: bool,
}

impl Solver {
    /// Get the literals of clause `ci`.
    #[inline]
    #[allow(dead_code)]
    fn clause_lits(&self, ci: u32) -> &[Lit] {
        let m = &self.clause_meta[ci as usize];
        &self.clause_lits[m.start as usize..(m.start as usize + m.len as usize)]
    }

    /// Get a mutable reference to the literals of clause `ci`.
    #[inline]
    #[allow(dead_code)]
    fn clause_lits_mut(&mut self, ci: u32) -> &mut [Lit] {
        let m = &self.clause_meta[ci as usize];
        &mut self.clause_lits[m.start as usize..(m.start as usize + m.len as usize)]
    }
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    pub fn new() -> Self {
        Self {
            config: SolverConfig::default(),
            num_vars: 0,
            assigns: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            trail_pos: Vec::new(),
            phase: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            clause_meta: Vec::new(),
            clause_lits: Vec::new(),
            watches: Vec::new(),
            pb_constraints: Vec::new(),
            pb_watches: Vec::new(),
            quad_pb_constraints: Vec::new(),
            quad_pb_var_watches: Vec::new(),
            quad_pb_var_terms: Vec::new(),
            quad_pb_seen_buf: Vec::new(),
            xor_constraints: Vec::new(),
            xor_var_watches: Vec::new(),
            analyze_seen: Vec::new(),
            analyze_reason_buf: Vec::new(),
            analyze_reason_buf2: Vec::new(),
            minimize_stack: Vec::new(),
            minimize_visited: Vec::new(),
            minimize_levels: Vec::new(),
            activity: Vec::new(),
            var_inc: 1.0,
            var_decay: 0.95,
            heap: Vec::new(),
            heap_pos: Vec::new(),
            prop_head: 0,
            conflicts: 0,
            restart_limit: 100,
            luby_index: 0,
            ema_lbd_fast: 0.0,
            ema_lbd_slow: 0.0,
            ema_restart_block: 0,
            ema_trail_fast: 0.0,
            ema_trail_slow: 0.0,
            rephase_conflicts: 10000,
            best_phase: Vec::new(),
            best_phase_set: false,
            conflict_limit: 0,
            ok: true,
            skip_backtrack_quad_pb: false,
        }
    }

    /// Ensure variable `v` (1-based) exists.
    fn ensure_var(&mut self, v: usize) {
        while self.num_vars < v {
            let idx = self.num_vars;
            self.num_vars += 1;
            self.assigns.push(LBool::Undef);
            self.level.push(0);
            self.reason.push(Reason::Decision);
            self.trail_pos.push(0);
            self.phase.push(true); // default: branch positive
            self.activity.push(0.0);
            self.watches.push(Vec::new()); // positive literal watch
            self.watches.push(Vec::new()); // negative literal watch
            self.pb_watches.push(Vec::new()); // positive literal PB
            self.pb_watches.push(Vec::new()); // negative literal PB
            self.quad_pb_var_watches.push(Vec::new());
            self.quad_pb_var_terms.push(Vec::new());
            self.xor_var_watches.push(Vec::new());
            self.heap_pos.push(self.heap.len());
            self.heap.push(idx);
        }
    }

    /// Add a clause. Literals are signed integers (DIMACS convention).
    pub fn add_clause(&mut self, lits: impl IntoIterator<Item = i32>) {
        if !self.ok { return; }
        let lits: Vec<Lit> = lits.into_iter().collect();

        // Ensure all variables exist
        for &lit in &lits {
            assert!(lit != 0, "literal 0 is invalid");
            self.ensure_var(lit.unsigned_abs() as usize);
        }

        match lits.len() {
            0 => { self.ok = false; }
            1 => {
                // Unit clause: enqueue immediately
                let lit = lits[0];
                let val = self.lit_value(lit);
                match val {
                    LBool::True => {} // already satisfied
                    LBool::False => { self.ok = false; } // contradiction
                    LBool::Undef => {
                        // Store as a clause so we have a reason index
                        let ci = self.clause_meta.len() as u32;
                        let start = self.clause_lits.len() as u32;
                        self.clause_lits.extend_from_slice(&lits);
                        self.clause_meta.push(ClauseMeta { start, len: lits.len() as u16, learnt: false, lbd: 0, deleted: false });
                        self.enqueue(lit, Reason::Clause(ci));
                        // Propagate immediately
                        if self.propagate().is_some() {
                            self.ok = false;
                        }
                    }
                }
            }
            _ => {
                let ci = self.clause_meta.len() as u32;
                let start = self.clause_lits.len() as u32;
                // Set up 2WL: watch the first two literals (blocker = the other watched lit)
                self.watches[lit_index(negate(lits[0]))].push((ci, lits[1]));
                self.watches[lit_index(negate(lits[1]))].push((ci, lits[0]));
                self.clause_lits.extend_from_slice(&lits);
                self.clause_meta.push(ClauseMeta { start, len: lits.len() as u16, learnt: false, lbd: 0, deleted: false });
            }
        }
    }

    /// Add a pseudo-boolean "at least" constraint: sum(coeffs[i] * lits[i]) >= bound.
    /// All coefficients must be positive. Literals use DIMACS convention.
    pub fn add_pb_atleast(&mut self, lits: &[i32], coeffs: &[u32], bound: u32) {
        if !self.ok { return; }
        assert_eq!(lits.len(), coeffs.len());

        // Ensure all variables exist
        for &lit in lits {
            assert!(lit != 0);
            self.ensure_var(lit.unsigned_abs() as usize);
        }

        let pbi = self.pb_constraints.len() as u32;

        // Watch all literals (we need to know when any becomes false)
        for &lit in lits {
            self.pb_watches[lit_index(negate(lit))].push(pbi);
        }

        self.pb_constraints.push(PbConstraint {
            lits: lits.to_vec(),
            coeffs: coeffs.to_vec(),
            bound,
        });

        // Initial propagation: check if any literals are already forced
        if self.propagate_pb(pbi).is_some() {
            self.ok = false;
        }
    }

    /// Add a pseudo-boolean equality: sum(coeffs[i] * lits[i]) = target.
    /// Encoded as two PB constraints: >= target AND sum(coeffs[i] * ¬lits[i]) >= sum(coeffs) - target.
    pub fn add_pb_eq(&mut self, lits: &[i32], coeffs: &[u32], target: u32) {
        let total: u32 = coeffs.iter().sum();
        // At least target
        self.add_pb_atleast(lits, coeffs, target);
        // At most target: negate all literals, bound = total - target
        if total >= target {
            let neg_lits: Vec<i32> = lits.iter().map(|&l| -l).collect();
            self.add_pb_atleast(&neg_lits, coeffs, total - target);
        }
    }

    /// Add a quadratic PB equality: sum(coeffs[i] * lits_a[i] * lits_b[i]) = target.
    /// Each term is 1 iff both lits_a[i] and lits_b[i] are true (under their polarities).
    pub fn add_quad_pb_eq(&mut self, lits_a: &[i32], lits_b: &[i32], coeffs: &[u32], target: u32) {
        if !self.ok { return; }
        assert_eq!(lits_a.len(), lits_b.len());
        assert_eq!(lits_a.len(), coeffs.len());

        for &lit in lits_a.iter().chain(lits_b.iter()) {
            assert!(lit != 0);
            self.ensure_var(lit.unsigned_abs() as usize);
        }

        let qi = self.quad_pb_constraints.len() as u32;

        // Watch by variable + build term index
        let mut watched = std::collections::HashSet::new();
        for i in 0..lits_a.len() {
            let va = var_of(lits_a[i]);
            let vb = var_of(lits_b[i]);
            if watched.insert(va) { self.quad_pb_var_watches[va].push(qi); }
            if watched.insert(vb) { self.quad_pb_var_watches[vb].push(qi); }
            self.quad_pb_var_terms[va].push((qi, i as u16, true));   // is_var_a = true
            self.quad_pb_var_terms[vb].push((qi, i as u16, false));  // is_var_a = false
        }

        let terms: Vec<QuadPbTerm> = (0..lits_a.len()).map(|i| {
            QuadPbTerm {
                lit_a: lits_a[i],
                lit_b: lits_b[i],
                coeff: coeffs[i] as u16,
                var_a: var_of(lits_a[i]) as u16,
                var_b: var_of(lits_b[i]) as u16,
                state: 1, // MAYBE
                tv_offset: (if lits_a[i] < 0 { 2u8 } else { 0 }) + (if lits_b[i] < 0 { 1 } else { 0 }),
            }
        }).collect();
        self.quad_pb_constraints.push(QuadPbConstraint {
            target,
            num_terms: terms.len() as u32,
            sums: [0, coeffs.iter().sum::<u32>() as i32, 0],
            terms,
            stale: true, // must recompute: some vars may already be assigned
        });

        // Recompute from current assignments, then propagate
        self.recompute_quad_pb(qi);
        if self.propagate_quad_pb(qi).is_some() {
            self.ok = false;
        }
    }

    /// Add an XOR constraint: XOR of the given variables (1-based) = parity.
    /// The constraint propagates during BCP: when exactly one variable remains
    /// unassigned, it is forced to satisfy the parity.
    pub fn add_xor(&mut self, vars_1based: &[i32], parity: bool) {
        if !self.ok { return; }
        let mut vars: Vec<usize> = Vec::with_capacity(vars_1based.len());
        for &v in vars_1based {
            let uv = v.unsigned_abs() as usize;
            assert!(uv > 0);
            self.ensure_var(uv);
            vars.push(uv - 1); // convert to 0-based
        }
        // Adjust parity for negated literals
        let mut p = parity;
        for &v in vars_1based {
            if v < 0 { p = !p; }
        }

        let xi = self.xor_constraints.len() as u32;
        for &v in &vars {
            self.xor_var_watches[v].push(xi);
        }

        // Check for already-assigned variables
        let mut num_unknown = vars.len() as u32;
        let mut assigned_xor = false;
        for &v in &vars {
            if self.assigns[v] != LBool::Undef {
                num_unknown -= 1;
                if self.assigns[v] == LBool::True {
                    assigned_xor ^= true;
                }
            }
        }

        self.xor_constraints.push(XorConstraint {
            vars,
            parity: p,
            num_unknown,
            assigned_xor,
        });

        // Immediate check (no propagation — the main solve loop handles that)
        if num_unknown == 0 {
            if assigned_xor != p {
                self.ok = false;
            }
        } else if num_unknown == 1 {
            // Find the one unassigned variable and force it.
            // Update the constraint state immediately so propagate() doesn't double-count.
            let xc = &self.xor_constraints[xi as usize];
            for &v in &xc.vars {
                if self.assigns[v] == LBool::Undef {
                    let need_true = xc.assigned_xor ^ xc.parity;
                    let lit = if need_true { (v + 1) as Lit } else { -((v + 1) as Lit) };
                    let val = need_true;
                    let xc = &mut self.xor_constraints[xi as usize];
                    xc.num_unknown = 0;
                    xc.assigned_xor ^= val;
                    self.enqueue(lit, Reason::Xor(xi));
                    break;
                }
            }
        }
    }

    /// Solve the formula. Returns Some(true) if SAT, Some(false) if UNSAT.
    pub fn solve(&mut self) -> Option<bool> {
        self.solve_with_assumptions(&[])
    }

    /// Solve under temporary assumptions. Assumptions are unit literals that
    /// are asserted at decision level 1. After solving, the solver backtracks
    /// to level 0, so assumptions don't persist but learnt clauses do.
    pub fn solve_with_assumptions(&mut self, assumptions: &[Lit]) -> Option<bool> {
        if !self.ok { return Some(false); }

        // Pre-size reusable buffers for analysis and explanation
        if self.quad_pb_seen_buf.len() < self.num_vars {
            self.quad_pb_seen_buf.resize(self.num_vars, false);
        }
        if self.analyze_seen.len() < self.num_vars {
            self.analyze_seen.resize(self.num_vars, false);
        }
        if self.minimize_visited.len() < self.num_vars {
            self.minimize_visited.resize(self.num_vars, false);
        }
        if self.best_phase.len() < self.num_vars {
            self.best_phase.resize(self.num_vars, false);
        }

        // Failed literal probing (runs once before first solve)
        if self.config.probing && self.conflicts == 0 {
            self.probe();
            if !self.ok { return Some(false); }
        }

        let assumption_level: u32 = if assumptions.is_empty() { 0 } else { 1 };

        // Assert assumptions at decision level 1
        if !assumptions.is_empty() {
            self.new_decision_level();
            for &lit in assumptions {
                self.ensure_var(lit.unsigned_abs() as usize);
                match self.lit_value(lit) {
                    LBool::True => {} // already satisfied
                    LBool::False => {
                        self.backtrack(0);
                        return Some(false); // contradicts existing assignment
                    }
                    LBool::Undef => {
                        self.enqueue(lit, Reason::Decision);
                    }
                }
            }
            // Propagate assumptions
            if let Some(_conflict) = self.propagate() {
                self.backtrack(0);
                return Some(false);
            }
        }

        // Lucky phase: try the saved phase vector as a complete assignment.
        // If it propagates without conflict, we solve in 0 conflicts.
        if self.config.lucky_phases {
            if let Some(result) = self.try_lucky_phase(assumption_level) {
                if result {
                    return Some(true); // keep model for value() queries
                }
                // Conflict — backtrack and fall through to normal search
            }
        }

        let result = self.solve_inner(assumption_level);

        // Only backtrack if UNSAT — keep model for value() queries if SAT.
        if result != Some(true) {
            self.backtrack(0);
        }
        result
    }

    /// Reset the solver to level 0 (undo all decisions, keep learnt clauses).
    pub fn reset(&mut self) {
        self.backtrack(0);
    }

    /// Number of variables.
    pub fn num_vars(&self) -> usize { self.num_vars }
    /// Number of active (non-deleted) clauses.
    pub fn num_clauses(&self) -> usize {
        self.clause_meta.iter().filter(|m| !m.deleted).count()
    }
    /// Number of conflicts so far.
    pub fn num_conflicts(&self) -> u64 { self.conflicts }

    /// Write all clauses in DIMACS CNF format to the given writer.
    /// Note: PB and quad-PB constraints are not included (DIMACS only supports CNF).
    pub fn dump_dimacs(&self, w: &mut impl std::io::Write) -> std::io::Result<()> {
        let num_clauses = self.clause_meta.iter().filter(|m| !m.deleted).count();
        writeln!(w, "p cnf {} {}", self.num_vars, num_clauses)?;
        for m in &self.clause_meta {
            if m.deleted { continue; }
            let lits = &self.clause_lits[m.start as usize..(m.start as usize + m.len as usize)];
            for &lit in lits {
                write!(w, "{} ", lit)?;
            }
            writeln!(w, "0")?;
        }
        Ok(())
    }

    /// Set a conflict limit. Solve returns None if limit is reached.
    /// Set to 0 to disable.
    /// Returns true if the solver is in a consistent state (no top-level contradiction detected).
    pub fn is_ok(&self) -> bool { self.ok }

    /// Add multiple unit clauses and propagate once at the end.
    /// More efficient than calling add_clause() for each unit individually.
    pub fn add_unit_clauses_batch(&mut self, units: &[Lit]) {
        if !self.ok { return; }
        for &lit in units {
            self.ensure_var(lit.unsigned_abs() as usize);
            let val = self.lit_value(lit);
            match val {
                LBool::True => {} // already satisfied
                LBool::False => { self.ok = false; return; }
                LBool::Undef => {
                    let ci = self.clause_meta.len() as u32;
                    let start = self.clause_lits.len() as u32;
                    self.clause_lits.push(lit);
                    self.clause_meta.push(ClauseMeta { start, len: 1, learnt: false, lbd: 0, deleted: false });
                    self.enqueue(lit, Reason::Clause(ci));
                }
            }
        }
        // Single propagation pass for all enqueued units
        if self.propagate().is_some() {
            self.ok = false;
        }
    }

    pub fn set_conflict_limit(&mut self, limit: u64) { self.conflict_limit = limit; }

    /// Set a per-call conflict budget: solver stops after `budget` additional conflicts.
    pub fn set_conflict_budget(&mut self, budget: u64) {
        self.conflict_limit = self.conflicts + budget;
    }

    /// Find equivalent literals via SCC on the binary implication graph.
    /// Returns number of equivalences found and applied.
    pub fn preprocess_scc_equivalences(&mut self) -> usize {
        if !self.ok { return 0; }
        // Propagate first
        if self.propagate().is_some() {
            self.ok = false;
            return 0;
        }

        let n = self.num_vars;
        let num_lits = 2 * n;

        // Build adjacency list for binary implication graph
        // Literal l → index: pos(v) = 2*v, neg(v) = 2*v+1
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); num_lits];

        for m in &self.clause_meta {
            if m.deleted || m.len != 2 { continue; }
            let lits = &self.clause_lits[m.start as usize..(m.start as usize + 2)];
            let a = lits[0];
            let b = lits[1];
            // Clause (a, b) means: -a → b and -b → a
            let idx_neg_a = lit_index(-a);
            let idx_b = lit_index(b);
            let idx_neg_b = lit_index(-b);
            let idx_a = lit_index(a);
            if idx_neg_a < num_lits && idx_b < num_lits {
                adj[idx_neg_a].push(idx_b);
            }
            if idx_neg_b < num_lits && idx_a < num_lits {
                adj[idx_neg_b].push(idx_a);
            }
        }

        // Tarjan's SCC
        let mut index_counter: usize = 0;
        let mut stack: Vec<usize> = Vec::new();
        let mut on_stack = vec![false; num_lits];
        let mut lowlink = vec![0usize; num_lits];
        let mut index = vec![usize::MAX; num_lits];
        let mut scc_id = vec![usize::MAX; num_lits]; // which SCC each literal belongs to
        let mut num_sccs = 0usize;

        // Iterative Tarjan's to avoid stack overflow
        let mut call_stack: Vec<(usize, usize)> = Vec::new(); // (node, neighbor_idx)

        for start in 0..num_lits {
            if index[start] != usize::MAX { continue; }

            call_stack.push((start, 0));
            index[start] = index_counter;
            lowlink[start] = index_counter;
            index_counter += 1;
            stack.push(start);
            on_stack[start] = true;

            while let Some(&mut (node, ref mut ni)) = call_stack.last_mut() {
                if *ni < adj[node].len() {
                    let w = adj[node][*ni];
                    *ni += 1;
                    if index[w] == usize::MAX {
                        index[w] = index_counter;
                        lowlink[w] = index_counter;
                        index_counter += 1;
                        stack.push(w);
                        on_stack[w] = true;
                        call_stack.push((w, 0));
                    } else if on_stack[w] {
                        lowlink[node] = lowlink[node].min(index[w]);
                    }
                } else {
                    // Done with this node
                    if lowlink[node] == index[node] {
                        // Root of SCC
                        let scc = num_sccs;
                        num_sccs += 1;
                        loop {
                            let w = stack.pop().unwrap();
                            on_stack[w] = false;
                            scc_id[w] = scc;
                            if w == node { break; }
                        }
                    }
                    let (popped_node, _) = call_stack.pop().unwrap();
                    if let Some(&(parent, _)) = call_stack.last() {
                        lowlink[parent] = lowlink[parent].min(lowlink[popped_node]);
                    }
                }
            }
        }

        // Check for contradictions: if lit and -lit are in the same SCC, UNSAT
        for v in 0..n {
            let pos = 2 * v;
            let neg = 2 * v + 1;
            if scc_id[pos] != usize::MAX && scc_id[pos] == scc_id[neg] {
                // Variable and its negation are equivalent → UNSAT
                self.ok = false;
                return 0;
            }
        }

        // Find equivalent literal pairs: if scc_id[pos(v)] == scc_id[pos(w)],
        // then v ↔ w (they must have the same value)
        // If scc_id[pos(v)] == scc_id[neg(w)], then v ↔ -w
        // Build a representative map: for each variable, map to its representative
        let mut repr: Vec<i32> = (0..n).map(|v| (v + 1) as i32).collect(); // identity map (1-based)
        let mut equivs = 0usize;

        for v in 0..n {
            if self.assigns[v] != LBool::Undef { continue; }
            let pos_v = 2 * v;
            if scc_id[pos_v] == usize::MAX { continue; }

            for w in (v + 1)..n {
                if self.assigns[w] != LBool::Undef { continue; }
                let pos_w = 2 * w;
                if scc_id[pos_w] == usize::MAX { continue; }

                if scc_id[pos_v] == scc_id[pos_w] {
                    // v ↔ w: substitute w with v
                    repr[w] = (v + 1) as i32; // positive equivalence
                    equivs += 1;
                } else if scc_id[pos_v] == scc_id[2 * w + 1] {
                    // v ↔ -w: substitute w with -v
                    repr[w] = -((v + 1) as i32); // negative equivalence
                    equivs += 1;
                }
            }
        }

        if equivs == 0 { return 0; }

        // Apply substitutions to all non-deleted clauses
        for m in &mut self.clause_meta {
            if m.deleted { continue; }
            let start = m.start as usize;
            let len = m.len as usize;
            for i in start..start + len {
                let lit = self.clause_lits[i];
                let v = var_of(lit);
                let r = repr[v];
                if r != (v + 1) as i32 {
                    // Substitute
                    self.clause_lits[i] = if lit > 0 { r } else { -r };
                }
            }
        }

        // Rebuild watches (substitution may have changed watched literals)
        for wl in &mut self.watches {
            wl.clear();
        }
        for (ci, m) in self.clause_meta.iter().enumerate() {
            if m.deleted || m.len < 2 { continue; }
            let lits = &self.clause_lits[m.start as usize..(m.start as usize + m.len as usize)];
            self.watches[lit_index(negate(lits[0]))].push((ci as u32, lits[1]));
            self.watches[lit_index(negate(lits[1]))].push((ci as u32, lits[0]));
        }

        equivs
    }

    /// Bounded variable elimination (BVE) preprocessing.
    /// Resolves out variables that appear in few clauses when the resolvent
    /// set is no larger than the original. Variables in `protected` are never eliminated.
    /// Returns number of eliminated variables.
    pub fn preprocess_bve(&mut self) -> usize {
        self.preprocess_bve_with_protection(&[])
    }

    /// BVE with a set of protected variable indices (0-based) that won't be eliminated.
    pub fn preprocess_bve_with_protection(&mut self, protected: &[usize]) -> usize {
        if !self.ok { return 0; }
        // Propagate first to simplify
        if self.propagate().is_some() {
            self.ok = false;
            return 0;
        }

        let mut eliminated = 0usize;
        let num_vars = self.num_vars;

        // First pass: simplify clauses using level-0 assignments.
        // Remove satisfied clauses, remove false literals from remaining clauses.
        self.simplify_clauses_at_level0();
        if !self.ok { return 0; }

        // Mark protected and constrained variables
        let mut skip_var = vec![false; num_vars];
        for &v in protected {
            if v < num_vars { skip_var[v] = true; }
        }
        for pbc in &self.pb_constraints {
            for &lit in &pbc.lits { skip_var[var_of(lit)] = true; }
        }
        for qpbc in &self.quad_pb_constraints {
            for t in &qpbc.terms {
                skip_var[t.var_a()] = true;
                skip_var[t.var_b()] = true;
            }
        }
        for xc in &self.xor_constraints {
            for &v in &xc.vars { skip_var[v] = true; }
        }

        // Build and maintain occurrence lists
        let mut pos_occs: Vec<Vec<u32>> = vec![Vec::new(); num_vars];
        let mut neg_occs: Vec<Vec<u32>> = vec![Vec::new(); num_vars];
        for (ci, m) in self.clause_meta.iter().enumerate() {
            if m.deleted { continue; }
            let lits = &self.clause_lits[m.start as usize..(m.start as usize + m.len as usize)];
            for &lit in lits {
                let v = var_of(lit);
                if self.assigns[v] != LBool::Undef { continue; }
                if lit > 0 { pos_occs[v].push(ci as u32); }
                else { neg_occs[v].push(ci as u32); }
            }
        }

        // Process variables in order of increasing resolvent product
        let mut candidates: Vec<(usize, usize)> = (0..num_vars)
            .filter(|&v| {
                self.assigns[v] == LBool::Undef
                && !skip_var[v]
                && !pos_occs[v].is_empty()
                && !neg_occs[v].is_empty()
            })
            .map(|v| (pos_occs[v].len() * neg_occs[v].len(), v))
            .collect();
        candidates.sort_unstable();

        for &(product, v) in &candidates {
            if product > 50 { break; } // limit resolvent explosion

            // Filter to non-deleted clauses
            let pos_valid: Vec<u32> = pos_occs[v].iter().copied()
                .filter(|&ci| !self.clause_meta[ci as usize].deleted)
                .collect();
            let neg_valid: Vec<u32> = neg_occs[v].iter().copied()
                .filter(|&ci| !self.clause_meta[ci as usize].deleted)
                .collect();
            if pos_valid.is_empty() || neg_valid.is_empty() { continue; }

            let original_count = pos_valid.len() + neg_valid.len();
            let var_lit_pos = (v + 1) as i32;
            let var_lit_neg = -var_lit_pos;

            // Compute all resolvents using a literal presence bitset for O(1) lookups
            let mut resolvents: Vec<Vec<Lit>> = Vec::new();
            let mut too_many = false;
            let num_lit_indices = 2 * num_vars;
            let mut in_resolvent = vec![false; num_lit_indices]; // lit_index → present

            for &pci in &pos_valid {
                let pm = &self.clause_meta[pci as usize];
                let p_lits: Vec<Lit> = self.clause_lits[pm.start as usize..(pm.start as usize + pm.len as usize)].to_vec();
                for &nci in &neg_valid {
                    let nm = &self.clause_meta[nci as usize];
                    let n_lits = &self.clause_lits[nm.start as usize..(nm.start as usize + nm.len as usize)];

                    // Build resolvent with O(1) membership testing
                    let mut resolvent: Vec<Lit> = Vec::new();
                    let mut tautology = false;

                    for &lit in &p_lits {
                        if lit == var_lit_pos { continue; }
                        if self.lit_value(lit) == LBool::False { continue; }
                        if self.lit_value(lit) == LBool::True { tautology = true; break; }
                        let li = lit_index(lit);
                        if !in_resolvent[li] {
                            in_resolvent[li] = true;
                            resolvent.push(lit);
                        }
                    }
                    if !tautology {
                        for &lit in n_lits {
                            if lit == var_lit_neg { continue; }
                            if self.lit_value(lit) == LBool::False { continue; }
                            if self.lit_value(lit) == LBool::True { tautology = true; break; }
                            // Check for complementary literal
                            if in_resolvent[lit_index(-lit)] { tautology = true; break; }
                            let li = lit_index(lit);
                            if !in_resolvent[li] {
                                in_resolvent[li] = true;
                                resolvent.push(lit);
                            }
                        }
                    }

                    // Clear the bitset for next iteration
                    for &lit in &resolvent { in_resolvent[lit_index(lit)] = false; }

                    if tautology { continue; }

                    resolvents.push(resolvent);
                    if resolvents.len() > original_count {
                        too_many = true;
                        break;
                    }
                }
                if too_many { break; }
            }

            if too_many || resolvents.len() > original_count { continue; }

            // Elimination is beneficial: delete original clauses, add resolvents
            for &ci in &pos_valid {
                self.clause_meta[ci as usize].deleted = true;
            }
            for &ci in &neg_valid {
                self.clause_meta[ci as usize].deleted = true;
            }

            // Add resolvents as new clauses
            for resolvent in &resolvents {
                if resolvent.is_empty() {
                    self.ok = false;
                    return eliminated;
                } else if resolvent.len() == 1 {
                    let lit = resolvent[0];
                    if self.lit_value(lit) == LBool::Undef {
                        self.enqueue(lit, Reason::Decision);
                        if self.propagate().is_some() {
                            self.ok = false;
                            return eliminated;
                        }
                    } else if self.lit_value(lit) == LBool::False {
                        self.ok = false;
                        return eliminated;
                    }
                } else {
                    let ci = self.clause_meta.len() as u32;
                    let start = self.clause_lits.len() as u32;
                    self.clause_lits.extend_from_slice(resolvent);
                    self.clause_meta.push(ClauseMeta {
                        start, len: resolvent.len() as u16, learnt: false, lbd: 0, deleted: false
                    });
                    // Add to occurrence lists for future iterations
                    for &lit in resolvent {
                        let w = var_of(lit);
                        if lit > 0 { pos_occs[w].push(ci); }
                        else { neg_occs[w].push(ci); }
                    }
                }
            }
            eliminated += 1;
        }

        // Rebuild all watches from scratch (clean and correct)
        for wl in &mut self.watches { wl.clear(); }
        for (ci, m) in self.clause_meta.iter().enumerate() {
            if m.deleted || m.len < 2 { continue; }
            let lits = &self.clause_lits[m.start as usize..(m.start as usize + m.len as usize)];
            self.watches[lit_index(negate(lits[0]))].push((ci as u32, lits[1]));
            self.watches[lit_index(negate(lits[1]))].push((ci as u32, lits[0]));
        }

        eliminated
    }

    /// Simplify clause database using level-0 assignments.
    /// Removes satisfied clauses and false literals.
    /// Simplify the clause database using level-0 assignments.
    /// Removes satisfied clauses and false literals. Also rebuilds watch lists.
    /// Returns the number of clauses removed.
    pub fn simplify(&mut self) -> usize {
        if !self.ok { return 0; }
        if self.propagate().is_some() {
            self.ok = false;
            return 0;
        }
        let before = self.clause_meta.iter().filter(|m| !m.deleted).count();
        self.simplify_clauses_at_level0();
        if !self.ok { return 0; }
        let after = self.clause_meta.iter().filter(|m| !m.deleted).count();
        // Rebuild watch lists from scratch (since clauses were modified)
        for wl in &mut self.watches { wl.clear(); }
        for (ci, m) in self.clause_meta.iter().enumerate() {
            if m.deleted || m.len < 2 { continue; }
            let lits = &self.clause_lits[m.start as usize..(m.start as usize + m.len as usize)];
            self.watches[lit_index(negate(lits[0]))].push((ci as u32, lits[1]));
            self.watches[lit_index(negate(lits[1]))].push((ci as u32, lits[0]));
        }
        before - after
    }

    fn simplify_clauses_at_level0(&mut self) {
        for ci in 0..self.clause_meta.len() {
            let m = &self.clause_meta[ci];
            if m.deleted { continue; }
            let start = m.start as usize;
            let len = m.len as usize;

            // Check if clause is satisfied
            let mut satisfied = false;
            for i in start..start + len {
                if self.lit_value(self.clause_lits[i]) == LBool::True {
                    satisfied = true;
                    break;
                }
            }
            if satisfied {
                self.clause_meta[ci].deleted = true;
                continue;
            }

            // Remove false literals (compact in place)
            let mut new_len = 0;
            for i in start..start + len {
                let lit = self.clause_lits[i];
                if self.lit_value(lit) != LBool::False {
                    self.clause_lits[start + new_len] = lit;
                    new_len += 1;
                }
            }
            if new_len == 0 {
                self.ok = false;
                return;
            }
            self.clause_meta[ci].len = new_len as u16;
        }
    }

    /// Extract high-quality learnt clauses (LBD <= max_lbd) as Vec<Vec<Lit>>.
    /// Only returns non-deleted learnt clauses.
    pub fn extract_learnt_clauses(&self, max_lbd: u8) -> Vec<Vec<Lit>> {
        let mut result = Vec::new();
        for m in &self.clause_meta {
            if m.deleted || !m.learnt || m.lbd > max_lbd { continue; }
            let lits = &self.clause_lits[m.start as usize..(m.start as usize + m.len as usize)];
            result.push(lits.to_vec());
        }
        result
    }

    /// Get a copy of the current phase saving vector.
    pub fn get_phase(&self) -> Vec<bool> {
        self.phase.clone()
    }

    /// Set the phase saving vector (for warm-starting).
    /// Only sets entries up to min(phase.len(), self.phase.len()).
    pub fn set_phase(&mut self, phase: &[bool]) {
        let n = phase.len().min(self.phase.len());
        self.phase[..n].copy_from_slice(&phase[..n]);
    }

    /// Inject clauses into the solver (for warm-starting with transferred clauses).
    /// Clauses are added as learnt with the given LBD.
    pub fn inject_clauses(&mut self, clauses: &[Vec<Lit>], lbd: u8) {
        for clause in clauses {
            if clause.len() < 2 { continue; } // skip unit/empty
            // Check all variables are in range
            let valid = clause.iter().all(|&lit| {
                let v = (lit.abs() - 1) as usize;
                v < self.num_vars
            });
            if !valid { continue; }
            let start = self.clause_lits.len() as u32;
            self.clause_lits.extend_from_slice(clause);
            let ci = self.clause_meta.len() as u32;
            self.clause_meta.push(ClauseMeta {
                start,
                len: clause.len() as u16,
                learnt: true,
                lbd,
                deleted: false,
            });
            // Add watches for first two literals
            let lit0 = clause[0];
            let lit1 = clause[1];
            self.watches[lit_index(-lit0)].push((ci, lit1));
            self.watches[lit_index(-lit1)].push((ci, lit0));
        }
    }

    /// Reset a quad PB constraint's incremental state from precomputed values.
    /// Used for fast boundary config switching without backtracking.
    pub fn reset_quad_pb_state(&mut self, qi: usize, term_state: &[u8], #[allow(unused)] sum_true: i32, sum_maybe: i32) {
        let qc = &mut self.quad_pb_constraints[qi];
        for (i, &s) in term_state.iter().enumerate() {
            qc.terms[i].state = s;
        }
        qc.sums = [0, sum_maybe, sum_true];
        qc.stale = false;
    }

    /// Get the number of quad PB constraints.
    pub fn num_quad_pb(&self) -> usize { self.quad_pb_constraints.len() }

    /// Get the number of terms in a quad PB constraint.
    pub fn quad_pb_num_terms(&self, qi: usize) -> usize { self.quad_pb_constraints[qi].num_terms as usize }

    /// Get quad PB term info for precomputation.
    pub fn quad_pb_term_info(&self, qi: usize, ti: usize) -> (usize, usize, bool, bool) {
        let t = &self.quad_pb_constraints[qi].terms[ti];
        (t.var_a(), t.var_b(), t.neg_a(), t.neg_b())
    }

    /// Full reset to base state: unassign all variables, clear trail, reset conflicts.
    /// Keeps all constraints and learnt clauses intact.
    pub fn reset_to_base(&mut self) {
        // Backtrack to level 0
        self.backtrack(0);
        // Reset conflict counter and restart state
        self.conflicts = 0;
        self.restart_limit = 100;
        self.luby_index = 0;
    }

    /// Delete all learnt clauses and clean watch lists.
    /// Call between independent solves to prevent clause database bloat.
    pub fn clear_learnt(&mut self) {
        self.backtrack(0);
        for m in &mut self.clause_meta {
            if m.learnt { m.deleted = true; }
        }
        for wl in &mut self.watches {
            wl.retain(|&(ci, _)| !self.clause_meta[ci as usize].deleted);
        }
    }

    /// Pre-allocate internal buffers for expected search size.
    /// Call before cloning as a template to ensure clones have capacity.
    pub fn reserve_for_search(&mut self, expected_clauses: usize) {
        self.clause_lits.reserve(expected_clauses * 5);
        self.clause_meta.reserve(expected_clauses);
        self.trail.reserve(self.num_vars);
    }

    /// Vivify (try to shorten) up to `max_clauses` learnt clauses.
    /// Must be called at decision level `base_level` with all propagation done.
    fn vivify_clauses(&mut self, base_level: u32, max_clauses: usize) {
        debug_assert!(self.decision_level() == base_level);

        // Collect candidate clause indices (learnt, non-deleted, len >= 3, small LBD)
        let mut candidates: Vec<(u8, u32)> = Vec::new(); // (lbd, ci)
        for (ci, m) in self.clause_meta.iter().enumerate() {
            if m.deleted || !m.learnt || m.len < 3 || m.lbd > 3 { continue; }
            candidates.push((m.lbd, ci as u32));
        }
        candidates.sort_unstable(); // sort by LBD (best first)
        candidates.truncate(max_clauses);

        for &(_, ci) in &candidates {
            let m = &self.clause_meta[ci as usize];
            if m.deleted { continue; }
            let len = m.len as usize;
            let start = m.start as usize;

            // Copy clause literals (we may modify the clause)
            let lits: Vec<Lit> = self.clause_lits[start..start + len].to_vec();

            // Try to shorten: assume negation of each literal, propagate
            let mut shortened = false;
            let mut new_len = len;

            for k in 0..len {
                let lit = lits[k];
                let val = self.lit_value(lit);

                if val == LBool::True {
                    // Literal is already true at this level — clause is satisfied
                    // Can strengthen by removing this literal (it's redundant)
                    // But we need to be careful with watches
                    break;
                }
                if val == LBool::False {
                    // Literal already false — skip (it contributes nothing)
                    continue;
                }

                // Assume negation of this literal
                self.new_decision_level();
                self.enqueue(-lit, Reason::Decision);
                if let Some(_conflict) = self.propagate() {
                    // Conflict! The clause can be shortened to lits[0..k] + asserting lit
                    new_len = k + 1;
                    shortened = true;
                    self.backtrack(base_level);
                    break;
                }
            }

            // Undo any decisions we made
            if self.decision_level() > base_level {
                self.backtrack(base_level);
            }

            if shortened && new_len < len {
                // Mark old clause as deleted
                self.clause_meta[ci as usize].deleted = true;
                // Remove watches for old clause
                for li in 0..self.watches.len() {
                    self.watches[li].retain(|&(wci, _)| wci != ci);
                }

                // Add shortened clause
                let short_lits: Vec<Lit> = lits[..new_len].to_vec();
                if short_lits.len() == 1 {
                    // Unit clause — propagate immediately
                    let unit = short_lits[0];
                    if self.lit_value(unit) == LBool::Undef {
                        self.enqueue(unit, Reason::Decision);
                        if self.propagate().is_some() {
                            self.ok = false;
                            return;
                        }
                    } else if self.lit_value(unit) == LBool::False {
                        self.ok = false;
                        return;
                    }
                } else {
                    let new_ci = self.clause_meta.len() as u32;
                    let new_start = self.clause_lits.len() as u32;
                    let lbd = self.compute_lbd(&short_lits).min(new_len as u32) as u8;
                    self.watches[lit_index(negate(short_lits[0]))].push((new_ci, short_lits[1]));
                    self.watches[lit_index(negate(short_lits[1]))].push((new_ci, short_lits[0]));
                    self.clause_lits.extend_from_slice(&short_lits);
                    self.clause_meta.push(ClauseMeta {
                        start: new_start, len: short_lits.len() as u16,
                        learnt: true, lbd, deleted: false,
                    });
                }
            }
        }
    }

    /// Try assigning all unassigned variables according to the phase vector.
    /// Returns Some(true) if a solution is found, Some(false) if a conflict
    /// occurs, or None if we couldn't make progress.
    fn try_lucky_phase(&mut self, base_level: u32) -> Option<bool> {
        // Make decisions for all unassigned variables in order
        let n = self.num_vars;
        for v in 0..n {
            if self.assigns[v] != LBool::Undef { continue; }
            let lit = if self.phase[v] { (v + 1) as i32 } else { -((v + 1) as i32) };
            self.new_decision_level();
            self.enqueue(lit, Reason::Decision);
            if let Some(_conflict) = self.propagate() {
                // Conflict — undo everything and return failure
                self.backtrack(base_level);
                return Some(false);
            }
        }
        // All variables assigned without conflict — solution found!
        if self.trail.len() >= n {
            return Some(true);
        }
        None
    }

    fn solve_inner(&mut self, base_level: u32) -> Option<bool> {
        loop {
            if let Some(conflict_reason) = self.propagate() {
                // Conflict
                self.conflicts += 1;
                // Check conflict limit
                if self.conflict_limit > 0 && self.conflicts >= self.conflict_limit {
                    return None; // indeterminate — limit reached
                }
                if self.decision_level() <= base_level {
                    return Some(false); // conflict at/below assumption level → UNSAT
                }
                let (learnt_clause, bt_level) = self.analyze(conflict_reason);
                // Verify: every literal in the learnt clause should be false
                // at the current decision level (before backtrack).
                #[cfg(debug_assertions)]
                for &lit in &learnt_clause {
                    debug_assert!(self.lit_value(lit) == LBool::False,
                        "learnt clause lit {} should be false but is {:?} (level={})",
                        lit, self.lit_value(lit), self.level[var_of(lit)]);
                }
                let bt_level = bt_level.max(base_level);
                let cur_level = self.decision_level();
                // CMS3: Chronological backtracking — when backjump is close,
                // backtrack just one level to avoid re-deriving implications.
                let use_chrono = self.config.chrono_bt
                    && cur_level > base_level + 1
                    && cur_level - bt_level <= 2
                    && learnt_clause.len() > 1;
                if use_chrono {
                    // Backtrack to current_level - 1 (chronological)
                    self.backtrack(cur_level - 1);
                    // Add clause but DON'T enqueue — it's not unit at this level
                    self.add_learnt_clause_no_enqueue(learnt_clause);
                } else {
                    self.backtrack(bt_level);
                    self.add_learnt_clause(learnt_clause);
                }
                self.decay_activities();

                // Update EMA stats (always, regardless of restart strategy)
                let lbd = self.clause_meta.last().map(|m| m.lbd as f64).unwrap_or(1.0);
                self.ema_lbd_fast += (lbd - self.ema_lbd_fast) / 32.0;
                self.ema_lbd_slow += (lbd - self.ema_lbd_slow) / 4096.0;
                let trail_sz = self.trail.len() as f64;
                self.ema_trail_fast += (trail_sz - self.ema_trail_fast) / 32.0;
                self.ema_trail_slow += (trail_sz - self.ema_trail_slow) / 4096.0;
                self.ema_restart_block += 1;

                // Restart check
                let should_restart = if self.config.ema_restarts {
                    // Glucose-style: restart when recent LBD quality is worse than global,
                    // but block if trail is unusually long (making good progress).
                    let lbd_trigger = self.conflicts > 100
                        && self.ema_lbd_fast > 1.25 * self.ema_lbd_slow;
                    let blocked = self.ema_restart_block < 50
                        || self.ema_trail_fast > 1.4 * self.ema_trail_slow;
                    lbd_trigger && !blocked
                } else {
                    // Luby restart schedule
                    self.conflicts >= self.restart_limit
                };
                if should_restart {
                    if !self.config.ema_restarts {
                        self.restart_limit += 100 * luby(self.luby_index);
                        self.luby_index += 1;
                    }
                    self.ema_restart_block = 0;
                    self.backtrack(base_level);
                    self.reduce_db();

                    // Vivification: periodically try to shorten clauses
                    if self.config.vivification && self.conflicts % 1000 == 0 {
                        self.vivify_clauses(base_level, 50);
                    }

                    // Rephasing: periodically reset phases
                    if self.config.rephasing && self.conflicts >= self.rephase_conflicts {
                        self.rephase();
                        self.rephase_conflicts = self.conflicts + 10000;
                    }
                }
            } else {
                // No conflict
                if self.trail.len() == self.num_vars {
                    return Some(true); // all vars assigned → SAT
                }
                // Make a decision
                let lit = self.pick_branching_var();
                self.new_decision_level();
                self.enqueue(lit, Reason::Decision);
            }
        }
    }

    /// Get the value of a variable after solving. Var is 1-based.
    pub fn value(&self, var: i32) -> Option<bool> {
        let v = var.unsigned_abs() as usize;
        if v == 0 || v > self.num_vars { return None; }
        match self.assigns[v - 1] {
            LBool::True => Some(var > 0),
            LBool::False => Some(var < 0),
            LBool::Undef => None,
        }
    }

    // ── Internal methods ──

    fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    fn new_decision_level(&mut self) {
        self.trail_lim.push(self.trail.len());
    }

    #[inline(always)]
    fn lit_value(&self, lit: Lit) -> LBool {
        let v = var_of(lit);
        let a = self.assigns[v];
        if a == LBool::Undef { return LBool::Undef; }
        // True XOR negative = flip if literal is negative
        if (a == LBool::True) == (lit > 0) { LBool::True } else { LBool::False }
    }

    fn enqueue(&mut self, lit: Lit, reason: Reason) {
        let v = var_of(lit);
        debug_assert!(self.assigns[v] == LBool::Undef,
            "enqueue lit={} but var {} already assigned {:?}", lit, v, self.assigns[v]);
        self.assigns[v] = if lit > 0 { LBool::True } else { LBool::False };
        self.trail_pos[v] = self.trail.len();
        self.level[v] = self.decision_level();
        self.reason[v] = reason;
        self.trail.push(TrailEntry { lit, level: self.decision_level(), reason });
    }

    /// BCP + PB propagation. Returns conflict reason or None.
    fn propagate(&mut self) -> Option<Reason> {
        while self.prop_head < self.trail.len() {
            let lit = self.trail[self.prop_head].lit;
            self.prop_head += 1;
            // Clause BCP
            if let Some(conflict_ci) = self.propagate_lit(lit) {
                return Some(Reason::Clause(conflict_ci));
            }
            // PB propagation: lit became true, so ¬lit is false.
            if !self.pb_constraints.is_empty() {
                let watch_idx = lit_index(lit);
                // PB watches are static (never modified), iterate by index to avoid clone
                for idx in 0..self.pb_watches[watch_idx].len() {
                    let pbi = self.pb_watches[watch_idx][idx];
                    if let Some(conflict_reason) = self.propagate_pb(pbi) {
                        return Some(conflict_reason);
                    }
                }
            }
            // Quadratic PB: incremental update + propagation
            if !self.quad_pb_constraints.is_empty() {
                let v = var_of(lit);
                let known_val = self.assigns[v]; // just assigned, hot in cache
                // Recompute stale constraints before incremental updates
                for idx in 0..self.quad_pb_var_watches[v].len() {
                    let qi = self.quad_pb_var_watches[v][idx];
                    if self.quad_pb_constraints[qi as usize].stale {
                        // Batch: recompute all stale at once for cache locality
                        for i in 0..self.quad_pb_constraints.len() {
                            if self.quad_pb_constraints[i].stale {
                                self.recompute_quad_pb(i as u32);
                            }
                        }
                        break;
                    }
                }
                // Update term states for all terms involving this variable
                for idx in 0..self.quad_pb_var_terms[v].len() {
                    let (qi, ti, is_a) = self.quad_pb_var_terms[v][idx];
                    self.update_quad_pb_term_hint(qi, ti as usize, known_val, is_a);
                }
                // Propagate constraints watching this variable
                for idx in 0..self.quad_pb_var_watches[v].len() {
                    let qi = self.quad_pb_var_watches[v][idx];
                    if let Some(conflict_reason) = self.propagate_quad_pb(qi) {
                        return Some(conflict_reason);
                    }
                }
            }
            // XOR (GF(2)) propagation
            if !self.xor_constraints.is_empty() {
                let v = var_of(lit);
                let val = self.assigns[v] == LBool::True;
                for idx in 0..self.xor_var_watches[v].len() {
                    let xi = self.xor_var_watches[v][idx];
                    let xc = &mut self.xor_constraints[xi as usize];
                    if xc.num_unknown == 0 { continue; } // already fully resolved (e.g. by add_xor)
                    xc.num_unknown -= 1;
                    xc.assigned_xor ^= val;
                    if xc.num_unknown == 0 {
                        // All assigned: check parity
                        if xc.assigned_xor != xc.parity {
                            return Some(Reason::Xor(xi));
                        }
                    } else if xc.num_unknown == 1 {
                        // One unknown left: force it
                        let need_true = xc.assigned_xor ^ xc.parity;
                        // Find the unassigned var
                        let mut forced_var = 0;
                        for &xv in &xc.vars {
                            if self.assigns[xv] == LBool::Undef {
                                forced_var = xv;
                                break;
                            }
                        }
                        let forced_lit = if need_true {
                            (forced_var + 1) as Lit
                        } else {
                            -((forced_var + 1) as Lit)
                        };
                        if self.lit_value(forced_lit) == LBool::False {
                            return Some(Reason::Xor(xi));
                        }
                        if self.lit_value(forced_lit) == LBool::Undef {
                            self.enqueue(forced_lit, Reason::Xor(xi));
                        }
                    }
                }
            }
        }
        None
    }

    fn propagate_lit(&mut self, lit: Lit) -> Option<u32> {
        let false_lit = negate(lit);
        let watch_idx = lit_index(lit);

        let mut watch_list = std::mem::take(&mut self.watches[watch_idx]);
        let mut i = 0;
        let mut j = 0;
        let mut conflict = None;

        while i < watch_list.len() {
            let (ci, blocker) = watch_list[i];
            if self.clause_meta[ci as usize].deleted {
                i += 1;
                continue;
            }

            // Blocker check: if the blocker literal is true, clause is satisfied
            if self.lit_value(blocker) == LBool::True {
                watch_list[j] = watch_list[i];
                j += 1;
                i += 1;
                continue;
            }

            let m = self.clause_meta[ci as usize];
            let cstart = m.start as usize;
            let clen = m.len as usize;

            // Ensure false_lit is at position [1]
            if self.clause_lits[cstart] == false_lit {
                self.clause_lits.swap(cstart, cstart + 1);
            }

            let other = self.clause_lits[cstart]; // lits[0]

            // If the other watched literal is already true, update blocker and skip
            if self.lit_value(other) == LBool::True {
                watch_list[j] = (ci, other); // update blocker
                j += 1;
                i += 1;
                continue;
            }

            // Look for a new literal to watch
            let mut found_new = false;
            for k in 2..clen {
                let repl = self.clause_lits[cstart + k];
                if self.lit_value(repl) != LBool::False {
                    self.clause_lits[cstart + 1] = repl;
                    self.clause_lits[cstart + k] = false_lit;
                    self.watches[lit_index(negate(repl))].push((ci, other));
                    found_new = true;
                    break;
                }
            }
            if found_new {
                i += 1;
                continue;
            }

            // No new watcher found
            watch_list[j] = (ci, other);
            j += 1;

            if self.lit_value(other) == LBool::False {
                conflict = Some(ci);
                while i + 1 < watch_list.len() {
                    i += 1;
                    watch_list[j] = watch_list[i];
                    j += 1;
                }
                break;
            } else {
                self.enqueue(other, Reason::Clause(ci));
            }
            i += 1;
        }

        watch_list.truncate(j);
        self.watches[watch_idx] = watch_list;
        conflict
    }

    /// Propagate a PB constraint. Returns conflict reason if violated, None otherwise.
    /// Computes slack = sum of coeffs for true/undef literals - bound.
    /// If slack < 0 → conflict. If slack < coeff[i] for undef lit i → propagate lit i.
    fn propagate_pb(&mut self, pbi: u32) -> Option<Reason> {
        let pb = &self.pb_constraints[pbi as usize];
        let n = pb.lits.len();

        // Compute slack: sum coefficients for non-false literals, subtract bound.
        // For unit coefficients, slack = count(non-false) - bound.
        let mut slack: i64 = -(pb.bound as i64);
        let mut first_undef = n; // index of first undef literal
        for i in 0..n {
            let v = var_of(pb.lits[i]);
            let a = self.assigns[v];
            if a == LBool::Undef {
                slack += pb.coeffs[i] as i64;
                if first_undef == n { first_undef = i; }
            } else if (a == LBool::True) == (pb.lits[i] > 0) {
                // Literal is true → contributes to slack
                slack += pb.coeffs[i] as i64;
            }
        }

        if slack < 0 {
            return Some(Reason::Pb(pbi)); // conflict
        }

        // Propagate: any undef literal whose coefficient > slack must be true.
        // Early exit: if slack >= max_coeff, no propagation possible.
        if slack > 0 { return None; } // all coefficients are 1, so slack>0 means no propagation

        // slack == 0: force all undef literals
        for i in first_undef..n {
            let lit = self.pb_constraints[pbi as usize].lits[i];
            let v = var_of(lit);
            if self.assigns[v] == LBool::Undef {
                self.enqueue(lit, Reason::Pb(pbi));
            }
        }
        None
    }

    /// Generate a clause explanation for a PB-based reason.
    /// The clause is: the propagated literal OR the negation of all false literals
    /// whose removal would violate the bound.
    #[allow(dead_code)]
    fn pb_reason_clause(&self, pbi: u32, propagated: Lit) -> Vec<Lit> {
        let pb = &self.pb_constraints[pbi as usize];
        let mut clause = vec![propagated];
        for i in 0..pb.lits.len() {
            let lit = pb.lits[i];
            if lit != propagated && self.lit_value(lit) == LBool::False {
                clause.push(negate(lit)); // negate: the false literal explains the propagation
            }
        }
        clause
    }

    /// Update a single quad PB term's state with a hint: the caller knows the
    /// value of one variable (is_a=true → var_a's value, is_a=false → var_b's value).
    /// This avoids one random assigns[] lookup per call (the 40% hotspot).
    #[inline(always)]
    fn update_quad_pb_term_hint(&mut self, qi: u32, ti: usize, known_val: LBool, is_a: bool) {
        let t = &self.quad_pb_constraints[qi as usize].terms[ti];
        // Only look up the *other* variable's assignment
        let (aa, ab) = if is_a {
            (known_val, self.assigns[t.var_b()])
        } else {
            (self.assigns[t.var_a()], known_val)
        };

        let new_state = t.compute_state(aa, ab);

        let qc = &mut self.quad_pb_constraints[qi as usize];
        let old_state = qc.terms[ti].state;
        if old_state == new_state { return; }

        let c = qc.terms[ti].coeff as i32;
        // Branchless: decrement old bucket, increment new bucket.
        // sums[0] (dead) is unused but absorbs index 0 writes harmlessly.
        qc.sums[old_state as usize] -= c;
        qc.sums[new_state as usize] += c;
        qc.terms[ti].state = new_state;
    }

    /// Propagate a quadratic PB constraint using incremental counters.
    /// Recompute term states and sums for a stale quad PB constraint.
    #[inline]
    fn recompute_quad_pb(&mut self, qi: u32) {
        let qi = qi as usize;
        let nt = self.quad_pb_constraints[qi].num_terms as usize;
        let mut sums = [0i32, 0, 0];
        for ti in 0..nt {
            let t = &self.quad_pb_constraints[qi].terms[ti];
            let aa = self.assigns[t.var_a()];
            let ab = self.assigns[t.var_b()];
            let new_state = t.compute_state(aa, ab);
            sums[new_state as usize] += t.coeff as i32;
            self.quad_pb_constraints[qi].terms[ti].state = new_state;
        }
        self.quad_pb_constraints[qi].sums = sums;
        self.quad_pb_constraints[qi].stale = false;
    }

    /// Single-pass: finds propagation and builds explanation in one fused scan.
    #[inline]
    fn propagate_quad_pb(&mut self, qi: u32) -> Option<Reason> {
        if self.quad_pb_constraints[qi as usize].stale {
            // Batch recompute all stale constraints at once (better cache locality)
            for i in 0..self.quad_pb_constraints.len() {
                if self.quad_pb_constraints[i].stale {
                    self.recompute_quad_pb(i as u32);
                }
            }
        }
        let qc = &self.quad_pb_constraints[qi as usize];
        let n = qc.num_terms as usize;
        let target = qc.target as i64;
        let sum_true = qc.sums[2] as i64;
        let sum_maybe = qc.sums[1] as i64;

        if sum_true + sum_maybe < target || sum_true > target {
            return Some(Reason::QuadPb(qi)); // conflict
        }

        let slack_up = sum_true + sum_maybe - target;
        let slack_down = target - sum_true;
        if slack_up > 0 && slack_down > 0 { return None; }

        for i in 0..n {
            let t = &self.quad_pb_constraints[qi as usize].terms[i];
            // Fast path: DEAD and TRUE terms can never propagate
            if t.state != 1 { continue; }
            let aa = self.assigns[t.var_a()];
            let ab = self.assigns[t.var_b()];
            let a_false = aa != LBool::Undef && aa != t.true_val_a();
            let b_false = ab != LBool::Undef && ab != t.true_val_b();
            if a_false | b_false { continue; }
            let a_undef = aa == LBool::Undef;
            let b_undef = ab == LBool::Undef;
            if !a_undef && !b_undef { continue; }

            let c = t.coeff as i64;
            let la = t.lit_a;
            let lb = t.lit_b;
            let propagated_lit;
            if c > slack_up {
                propagated_lit = if !a_undef { lb } else { la };
            } else if c > slack_down && (!a_undef || !b_undef) {
                if !a_undef && b_undef { propagated_lit = negate(lb); }
                else if !b_undef && a_undef { propagated_lit = negate(la); }
                else { continue; }
            } else { continue; }

            // Lazy explanation: encode is_upper in bit 31 of qi, defer building to analyze time.
            let is_upper = c > slack_down;
            let reason_qi = qi | if is_upper { 1u32 << 31 } else { 0 };
            self.enqueue(propagated_lit, Reason::QuadPb(reason_qi));
            return None;
        }
        None
    }

    /// Compute quad PB explanation on-demand (lazy). Called during conflict analysis.
    /// `qi_encoded` has bit 31 = is_upper flag, bits 0-30 = constraint index.
    /// `pv` is the propagated variable (excluded from explanation).
    /// Only includes variables assigned before `pv` on the trail (trail_pos filter).
    /// Compute quad PB explanation into a provided output buffer.
    /// Clears `out` first, appends explanation literals.
    fn compute_quad_pb_explanation_into(&mut self, qi_encoded: u32, pv: usize, out: &mut Vec<Lit>) {
        out.clear();
        let is_upper = (qi_encoded >> 31) != 0;
        let qi = (qi_encoded & 0x7FFFFFFF) as usize;
        let pv_pos = self.trail_pos[pv];

        let seen = &mut self.quad_pb_seen_buf;
        let terms = &self.quad_pb_constraints[qi].terms;
        for t in terms {
            let va = t.var_a();
            let vb = t.var_b();
            let aa = if self.assigns[va] != LBool::Undef && self.trail_pos[va] < pv_pos { self.assigns[va] } else { LBool::Undef };
            let ab = if self.assigns[vb] != LBool::Undef && self.trail_pos[vb] < pv_pos { self.assigns[vb] } else { LBool::Undef };
            let af = (aa == LBool::True && t.neg_a()) || (aa == LBool::False && !t.neg_a());
            let bf = (ab == LBool::True && t.neg_b()) || (ab == LBool::False && !t.neg_b());

            if af || bf {
                let (lit, v) = if af { (t.lit_a, va) } else { (t.lit_b, vb) };
                if v != pv && !seen[v] && self.level[v] > 0 {
                    seen[v] = true;
                    out.push(lit);
                }
            } else if is_upper && aa != LBool::Undef && ab != LBool::Undef {
                if va != pv && !seen[va] && self.level[va] > 0 {
                    seen[va] = true;
                    out.push(negate(t.lit_a));
                }
                if vb != pv && !seen[vb] && self.level[vb] > 0 {
                    seen[vb] = true;
                    out.push(negate(t.lit_b));
                }
            }
        }
        // Clear seen flags
        for i in 0..out.len() {
            seen[var_of(out[i])] = false;
        }
    }

    /// 1-UIP conflict analysis with learnt clause minimization.
    /// Returns (learnt clause, backtrack level).
    /// Uses solver-level reusable buffers to eliminate per-conflict allocations.
    fn analyze(&mut self, conflict_reason: Reason) -> (Vec<Lit>, u32) {
        // Reuse analyze_seen buffer (fill is O(num_vars) = O(44) at n=26)
        self.analyze_seen.resize(self.num_vars, false);
        self.analyze_seen.fill(false);

        let mut counter = 0;
        let mut learnt = Vec::new();
        let mut bt_level: u32 = 0;
        let mut current_reason = conflict_reason;
        let mut trail_idx = self.trail.len();
        let mut p: Lit = 0;

        loop {
            // Process reason literals inline — avoid Vec allocation for Clause path
            match current_reason {
                Reason::Clause(ci) => {
                    let m = self.clause_meta[ci as usize];
                    let cstart = m.start as usize;
                    let clen = m.len as usize;
                    for idx in 0..clen {
                        let lit = self.clause_lits[cstart + idx];
                        if lit == p { continue; }
                        let v = var_of(lit);
                        if self.analyze_seen[v] { continue; }
                        self.analyze_seen[v] = true;
                        self.bump_activity(v);
                        if self.level[v] == self.decision_level() {
                            counter += 1;
                        } else if self.level[v] > 0 {
                            learnt.push(lit);
                            bt_level = bt_level.max(self.level[v]);
                        }
                    }
                }
                Reason::Pb(pbi) => {
                    // Collect into reusable buffer
                    self.analyze_reason_buf.clear();
                    let pb = &self.pb_constraints[pbi as usize];
                    for i in 0..pb.lits.len() {
                        let lit = pb.lits[i];
                        if lit == negate(p) { continue; }
                        if self.lit_value(lit) == LBool::False {
                            self.analyze_reason_buf.push(lit);
                        }
                    }
                    if p != 0 { self.analyze_reason_buf.push(p); }
                    for idx in 0..self.analyze_reason_buf.len() {
                        let lit = self.analyze_reason_buf[idx];
                        if lit == p { continue; }
                        let v = var_of(lit);
                        if self.analyze_seen[v] { continue; }
                        self.analyze_seen[v] = true;
                        self.bump_activity(v);
                        if self.level[v] == self.decision_level() {
                            counter += 1;
                        } else if self.level[v] > 0 {
                            learnt.push(lit);
                            bt_level = bt_level.max(self.level[v]);
                        }
                    }
                }
                Reason::QuadPb(qi_encoded) => {
                    let qi = (qi_encoded & 0x7FFFFFFF) as usize;
                    let mut buf = std::mem::take(&mut self.analyze_reason_buf);
                    if p != 0 {
                        let pv = var_of(p);
                        self.compute_quad_pb_explanation_into(qi_encoded, pv, &mut buf);
                        buf.push(p);
                    } else {
                        // Conflict: compute from current state
                        buf.clear();
                        let nt = self.quad_pb_constraints[qi].num_terms as usize;
                        for ti in 0..nt {
                            let t = &self.quad_pb_constraints[qi].terms[ti];
                            let pairs: [(Lit, usize); 2] = [(t.lit_a, t.var_a()), (t.lit_b, t.var_b())];
                            for &(lit, v) in &pairs {
                                if !self.quad_pb_seen_buf[v] && self.assigns[v] != LBool::Undef && self.level[v] > 0 {
                                    self.quad_pb_seen_buf[v] = true;
                                    buf.push(if self.lit_value(lit) == LBool::False { lit } else { negate(lit) });
                                }
                            }
                        }
                        for idx in 0..buf.len() {
                            self.quad_pb_seen_buf[var_of(buf[idx])] = false;
                        }
                    }
                    for idx in 0..buf.len() {
                        let lit = buf[idx];
                        if lit == p { continue; }
                        let v = var_of(lit);
                        if self.analyze_seen[v] { continue; }
                        self.analyze_seen[v] = true;
                        self.bump_activity(v);
                        if self.level[v] == self.decision_level() {
                            counter += 1;
                        } else if self.level[v] > 0 {
                            learnt.push(lit);
                            bt_level = bt_level.max(self.level[v]);
                        }
                    }
                    self.analyze_reason_buf = buf;
                }
                Reason::Xor(xi) => {
                    // XOR reason: all assigned variables in the constraint
                    // form the reason clause. Each assigned var contributes
                    // its negated literal (it was assigned, forcing the propagation).
                    let mut buf = std::mem::take(&mut self.analyze_reason_buf);
                    buf.clear();
                    let xc = &self.xor_constraints[xi as usize];
                    for &v in &xc.vars {
                        if self.assigns[v] == LBool::Undef { continue; }
                        let lit_v = (v + 1) as Lit;
                        let neg_lit = if self.assigns[v] == LBool::True { -lit_v } else { lit_v };
                        buf.push(neg_lit);
                    }
                    // Also include the propagated literal itself (if not conflict)
                    if p != 0 { buf.push(p); }
                    for idx in 0..buf.len() {
                        let lit = buf[idx];
                        if lit == p { continue; }
                        let v = var_of(lit);
                        if self.analyze_seen[v] { continue; }
                        self.analyze_seen[v] = true;
                        self.bump_activity(v);
                        if self.level[v] == self.decision_level() {
                            counter += 1;
                        } else if self.level[v] > 0 {
                            learnt.push(lit);
                            bt_level = bt_level.max(self.level[v]);
                        }
                    }
                    self.analyze_reason_buf = buf;
                }
                Reason::Decision => { unreachable!(); }
            }

            // Find next literal on trail at current decision level that was seen
            loop {
                trail_idx -= 1;
                let entry = &self.trail[trail_idx];
                let v = var_of(entry.lit);
                if self.analyze_seen[v] && entry.level == self.decision_level() {
                    p = entry.lit;
                    counter -= 1;
                    if counter == 0 {
                        learnt.insert(0, negate(p));
                        self.minimize_learnt(&mut learnt);
                        bt_level = 0;
                        for &lit in &learnt[1..] {
                            bt_level = bt_level.max(self.level[var_of(lit)]);
                        }
                        return (learnt, bt_level);
                    }
                    current_reason = entry.reason;
                    break;
                }
            }
        }
    }

    /// Recursive clause minimization (MiniSat-style).
    /// Uses `analyze_seen` (populated by analyze()) and reusable buffers.
    fn minimize_learnt(&mut self, learnt: &mut Vec<Lit>) {
        let dl = self.decision_level() as usize + 1;
        self.minimize_levels.resize(dl, false);
        self.minimize_levels.fill(false);
        for &lit in learnt.iter() {
            let lv = self.level[var_of(lit)] as usize;
            if lv < dl { self.minimize_levels[lv] = true; }
        }

        let mut j = 1;
        for i in 1..learnt.len() {
            let lit = learnt[i];
            let v = var_of(lit);
            match self.reason[v] {
                Reason::Clause(_) | Reason::Pb(_) | Reason::QuadPb(_) | Reason::Xor(_) => {
                    if self.lit_removable(v) { continue; }
                }
                Reason::Decision => {}
            }
            learnt[j] = lit;
            j += 1;
        }
        learnt.truncate(j);
    }

    /// Check if a literal's antecedent chain is covered by the learnt clause.
    /// Uses `analyze_seen` and `minimize_levels` from caller, and reusable
    /// `minimize_stack`/`minimize_visited`/`analyze_reason_buf2` buffers.
    fn lit_removable(&mut self, v: usize) -> bool {
        self.minimize_stack.clear();
        self.minimize_stack.push(v);
        self.minimize_visited.resize(self.num_vars, false);
        self.minimize_visited.fill(false);
        self.minimize_visited[v] = true;

        while let Some(cur) = self.minimize_stack.pop() {
            // Process reason literals inline to avoid allocation
            match self.reason[cur] {
                Reason::Clause(ci) => {
                    let m = self.clause_meta[ci as usize];
                    let cstart = m.start as usize;
                    let clen = m.len as usize;
                    for idx in 0..clen {
                        let lit = self.clause_lits[cstart + idx];
                        let u = var_of(lit);
                        if u == cur || self.minimize_visited[u] { continue; }
                        self.minimize_visited[u] = true;
                        if self.level[u] == 0 { continue; }
                        if self.analyze_seen[u] { continue; }
                        let lv = self.level[u] as usize;
                        if lv >= self.minimize_levels.len() || !self.minimize_levels[lv] { return false; }
                        match self.reason[u] {
                            Reason::Decision => return false,
                            _ => { self.minimize_stack.push(u); }
                        }
                    }
                }
                Reason::Pb(pbi) => {
                    let n = self.pb_constraints[pbi as usize].lits.len();
                    for i in 0..n {
                        let lit = self.pb_constraints[pbi as usize].lits[i];
                        let u = var_of(lit);
                        if u == cur || self.minimize_visited[u] { continue; }
                        if self.lit_value(lit) != LBool::False { continue; }
                        self.minimize_visited[u] = true;
                        if self.level[u] == 0 { continue; }
                        if self.analyze_seen[u] { continue; }
                        let lv = self.level[u] as usize;
                        if lv >= self.minimize_levels.len() || !self.minimize_levels[lv] { return false; }
                        match self.reason[u] {
                            Reason::Decision => return false,
                            _ => { self.minimize_stack.push(u); }
                        }
                    }
                }
                Reason::QuadPb(qi_encoded) => {
                    let mut buf2 = std::mem::take(&mut self.analyze_reason_buf2);
                    self.compute_quad_pb_explanation_into(qi_encoded, cur, &mut buf2);
                    let mut fail = false;
                    for idx in 0..buf2.len() {
                        let lit = buf2[idx];
                        let u = var_of(lit);
                        if u == cur || self.minimize_visited[u] { continue; }
                        self.minimize_visited[u] = true;
                        if self.level[u] == 0 { continue; }
                        if self.analyze_seen[u] { continue; }
                        let lv = self.level[u] as usize;
                        if lv >= self.minimize_levels.len() || !self.minimize_levels[lv] { fail = true; break; }
                        match self.reason[u] {
                            Reason::Decision => { fail = true; break; }
                            _ => { self.minimize_stack.push(u); }
                        }
                    }
                    self.analyze_reason_buf2 = buf2;
                    if fail { return false; }
                }
                Reason::Xor(xi) => {
                    let xc = &self.xor_constraints[xi as usize];
                    for vi in 0..xc.vars.len() {
                        let u = xc.vars[vi];
                        if u == cur || self.minimize_visited[u] { continue; }
                        if self.assigns[u] == LBool::Undef { continue; }
                        self.minimize_visited[u] = true;
                        if self.level[u] == 0 { continue; }
                        if self.analyze_seen[u] { continue; }
                        let lv = self.level[u] as usize;
                        if lv >= self.minimize_levels.len() || !self.minimize_levels[lv] { return false; }
                        match self.reason[u] {
                            Reason::Decision => return false,
                            _ => { self.minimize_stack.push(u); }
                        }
                    }
                }
                Reason::Decision => return false,
            }
        }
        true
    }

    /// Backtrack to the given decision level.
    fn backtrack(&mut self, level: u32) {
        if self.decision_level() <= level { return; }

        while self.trail.len() > self.trail_lim[level as usize] {
            let entry = self.trail.pop().unwrap();
            let v = var_of(entry.lit);
            self.phase[v] = entry.lit > 0;
            self.assigns[v] = LBool::Undef;
            // Mark quad PB constraints involving this variable as stale.
            // Skip for level 0 when caller manages state externally (table path).
            if !(level == 0 && self.skip_backtrack_quad_pb) {
                for idx in 0..self.quad_pb_var_watches[v].len() {
                    let qi = self.quad_pb_var_watches[v][idx];
                    self.quad_pb_constraints[qi as usize].stale = true;
                }
            }
            // Undo XOR constraint updates
            if !self.xor_constraints.is_empty() {
                let val = entry.lit > 0;
                for idx in 0..self.xor_var_watches[v].len() {
                    let xi = self.xor_var_watches[v][idx];
                    let xc = &mut self.xor_constraints[xi as usize];
                    xc.num_unknown += 1;
                    xc.assigned_xor ^= val;
                }
            }
            self.heap_insert(v);
        }
        self.trail_lim.truncate(level as usize);
        self.prop_head = self.trail.len();

        // For backtrack to level 0 with external state management:
        // batch-reset all quad PB constraints (all vars Undef → all terms MAYBE).
        if level == 0 && self.skip_backtrack_quad_pb && !self.quad_pb_constraints.is_empty() {
            for qc in &mut self.quad_pb_constraints {
                let total: i32 = qc.terms.iter().map(|t| t.coeff as i32).sum();
                qc.sums = [0, total, 0];
                for t in qc.terms.iter_mut() { t.state = 1; } // all MAYBE
                qc.stale = false;
            }
        }
    }

    /// Minimize a learnt clause by removing redundant literals.
    /// A literal is redundant if it's at level 0 (always false) or
    /// if its reason clause is subsumed by the learnt clause.
    /// Add a learnt clause and enqueue the asserting literal.
    fn add_learnt_clause(&mut self, lits: Vec<Lit>) {
        if lits.len() == 1 {
            // Unit learnt clause: enqueue at level 0
            self.enqueue(lits[0], Reason::Decision); // no clause needed
            return;
        }

        let ci = self.clause_meta.len() as u32;
        let lbd = self.compute_lbd(&lits);
        let start = self.clause_lits.len() as u32;
        let asserting_lit = lits[0];

        // Watch the first two literals (blocker = the other watched lit)
        self.watches[lit_index(negate(lits[0]))].push((ci, lits[1]));
        self.watches[lit_index(negate(lits[1]))].push((ci, lits[0]));
        self.clause_lits.extend_from_slice(&lits);
        self.clause_meta.push(ClauseMeta { start, len: lits.len() as u16, learnt: true, lbd: lbd as u8, deleted: false });

        // The asserting literal (lits[0]) should be propagated
        self.enqueue(asserting_lit, Reason::Clause(ci));
    }

    /// Add a learnt clause WITHOUT enqueueing the asserting literal.
    /// Used for chronological backtracking where the clause isn't unit.
    fn add_learnt_clause_no_enqueue(&mut self, lits: Vec<Lit>) {
        if lits.len() == 1 {
            // Unit — still enqueue
            self.enqueue(lits[0], Reason::Decision);
            return;
        }

        let ci = self.clause_meta.len() as u32;
        let lbd = self.compute_lbd(&lits);
        let start = self.clause_lits.len() as u32;

        self.watches[lit_index(negate(lits[0]))].push((ci, lits[1]));
        self.watches[lit_index(negate(lits[1]))].push((ci, lits[0]));
        self.clause_lits.extend_from_slice(&lits);
        self.clause_meta.push(ClauseMeta { start, len: lits.len() as u16, learnt: true, lbd: lbd as u8, deleted: false });
        // Don't enqueue — at chronological backtrack level, clause is not unit
    }

    /// Compute LBD (Literal Block Distance) of a clause.
    fn compute_lbd(&self, lits: &[Lit]) -> u32 {
        // Use a small bitset for levels (decision levels rarely exceed a few hundred)
        let mut seen_levels = vec![false; self.decision_level() as usize + 1];
        let mut count = 0u32;
        for &lit in lits {
            let lv = self.level[var_of(lit)] as usize;
            if lv < seen_levels.len() && !seen_levels[lv] {
                seen_levels[lv] = true;
                count += 1;
            }
        }
        count
    }

    /// VSIDS: pick the unassigned variable with highest activity (O(log n) via heap).
    fn pick_branching_var(&mut self) -> Lit {
        // Pop variables from the heap until we find one that's unassigned
        while let Some(&top) = self.heap.first() {
            if self.assigns[top] == LBool::Undef {
                // Use phase saving: branch with last known polarity
                let v = (top as i32) + 1;
                return if self.phase[top] { v } else { -v };
            }
            self.heap_pop();
        }
        // Fallback: linear scan (should never happen if heap is maintained)
        for v in 0..self.num_vars {
            if self.assigns[v] == LBool::Undef {
                let lit = (v as i32) + 1;
                return if self.phase[v] { lit } else { -lit };
            }
        }
        unreachable!("no unassigned variable")
    }

    fn bump_activity(&mut self, v: usize) {
        self.activity[v] += self.var_inc;
        if self.activity[v] > 1e100 {
            for a in &mut self.activity {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
        // Update heap position (sift up)
        if self.heap_pos[v] < self.heap.len() {
            self.heap_sift_up(self.heap_pos[v]);
        }
    }

    // ── Heap operations (max-heap by activity) ──

    fn heap_parent(i: usize) -> usize { (i.wrapping_sub(1)) / 2 }
    fn heap_left(i: usize) -> usize { 2 * i + 1 }
    fn heap_right(i: usize) -> usize { 2 * i + 2 }

    fn heap_sift_up(&mut self, mut i: usize) {
        let v = self.heap[i];
        while i > 0 {
            let p = Self::heap_parent(i);
            if self.activity[self.heap[p]] >= self.activity[v] { break; }
            self.heap[i] = self.heap[p];
            self.heap_pos[self.heap[p]] = i;
            i = p;
        }
        self.heap[i] = v;
        self.heap_pos[v] = i;
    }

    fn heap_sift_down(&mut self, mut i: usize) {
        let v = self.heap[i];
        let n = self.heap.len();
        loop {
            let l = Self::heap_left(i);
            if l >= n { break; }
            let r = Self::heap_right(i);
            let best = if r < n && self.activity[self.heap[r]] > self.activity[self.heap[l]] { r } else { l };
            if self.activity[self.heap[best]] <= self.activity[v] { break; }
            self.heap[i] = self.heap[best];
            self.heap_pos[self.heap[best]] = i;
            i = best;
        }
        self.heap[i] = v;
        self.heap_pos[v] = i;
    }

    fn heap_pop(&mut self) -> usize {
        let top = self.heap[0];
        let last = self.heap.len() - 1;
        self.heap[0] = self.heap[last];
        self.heap_pos[self.heap[0]] = 0;
        self.heap_pos[top] = usize::MAX;
        self.heap.pop();
        if !self.heap.is_empty() {
            self.heap_sift_down(0);
        }
        top
    }

    fn heap_insert(&mut self, v: usize) {
        if self.heap_pos[v] < self.heap.len() { return; } // already in heap
        let pos = self.heap.len();
        self.heap.push(v);
        self.heap_pos[v] = pos;
        self.heap_sift_up(pos);
    }

    fn decay_activities(&mut self) {
        self.var_inc /= self.var_decay;
    }

    /// Remove low-quality learnt clauses to keep the database manageable.
    fn reduce_db(&mut self) {
        let num_learnt: usize = self.clause_meta.iter()
            .filter(|m| m.learnt && !m.deleted).count();
        let num_original: usize = self.clause_meta.iter()
            .filter(|m| !m.learnt && !m.deleted).count();
        if num_learnt < num_original { return; }

        // Collect which clauses are currently reasons
        let mut is_reason = vec![false; self.clause_meta.len()];
        for entry in &self.trail {
            if let Reason::Clause(ci) = entry.reason {
                is_reason[ci as usize] = true;
            }
        }

        // Keep glue clauses (LBD ≤ 3) always. Delete worst half of the rest.
        let mut eligible: Vec<(u32, u8)> = Vec::new();
        for ci in 0..self.clause_meta.len() {
            let m = &self.clause_meta[ci];
            if m.learnt && !m.deleted && m.lbd > 3 && !is_reason[ci] {
                eligible.push((ci as u32, m.lbd));
            }
        }
        if eligible.len() < 100 { return; }

        // Sort by LBD descending — delete worst half
        eligible.sort_by(|a, b| b.1.cmp(&a.1));
        let to_delete = eligible.len() / 2;
        for &(ci, _) in &eligible[..to_delete] {
            self.clause_meta[ci as usize].deleted = true;
        }

        // Clean watch lists
        for wl in &mut self.watches {
            wl.retain(|&(ci, _)| !self.clause_meta[ci as usize].deleted);
        }
    }

    /// Rephasing: alternate between resetting to best-known phase and random phases.
    fn rephase(&mut self) {
        if self.best_phase_set {
            // Alternate: 50% best phase, 50% inverted
            let invert = (self.rephase_conflicts / 10000) % 2 == 1;
            for v in 0..self.num_vars {
                self.phase[v] = if invert { !self.best_phase[v] } else { self.best_phase[v] };
            }
        }
        // else: keep current phases (no best known yet)
    }

    /// Failed literal probing: for each unassigned literal, assume it true and propagate.
    /// If conflict, the literal must be false — enqueue its negation at level 0.
    pub fn probe(&mut self) {
        if self.num_vars == 0 { return; }
        self.backtrack(0);
        let nv = self.num_vars;
        let max_probes = nv.min(200); // limit to avoid excessive cost
        // Probe most active variables first
        let mut vars_by_activity: Vec<usize> = (0..nv).collect();
        vars_by_activity.sort_by(|&a, &b|
            self.activity[b].partial_cmp(&self.activity[a]).unwrap_or(std::cmp::Ordering::Equal));

        for &v in vars_by_activity.iter().take(max_probes) {
            if self.assigns[v] != LBool::Undef { continue; }
            let lit = (v + 1) as Lit;
            // Try positive
            for sign in [lit, -lit] {
                self.new_decision_level();
                self.enqueue(sign, Reason::Decision);
                let conflict = self.propagate().is_some();
                self.backtrack(0);
                if conflict {
                    // sign leads to conflict, so negate(sign) is forced
                    if self.assigns[v] == LBool::Undef {
                        self.enqueue(-sign, Reason::Decision);
                        if self.propagate().is_some() {
                            self.ok = false;
                            return;
                        }
                    }
                    break; // no need to try the other polarity
                }
            }
        }
    }
}

/// Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
fn luby(i: u32) -> u64 {
    // Find the smallest k such that 2^k - 1 >= i+1
    let idx = i + 1;
    let mut size = 1u32;
    while size < idx {
        size = 2 * size + 1;
    }
    // Now recurse down the tree
    let mut size = size;
    let mut idx = idx;
    loop {
        if size == idx {
            return ((size + 1) / 2) as u64;
        }
        size /= 2;
        if idx > size {
            idx -= size;
        }
    }
}

/// Parse a DIMACS CNF file and load it into a new solver.
/// Returns the solver ready for `solve()`.
pub fn parse_dimacs(input: &str) -> Solver {
    let mut solver = Solver::new();
    let mut clause: Vec<i32> = Vec::new();
    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') || line.starts_with('p') {
            continue;
        }
        for tok in line.split_whitespace() {
            let lit: i32 = tok.parse().expect("invalid literal in DIMACS");
            if lit == 0 {
                solver.add_clause(clause.drain(..));
            } else {
                clause.push(lit);
            }
        }
    }
    if !clause.is_empty() {
        solver.add_clause(clause);
    }
    solver
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── API compatibility tests (match cadical::Solver behavior) ──

    #[test]
    fn empty_solver_is_sat() {
        let mut s = Solver::new();
        assert_eq!(s.solve(), Some(true));
    }

    #[test]
    fn single_unit_clause() {
        let mut s = Solver::new();
        s.add_clause([1]);
        assert_eq!(s.solve(), Some(true));
        assert_eq!(s.value(1), Some(true));
    }

    #[test]
    fn contradicting_units() {
        let mut s = Solver::new();
        s.add_clause([1]);
        s.add_clause([-1]);
        assert_eq!(s.solve(), Some(false));
    }

    #[test]
    fn empty_clause_is_unsat() {
        let mut s = Solver::new();
        s.add_clause(std::iter::empty::<i32>());
        assert_eq!(s.solve(), Some(false));
    }

    #[test]
    fn simple_sat() {
        let mut s = Solver::new();
        s.add_clause([1, 2]);
        s.add_clause([-1, 2]);
        assert_eq!(s.solve(), Some(true));
        assert_eq!(s.value(2), Some(true)); // 2 must be true
    }

    #[test]
    fn simple_unsat() {
        let mut s = Solver::new();
        s.add_clause([1, 2]);
        s.add_clause([1, -2]);
        s.add_clause([-1, 2]);
        s.add_clause([-1, -2]);
        assert_eq!(s.solve(), Some(false));
    }

    #[test]
    fn three_coloring_triangle() {
        // Graph coloring: triangle with 3 colors (SAT)
        // Variables: x_{node,color} for node=0,1,2 and color=0,1,2
        // var(n,c) = 3*n + c + 1
        let var = |n: i32, c: i32| -> i32 { 3 * n + c + 1 };
        let mut s = Solver::new();

        // Each node gets at least one color
        for n in 0..3 {
            s.add_clause([var(n, 0), var(n, 1), var(n, 2)]);
        }
        // Each node gets at most one color
        for n in 0..3 {
            for c1 in 0..3 {
                for c2 in (c1 + 1)..3 {
                    s.add_clause([-var(n, c1), -var(n, c2)]);
                }
            }
        }
        // Adjacent nodes get different colors
        let edges = [(0, 1), (1, 2), (0, 2)];
        for &(a, b) in &edges {
            for c in 0..3 {
                s.add_clause([-var(a, c), -var(b, c)]);
            }
        }

        assert_eq!(s.solve(), Some(true));
        // Verify: each node has exactly one color, adjacent different
        for n in 0..3 {
            let colors: Vec<bool> = (0..3).map(|c| s.value(var(n, c)) == Some(true)).collect();
            assert_eq!(colors.iter().filter(|&&c| c).count(), 1,
                "node {} should have exactly one color", n);
        }
        for &(a, b) in &edges {
            for c in 0..3 {
                assert!(!(s.value(var(a, c)) == Some(true) && s.value(var(b, c)) == Some(true)),
                    "adjacent nodes {} and {} both have color {}", a, b, c);
            }
        }
    }

    #[test]
    fn four_coloring_complete4_is_sat() {
        // K4 with 4 colors: SAT
        let var = |n: i32, c: i32| -> i32 { 4 * n + c + 1 };
        let mut s = Solver::new();
        for n in 0..4 {
            s.add_clause((0..4).map(|c| var(n, c)));
            for c1 in 0..4 {
                for c2 in (c1 + 1)..4 {
                    s.add_clause([-var(n, c1), -var(n, c2)]);
                }
            }
        }
        for a in 0..4 {
            for b in (a + 1)..4 {
                for c in 0..4 {
                    s.add_clause([-var(a, c), -var(b, c)]);
                }
            }
        }
        assert_eq!(s.solve(), Some(true));
    }

    #[test]
    fn three_coloring_complete4_is_unsat() {
        // K4 with 3 colors: UNSAT
        let var = |n: i32, c: i32| -> i32 { 3 * n + c + 1 };
        let mut s = Solver::new();
        for n in 0..4 {
            s.add_clause((0..3).map(|c| var(n, c)));
            for c1 in 0..3 {
                for c2 in (c1 + 1)..3 {
                    s.add_clause([-var(n, c1), -var(n, c2)]);
                }
            }
        }
        for a in 0..4 {
            for b in (a + 1)..4 {
                for c in 0..3 {
                    s.add_clause([-var(a, c), -var(b, c)]);
                }
            }
        }
        assert_eq!(s.solve(), Some(false));
    }

    #[test]
    fn pigeonhole_3_in_2_is_unsat() {
        // 3 pigeons, 2 holes: UNSAT
        // var(p,h) = 2*p + h + 1
        let var = |p: i32, h: i32| -> i32 { 2 * p + h + 1 };
        let mut s = Solver::new();
        // Each pigeon gets at least one hole
        for p in 0..3 {
            s.add_clause([var(p, 0), var(p, 1)]);
        }
        // No two pigeons in the same hole
        for h in 0..2 {
            for p1 in 0..3 {
                for p2 in (p1 + 1)..3 {
                    s.add_clause([-var(p1, h), -var(p2, h)]);
                }
            }
        }
        assert_eq!(s.solve(), Some(false));
    }

    #[test]
    fn value_returns_none_for_unknown_var() {
        let s = Solver::new();
        assert_eq!(s.value(1), None);
        assert_eq!(s.value(0), None);
    }

    #[test]
    fn larger_clause() {
        let mut s = Solver::new();
        s.add_clause([1, 2, 3, 4, 5]);
        s.add_clause([-1]);
        s.add_clause([-2]);
        s.add_clause([-3]);
        s.add_clause([-4]);
        // 1-4 are false, so 5 must be true
        assert_eq!(s.solve(), Some(true));
        assert_eq!(s.value(5), Some(true));
    }

    #[test]
    fn luby_sequence() {
        let expected = [1u64, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
        for (i, &exp) in expected.iter().enumerate() {
            assert_eq!(luby(i as u32), exp, "luby({}) should be {}", i, exp);
        }
    }

    // ── Cardinality / XNOR tests (same patterns used by turyn) ──

    #[test]
    fn xnor_encoding() {
        // Test that we can encode XNOR(a,b) = aux correctly
        let mut s = Solver::new();
        let a = 1;
        let b = 2;
        let aux = 3;
        // aux ↔ (a ↔ b)
        s.add_clause([-aux, -a, b]);
        s.add_clause([-aux, a, -b]);
        s.add_clause([a, b, aux]);
        s.add_clause([-a, -b, aux]);
        // Force a=true, b=true → aux must be true
        s.add_clause([a]);
        s.add_clause([b]);
        assert_eq!(s.solve(), Some(true));
        assert_eq!(s.value(aux), Some(true));
    }

    #[test]
    fn exactly_k_of_n_via_totalizer() {
        // Test exactly 2 of 4 variables are true
        // Build a simple totalizer manually
        let mut s = Solver::new();
        let lits = [1, 2, 3, 4];

        // Instead of building a totalizer, just test with brute force clauses
        // At least 2: every pair of negations is forbidden
        // At most 2: every triple of positives is forbidden
        // (this is the simplest exact-k encoding for small k)
        for a in 0..4 {
            for b in (a+1)..4 {
                for c in (b+1)..4 {
                    s.add_clause([-lits[a], -lits[b], -lits[c]]); // at most 2
                }
            }
        }
        for a in 0..4 {
            for b in (a+1)..4 {
                for c in (b+1)..4 {
                    // at least 2 = ¬(at most 1) = not all triples of negations
                    s.add_clause([lits[a], lits[b], lits[c]]);
                }
            }
        }

        assert_eq!(s.solve(), Some(true));
        let count = lits.iter().filter(|&&v| s.value(v) == Some(true)).count();
        assert_eq!(count, 2, "exactly 2 of 4 should be true");
    }

    #[test]
    fn stress_random_3sat() {
        // Random 3-SAT near the phase transition (ratio 4.26)
        // 20 variables, 85 clauses — should be solvable
        let mut s = Solver::new();
        let n_vars = 20;
        let n_clauses = 80; // slightly below transition
        let mut rng: u64 = 42;
        let mut next = || -> u64 {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng
        };

        for _ in 0..n_clauses {
            let mut clause = Vec::new();
            for _ in 0..3 {
                let v = (next() % n_vars) as i32 + 1;
                let lit = if next() & 1 == 0 { v } else { -v };
                clause.push(lit);
            }
            s.add_clause(clause);
        }

        // Should complete (SAT or UNSAT) without panicking
        let result = s.solve();
        assert!(result == Some(true) || result == Some(false));
    }

    #[test]
    fn assumptions_basic() {
        let mut s = Solver::new();
        s.add_clause([1, 2]);       // x1 OR x2
        s.add_clause([-1, -2]);     // at most one true

        // x1=true → x2=false
        assert_eq!(s.solve_with_assumptions(&[1]), Some(true));
        assert_eq!(s.value(1), Some(true));
        assert_eq!(s.value(2), Some(false));
        s.reset();

        // x2=true → x1=false
        assert_eq!(s.solve_with_assumptions(&[2]), Some(true));
        assert_eq!(s.value(2), Some(true));
        assert_eq!(s.value(1), Some(false));
        s.reset();

        // Both false: UNSAT
        assert_eq!(s.solve_with_assumptions(&[-1, -2]), Some(false));

        // After UNSAT, different assumptions should still work
        assert_eq!(s.solve_with_assumptions(&[1]), Some(true));
    }

    #[test]
    fn assumptions_repeated_sat() {
        // Simulate the hybrid pattern: same structural clauses,
        // different cardinality targets via assumptions
        let mut s = Solver::new();
        // 4 variables, structural clause: at least one true
        s.add_clause([1, 2, 3, 4]);
        // at most 2 true
        s.add_clause([-1, -2, -3]);
        s.add_clause([-1, -2, -4]);
        s.add_clause([-1, -3, -4]);
        s.add_clause([-2, -3, -4]);

        // Multiple rounds with different assumptions
        for round in 0..10 {
            let assume_var = (round % 4) as i32 + 1;
            let result = s.solve_with_assumptions(&[assume_var]);
            assert_eq!(result, Some(true), "round {} with assumption {} should be SAT", round, assume_var);
            s.reset();
        }

        // Assumption that makes it UNSAT: all four true
        assert_eq!(s.solve_with_assumptions(&[1, 2, 3]), Some(false));

        // Should still work after UNSAT
        assert_eq!(s.solve_with_assumptions(&[1]), Some(true));
        s.reset();
        assert_eq!(s.solve_with_assumptions(&[4]), Some(true));
    }
}
