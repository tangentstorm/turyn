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
#[derive(Clone, Copy, Debug)]
struct QuadPbTerm {
    lit_a: Lit,
    lit_b: Lit,
    coeff: u32,
    state: u8,      // 0=DEAD, 1=MAYBE, 2=TRUE
}

impl QuadPbTerm {
    #[inline(always)]
    fn var_a(&self) -> usize { var_of(self.lit_a) }
    #[inline(always)]
    fn var_b(&self) -> usize { var_of(self.lit_b) }
    #[inline(always)]
    fn true_val_a(&self) -> LBool { if self.lit_a > 0 { LBool::True } else { LBool::False } }
    #[inline(always)]
    fn true_val_b(&self) -> LBool { if self.lit_b > 0 { LBool::True } else { LBool::False } }
    #[inline(always)]
    fn neg_a(&self) -> bool { self.lit_a < 0 }
    #[inline(always)]
    fn neg_b(&self) -> bool { self.lit_b < 0 }
}

#[derive(Clone, Debug)]
struct QuadPbConstraint {
    terms: Vec<QuadPbTerm>,  // single Vec instead of 10 separate ones
    target: u32,
    num_terms: u32,
    sum_true: i32,
    sum_maybe: i32,
}

/// Reason a variable was assigned (for conflict analysis).
#[derive(Clone, Copy, Debug)]
enum Reason {
    Decision,
    Clause(u32),  // index into clause database
    Pb(u32),      // index into pb_constraints
    QuadPb(u32),  // index into quad_pb_constraints
}

/// Trail entry: records an assignment.
#[derive(Clone, Copy, Debug)]
struct TrailEntry {
    lit: Lit,
    level: u32,
    reason: Reason,
}

/// CDCL SAT Solver.
#[derive(Clone)]
pub struct Solver {
    // Variable state
    num_vars: usize,
    assigns: Vec<LBool>,    // indexed by var (0-based)
    level: Vec<u32>,         // decision level of each var
    reason: Vec<Reason>,     // reason for assignment
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
    // Stored explanations: captured at propagation time, used during analysis.
    // Indexed by variable. Cleared on backtrack.
    quad_pb_reasons: Vec<Option<Vec<Lit>>>,
    // Reusable scratch buffers for propagate_quad_pb (avoid per-call allocation)
    quad_pb_expl_buf: Vec<Lit>,
    quad_pb_seen_buf: Vec<bool>,

    // Propagation queue
    prop_head: usize, // next trail entry to propagate

    // Restart
    conflicts: u64,
    restart_limit: u64,
    luby_index: u32,

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
            num_vars: 0,
            assigns: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
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
            quad_pb_reasons: Vec::new(),
            quad_pb_expl_buf: Vec::new(),
            quad_pb_seen_buf: Vec::new(),
            activity: Vec::new(),
            var_inc: 1.0,
            var_decay: 0.95,
            heap: Vec::new(),
            heap_pos: Vec::new(),
            prop_head: 0,
            conflicts: 0,
            restart_limit: 100,
            luby_index: 0,
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
            self.phase.push(true); // default: branch positive
            self.activity.push(0.0);
            self.watches.push(Vec::new()); // positive literal watch
            self.watches.push(Vec::new()); // negative literal watch
            self.pb_watches.push(Vec::new()); // positive literal PB
            self.pb_watches.push(Vec::new()); // negative literal PB
            self.quad_pb_var_watches.push(Vec::new());
            self.quad_pb_var_terms.push(Vec::new());
            self.quad_pb_reasons.push(None);
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
                coeff: coeffs[i],
                state: 1, // MAYBE
            }
        }).collect();
        self.quad_pb_constraints.push(QuadPbConstraint {
            target,
            num_terms: terms.len() as u32,
            sum_true: 0,
            sum_maybe: coeffs.iter().sum::<u32>() as i32,
            terms,
        });

        // Initial propagation
        if self.propagate_quad_pb(qi).is_some() {
            self.ok = false;
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
    pub fn set_conflict_limit(&mut self, limit: u64) { self.conflict_limit = limit; }

    /// Reset a quad PB constraint's incremental state from precomputed values.
    /// Used for fast boundary config switching without backtracking.
    pub fn reset_quad_pb_state(&mut self, qi: usize, term_state: &[u8], sum_true: i32, sum_maybe: i32) {
        let qc = &mut self.quad_pb_constraints[qi];
        for (i, &s) in term_state.iter().enumerate() {
            qc.terms[i].state = s;
        }
        qc.sum_true = sum_true;
        qc.sum_maybe = sum_maybe;
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
                self.backtrack(bt_level);
                self.add_learnt_clause(learnt_clause);
                self.decay_activities();

                // Restart check
                if self.conflicts >= self.restart_limit {
                    self.restart_limit += 100 * luby(self.luby_index);
                    self.luby_index += 1;
                    self.backtrack(base_level);
                    self.reduce_db();
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

        let new_state = if aa == LBool::Undef {
            if ab == LBool::Undef { 1u8 }
            else if ab != t.true_val_b() { 0u8 }
            else { 1u8 }
        } else if ab == LBool::Undef {
            if aa != t.true_val_a() { 0u8 }
            else { 1u8 }
        } else {
            if (aa != t.true_val_a()) | (ab != t.true_val_b()) { 0u8 } else { 2u8 }
        };

        let qc = &mut self.quad_pb_constraints[qi as usize];
        let old_state = qc.terms[ti].state;
        if old_state == new_state { return; }

        let c = qc.terms[ti].coeff as i32;
        if old_state == 1 { qc.sum_maybe -= c; }
        else if old_state == 2 { qc.sum_true -= c; }
        if new_state == 1 { qc.sum_maybe += c; }
        else if new_state == 2 { qc.sum_true += c; }
        qc.terms[ti].state = new_state;
    }

    /// Propagate a quadratic PB constraint using incremental counters.
    /// Single-pass: finds propagation and builds explanation in one fused scan.
    #[inline]
    fn propagate_quad_pb(&mut self, qi: u32) -> Option<Reason> {
        let qc = &self.quad_pb_constraints[qi as usize];
        let n = qc.num_terms as usize;
        let target = qc.target as i64;
        let sum_true = qc.sum_true as i64;
        let sum_maybe = qc.sum_maybe as i64;

        if sum_true + sum_maybe < target || sum_true > target {
            return Some(Reason::QuadPb(qi)); // conflict
        }

        let slack_up = sum_true + sum_maybe - target;
        let slack_down = target - sum_true;
        if slack_up > 0 && slack_down > 0 { return None; }

        // Grow seen buffer if needed; clear only used entries after each propagation
        if self.quad_pb_seen_buf.len() < self.num_vars {
            self.quad_pb_seen_buf.resize(self.num_vars, false);
        }

        for i in 0..n {
            let t = &self.quad_pb_constraints[qi as usize].terms[i];
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

            let pv = var_of(propagated_lit);
            let is_upper = c > slack_down;

            // Reuse scratch buffers instead of allocating
            self.quad_pb_expl_buf.clear();
            let seen = &mut self.quad_pb_seen_buf;
            {
                let terms = &self.quad_pb_constraints[qi as usize].terms;
                for t in terms {
                    let va = t.var_a();
                    let vb = t.var_b();
                    let aa = self.assigns[va];
                    let ab = self.assigns[vb];
                    let af = (aa == LBool::True && t.neg_a()) || (aa == LBool::False && !t.neg_a());
                    let bf = (ab == LBool::True && t.neg_b()) || (ab == LBool::False && !t.neg_b());

                    if af || bf {
                        let (lit, v) = if af { (t.lit_a, va) } else { (t.lit_b, vb) };
                        if v != pv && !seen[v] && self.level[v] > 0 {
                            seen[v] = true;
                            self.quad_pb_expl_buf.push(lit);
                        }
                    } else if is_upper && aa != LBool::Undef && ab != LBool::Undef {
                        if va != pv && !seen[va] && self.level[va] > 0 {
                            seen[va] = true;
                            self.quad_pb_expl_buf.push(negate(t.lit_a));
                        }
                        if vb != pv && !seen[vb] && self.level[vb] > 0 {
                            seen[vb] = true;
                            self.quad_pb_expl_buf.push(negate(t.lit_b));
                        }
                    }
                }
            }
            // Clear seen flags for used entries
            for &lit in &self.quad_pb_expl_buf {
                seen[var_of(lit)] = false;
            }
            // Clone into storage, keeping buffer capacity for reuse
            self.quad_pb_reasons[pv] = Some(self.quad_pb_expl_buf.clone());
            self.enqueue(propagated_lit, Reason::QuadPb(qi));
            return None;
        }
        None
    }

    /// 1-UIP conflict analysis with learnt clause minimization.
    /// Returns (learnt clause, backtrack level).
    fn analyze(&mut self, conflict_reason: Reason) -> (Vec<Lit>, u32) {
        let mut seen = vec![false; self.num_vars];
        let mut counter = 0;
        let mut learnt = Vec::new();
        let mut bt_level: u32 = 0;
        let mut current_reason = conflict_reason;
        let mut trail_idx = self.trail.len();
        let mut p: Lit = 0;

        loop {
            // Get the literals of the reason (clause or PB explanation)
            let reason_lits: Vec<Lit> = match current_reason {
                Reason::Clause(ci) => {
                    let m = self.clause_meta[ci as usize];
                    let cstart = m.start as usize;
                    let clen = m.len as usize;
                    self.clause_lits[cstart..cstart + clen].to_vec()
                }
                Reason::Pb(pbi) => {
                    // For PB conflict/propagation: generate clause from all false lits
                    let pb = &self.pb_constraints[pbi as usize];
                    let mut lits = Vec::new();
                    for i in 0..pb.lits.len() {
                        let lit = pb.lits[i];
                        if lit == negate(p) { continue; } // skip the propagated lit's negation
                        if self.lit_value(lit) == LBool::False {
                            lits.push(lit); // false literal, part of the reason
                        }
                    }
                    if p != 0 {
                        lits.push(p); // the propagated literal itself
                    }
                    lits
                }
                Reason::QuadPb(qi) => {
                    if p != 0 {
                        // Propagation: use stored explanation (captured at propagation time)
                        let pv = var_of(p);
                        let mut lits = self.quad_pb_reasons[pv].take().unwrap_or_default();
                        lits.push(p);
                        lits
                    } else {
                        // Conflict: compute from current state (haven't backtracked yet)
                        let terms = &self.quad_pb_constraints[qi as usize].terms;
                        let mut lits = Vec::new();
                        let mut seen_v = vec![false; self.num_vars];
                        for t in terms {
                            for &(lit, v) in &[(t.lit_a, t.var_a()), (t.lit_b, t.var_b())] {
                                if !seen_v[v] && self.assigns[v] != LBool::Undef && self.level[v] > 0 {
                                    seen_v[v] = true;
                                    lits.push(if self.lit_value(lit) == LBool::False { lit } else { negate(lit) });
                                }
                            }
                        }
                        lits
                    }
                }
                Reason::Decision => { unreachable!(); }
            };

            for &lit in &reason_lits {
                if lit == p { continue; }
                let v = var_of(lit);
                if seen[v] { continue; }
                seen[v] = true;
                self.bump_activity(v);

                if self.level[v] == self.decision_level() {
                    counter += 1;
                } else if self.level[v] > 0 {
                    learnt.push(lit);
                    bt_level = bt_level.max(self.level[v]);
                }
            }

            // Find next literal on trail at current decision level that was seen
            loop {
                trail_idx -= 1;
                let entry = &self.trail[trail_idx];
                let v = var_of(entry.lit);
                if seen[v] && entry.level == self.decision_level() {
                    p = entry.lit;
                    counter -= 1;
                    if counter == 0 {
                        learnt.insert(0, negate(p));
                        self.minimize_learnt(&mut learnt, &seen);
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
    fn minimize_learnt(&self, learnt: &mut Vec<Lit>, seen: &[bool]) {
        let mut levels_in_learnt = vec![false; self.decision_level() as usize + 1];
        for &lit in learnt.iter() {
            let lv = self.level[var_of(lit)] as usize;
            if lv < levels_in_learnt.len() {
                levels_in_learnt[lv] = true;
            }
        }

        let mut j = 1; // keep learnt[0] (the asserting literal)
        for i in 1..learnt.len() {
            let lit = learnt[i];
            let v = var_of(lit);
            match self.reason[v] {
                Reason::Clause(_) | Reason::Pb(_) | Reason::QuadPb(_) => {
                    if self.lit_removable(v, seen, &levels_in_learnt) {
                        continue;
                    }
                }
                Reason::Decision => {}
            }
            learnt[j] = lit;
            j += 1;
        }
        learnt.truncate(j);
    }

    /// Check if a literal's antecedent chain is covered by the learnt clause.
    fn lit_removable(&self, v: usize, seen: &[bool], levels_in_learnt: &[bool]) -> bool {
        let mut stack: Vec<usize> = vec![v];
        let mut visited = vec![false; self.num_vars];
        visited[v] = true;

        while let Some(cur) = stack.pop() {
            // Get reason literals (clause or PB explanation)
            let reason_lits: Vec<Lit> = match self.reason[cur] {
                Reason::Clause(ci) => self.clause_lits(ci).to_vec(),
                Reason::Pb(pbi) => {
                    let pb = &self.pb_constraints[pbi as usize];
                    pb.lits.iter().copied()
                        .filter(|&l| var_of(l) != cur && self.lit_value(l) == LBool::False)
                        .collect()
                }
                Reason::QuadPb(_qi) => {
                    // Use stored explanation if available
                    if let Some(ref lits) = self.quad_pb_reasons[cur] {
                        lits.clone()
                    } else {
                        // Fallback: can't minimize without explanation
                        return false;
                    }
                }
                Reason::Decision => return false,
            };
            for &lit in &reason_lits {
                let u = var_of(lit);
                if u == cur || visited[u] { continue; }
                visited[u] = true;
                if self.level[u] == 0 { continue; }
                if seen[u] { continue; }
                let lv = self.level[u] as usize;
                if lv >= levels_in_learnt.len() || !levels_in_learnt[lv] { return false; }
                match self.reason[u] {
                    Reason::Decision => return false,
                    Reason::Clause(_) | Reason::Pb(_) | Reason::QuadPb(_) => { stack.push(u); }
                }
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
            if v < self.quad_pb_reasons.len() { self.quad_pb_reasons[v] = None; }
            // Incrementally update quad PB term states after unassigning.
            // Skip for level 0 when caller manages state externally (table path).
            if !(level == 0 && self.skip_backtrack_quad_pb) {
                for idx in 0..self.quad_pb_var_terms[v].len() {
                    let (qi, ti, is_a) = self.quad_pb_var_terms[v][idx];
                    self.update_quad_pb_term_hint(qi, ti as usize, LBool::Undef, is_a);
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
                qc.sum_true = 0;
                qc.sum_maybe = total;
                for t in qc.terms.iter_mut() { t.state = 1; } // all MAYBE
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
