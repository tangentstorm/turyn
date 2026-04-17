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

/// A "sum is in a set" constraint: `#{i : lit_i true} ∈ V` where `V` is a
/// sorted, deduplicated set of non-negative integer cardinality targets.
///
/// Propagation recounts `(num_true, num_undef)` from the trail on every
/// call (see `propagate_pb_set_eq`).  Let `cnt_lo = num_true`,
/// `cnt_hi = num_true + num_undef`.  Binary-search V for
/// `V_alive = V ∩ [cnt_lo, cnt_hi]`:
///   - `V_alive == ∅` ⇒ conflict.
///   - `V_alive == {v}` and `v == cnt_lo` ⇒ force all unassigned lits false.
///   - `V_alive == {v}` and `v == cnt_hi` ⇒ force all unassigned lits true.
///   - `|V_alive| > 1` and `cnt_lo == max(V_alive)` ⇒ force all unassigned false.
///   - `|V_alive| > 1` and `cnt_hi == min(V_alive)` ⇒ force all unassigned true.
///   - otherwise ⇒ no propagation (the SAT will branch).
///
/// No incremental counter is maintained: a previous attempt at
/// incremental bookkeeping was unsound because prior propagators in
/// the same propagate-loop iteration (QuadPb, or this constraint's own
/// `force_pb_set_eq_dir`) can enqueue literals whose state change is
/// not reflected in the incremental until the main loop eventually
/// picks them up.  See `pb_set_eq_plus_quad_pb_tt18_regression`.
#[derive(Clone, Debug)]
struct PbSetEqConstraint {
    lits: Vec<Lit>,
    values: Vec<u32>, // sorted ascending, unique, all in 0..=lits.len()
    // `num_true` and `num_undef` are scratch fields set by
    // `recompute_pb_set_eq` at the start of every `propagate_pb_set_eq`
    // call; they are *not* a persistent incremental count.  Do not
    // read them outside `propagate_pb_set_eq`.
    num_true: u32,
    num_undef: u32,
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

/// MDD constraint: encodes a multi-valued decision diagram over boundary variable pairs.
/// At each of `depth` levels, two SAT variables (x, y) select one of 4 branches.
/// The MDD prunes infeasible boundary combinations without auxiliary variables.
///
/// Propagation: when a boundary variable is assigned, recompute the set of
/// reachable MDD nodes (top-down frontier). If the frontier becomes empty → conflict.
/// If only one branch is viable at some level → force the implied variable.
#[derive(Clone)]
pub struct MddConstraint {
    /// MDD node table. nodes[nid] = [child0, child1, child2, child3].
    /// Branch index = x_val | (y_val << 1). DEAD=0, LEAF=u32::MAX.
    pub nodes: Vec<[u32; 4]>,
    pub root: u32,
    pub depth: usize,
    /// level_x_var[level] = 0-based SAT variable for X at this MDD level
    pub level_x_var: Vec<usize>,
    /// level_y_var[level] = 0-based SAT variable for Y at this MDD level
    pub level_y_var: Vec<usize>,
    /// var_to_level[var_0based] = MDD level, or usize::MAX if not an MDD variable
    pub var_to_level: Vec<usize>,
    /// Whether this var is the X (true) or Y (false) variable at its level
    pub var_is_x: Vec<bool>,
    /// Cached frontier per level (level_frontier[l] = reachable nodes entering level l)
    /// level_frontier[0] = [root], updated incrementally.
    pub level_frontier: Vec<Vec<u32>>,
    /// Lowest dirty level (levels below this are clean). On backtrack we only
    /// raise dirty_level to the level of the lowest unassigning MDD variable,
    /// so levels above it retain their valid frontiers.
    pub dirty_level: usize,
    /// Scratch dedup bitset: 1 slot per node. Replaces the old O(n) `contains`
    /// scan when building the next-level frontier. Reset between levels by
    /// iterating `scratch_seen_list` (O(frontier_size), not O(nodes)).
    scratch_seen: Vec<bool>,
    scratch_seen_list: Vec<u32>,
    /// Scratch buffer for the next-level frontier being built. Swapped into
    /// level_frontier[level+1] once populated, avoiding a per-level clone.
    scratch_next: Vec<u32>,
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
    target_hi: u32,         // for range constraints; equals target for equality
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
    Spectral,     // spectral power constraint violation
    Mdd,          // MDD constraint: boundary variables violate MDD path feasibility
    PbSetEq(u32), // index into pb_set_eq_constraints
}

/// Trail entry: records an assignment.
#[derive(Clone, Copy, Debug)]
struct TrailEntry {
    lit: Lit,
    level: u32,
    reason: Reason,
}

/// Spectral power constraint: |DFT(sequence)|² ≤ bound at every sampled frequency.
/// Incrementally tracks DFT sums as variables are assigned.
/// Variables 1..num_seq_vars represent ±1 sequence positions.
#[derive(Clone)]
pub struct SpectralConstraint {
    /// Number of sequence variables (positions that the SAT solver controls).
    pub num_seq_vars: usize,
    /// Cosine table: cos_table[var_idx * num_freqs + freq_idx]
    /// Precomputed: cos(2π * position_in_full_seq * ω_j / fft_size).
    /// Shared across SpectralConstraint instances built from the same
    /// SpectralTables (boundary-independent).
    pub cos_table: std::sync::Arc<Vec<f32>>,
    /// Sine table (same layout, shared)
    pub sin_table: std::sync::Arc<Vec<f32>>,
    /// Number of sampled frequencies
    pub num_freqs: usize,
    /// Running DFT real parts per frequency (includes boundary contribution)
    pub re: Vec<f64>,
    /// Running DFT imaginary parts per frequency
    pub im: Vec<f64>,
    /// Boundary contribution to DFT (constant, precomputed)
    pub re_boundary: Vec<f64>,
    pub im_boundary: Vec<f64>,
    /// Spectral power bound: |DFT(ω)|² ≤ bound for each ω
    pub bound: f64,
    /// Optional per-frequency bounds (for Z pair-spectral: B - |W(ω)|²).
    pub per_freq_bound: Option<Vec<f64>>,
    /// Max possible magnitude reduction from unassigned vars, per frequency.
    /// Updated incrementally on assign/unassign.
    pub max_reduction: Vec<f64>,
    /// Per-variable amplitude at each frequency: sqrt(cos² + sin²).
    /// Shared across instances with the same tables.
    pub amplitudes: std::sync::Arc<Vec<f32>>,
    /// Which variables have been assigned (for backtrack)
    pub assigned: Vec<bool>,
    /// The value assigned to each variable (+1 or -1), 0 if unassigned
    pub values: Vec<i8>,
    /// Optional second sequence for combined spectral (e.g., WZ pair bound).
    /// If set, vars 0..seq2_start are sequence 1 (weight seq1_weight),
    /// vars seq2_start.. are sequence 2 (weight seq2_weight).
    /// Check: w1*|S1(ω)|² + w2*|S2(ω)|² ≤ bound.
    pub seq2: Option<Seq2Config>,
}

/// Config for a two-sequence spectral constraint.
#[derive(Clone)]
pub struct Seq2Config {
    /// First var index of the second sequence (0-based).
    pub seq2_start: usize,
    /// Weight for sequence 1 power in combined constraint (e.g., 2.0 for W).
    pub weight1: f64,
    /// Weight for sequence 2 power in combined constraint (e.g., 2.0 for Z).
    pub weight2: f64,
    /// Individual bound per sequence (e.g., individual_bound for W and Z separately).
    pub individual_bound: f64,
    /// Separate DFT tracking for sequence 1.
    pub re1: Vec<f64>,
    pub im1: Vec<f64>,
    pub re1_boundary: Vec<f64>,
    pub im1_boundary: Vec<f64>,
    pub max_reduction1: Vec<f64>,
    /// Separate DFT tracking for sequence 2.
    pub re2: Vec<f64>,
    pub im2: Vec<f64>,
    pub re2_boundary: Vec<f64>,
    pub im2_boundary: Vec<f64>,
    pub max_reduction2: Vec<f64>,
}

/// Pre-computed trig tables for spectral constraint (boundary-independent).
/// Shared across all SpectralConstraint instances with the same (seq_len, k, num_freqs).
#[derive(Clone)]
pub struct SpectralTables {
    pub cos_table: std::sync::Arc<Vec<f32>>,
    pub sin_table: std::sync::Arc<Vec<f32>>,
    pub amplitudes: std::sync::Arc<Vec<f32>>,
    pub max_reduction_total: Vec<f64>,  // sum of all amplitudes per freq
    pub num_freqs: usize,
    pub middle_len: usize,
    pub seq_len: usize,
    pub k: usize,
    /// Precomputed omega values for boundary DFT
    #[allow(dead_code)]
    omega: Vec<f64>,
    /// Precomputed cos/sin for ALL positions (for boundary DFT).
    /// Indexed as pos_cos[pos * num_freqs + fi] where pos in 0..seq_len,
    /// fi in 0..num_freqs. Public so callers can compute W's DFT at the
    /// SAT frequency grid without redoing the trig.
    pub pos_cos: Vec<f64>,
    pub pos_sin: Vec<f64>,
}

impl SpectralTables {
    /// Build once per (seq_len, k, num_freqs). Reuse across boundaries.
    ///
    /// Frequency grid: `ω_fi = (fi + 1) / (num_freqs + 1) · π` for
    /// `fi ∈ 0..num_freqs`, i.e., `num_freqs` equally-spaced interior
    /// samples of `(0, π)` excluding both endpoints.
    pub fn new(seq_len: usize, k: usize, num_freqs: usize) -> Self {
        let middle_len = seq_len - 2 * k;
        let mut cos_table = vec![0.0f32; middle_len * num_freqs];
        let mut sin_table = vec![0.0f32; middle_len * num_freqs];
        let mut omega_vec = vec![0.0f64; num_freqs];
        let mut pos_cos = vec![0.0f64; seq_len * num_freqs];
        let mut pos_sin = vec![0.0f64; seq_len * num_freqs];

        for fi in 0..num_freqs {
            let omega = (fi as f64 + 1.0) / (num_freqs as f64 + 1.0) * std::f64::consts::PI;
            omega_vec[fi] = omega;

            for pos in 0..seq_len {
                pos_cos[pos * num_freqs + fi] = (omega * pos as f64).cos();
                pos_sin[pos * num_freqs + fi] = (omega * pos as f64).sin();
            }

            for vi in 0..middle_len {
                let pos = k + vi;
                cos_table[vi * num_freqs + fi] = pos_cos[pos * num_freqs + fi] as f32;
                sin_table[vi * num_freqs + fi] = pos_sin[pos * num_freqs + fi] as f32;
            }
        }

        let mut amplitudes = vec![0.0f32; middle_len * num_freqs];
        let mut max_reduction_total = vec![0.0f64; num_freqs];
        for vi in 0..middle_len {
            for fi in 0..num_freqs {
                let c = cos_table[vi * num_freqs + fi] as f64;
                let s = sin_table[vi * num_freqs + fi] as f64;
                let amp = (c * c + s * s).sqrt() as f32;
                amplitudes[vi * num_freqs + fi] = amp;
                max_reduction_total[fi] += amp as f64;
            }
        }

        SpectralTables {
            cos_table: std::sync::Arc::new(cos_table),
            sin_table: std::sync::Arc::new(sin_table),
            amplitudes: std::sync::Arc::new(amplitudes),
            max_reduction_total,
            num_freqs, middle_len, seq_len, k,
            omega: omega_vec, pos_cos, pos_sin,
        }
    }
}

impl SpectralConstraint {
    /// Create a new spectral constraint.
    /// `seq_len`: total sequence length (including boundary)
    /// `k`: boundary width
    /// `boundary`: full sequence with boundary positions filled, middle = 0
    /// `bound`: spectral power bound (|DFT(ω)|² ≤ bound)
    /// `num_freqs`: number of frequency samples
    pub fn new(
        seq_len: usize,
        k: usize,
        boundary: &[i8],
        bound: f64,
        num_freqs: usize,
    ) -> Self {
        let tables = SpectralTables::new(seq_len, k, num_freqs);
        Self::from_tables(&tables, boundary, bound)
    }

    /// Create from pre-computed tables (fast: skips trig computation).
    pub fn from_tables(tables: &SpectralTables, boundary: &[i8], bound: f64) -> Self {
        let num_freqs = tables.num_freqs;
        let middle_len = tables.middle_len;
        let seq_len = tables.seq_len;
        let k = tables.k;

        // Compute boundary DFT using precomputed pos_cos/pos_sin
        let mut re_boundary = vec![0.0f64; num_freqs];
        let mut im_boundary = vec![0.0f64; num_freqs];
        for pos in 0..seq_len {
            if pos >= k && pos < seq_len - k { continue; }
            let val = boundary[pos] as f64;
            for fi in 0..num_freqs {
                re_boundary[fi] += val * tables.pos_cos[pos * num_freqs + fi];
                im_boundary[fi] += val * tables.pos_sin[pos * num_freqs + fi];
            }
        }

        SpectralConstraint {
            num_seq_vars: middle_len,
            cos_table: std::sync::Arc::clone(&tables.cos_table),
            sin_table: std::sync::Arc::clone(&tables.sin_table),
            num_freqs,
            re: re_boundary.clone(),
            im: im_boundary.clone(),
            re_boundary,
            im_boundary,
            bound,
            per_freq_bound: None,
            max_reduction: tables.max_reduction_total.clone(),
            amplitudes: std::sync::Arc::clone(&tables.amplitudes),
            assigned: vec![false; middle_len],
            values: vec![0i8; middle_len],
            seq2: None,
        }
    }

    /// Reset DFT sums to boundary-only state (for checkpoint/restore).
    pub fn reset(&mut self) {
        self.re.copy_from_slice(&self.re_boundary);
        self.im.copy_from_slice(&self.im_boundary);
        // Recompute max_reduction from all vars being unassigned
        for fi in 0..self.num_freqs { self.max_reduction[fi] = 0.0; }
        for vi in 0..self.num_seq_vars {
            let base = vi * self.num_freqs;
            for fi in 0..self.num_freqs {
                self.max_reduction[fi] += self.amplitudes[base + fi] as f64;
            }
        }
        for v in &mut self.assigned { *v = false; }
        for v in &mut self.values { *v = 0; }
        if let Some(ref mut s2) = self.seq2 {
            s2.re1.copy_from_slice(&s2.re1_boundary);
            s2.im1.copy_from_slice(&s2.im1_boundary);
            s2.re2.copy_from_slice(&s2.re2_boundary);
            s2.im2.copy_from_slice(&s2.im2_boundary);
            // Recompute max_reduction from amplitudes
            for fi in 0..self.num_freqs { s2.max_reduction1[fi] = 0.0; s2.max_reduction2[fi] = 0.0; }
            for vi in 0..s2.seq2_start {
                for fi in 0..self.num_freqs {
                    s2.max_reduction1[fi] += self.amplitudes[vi * self.num_freqs + fi] as f64;
                }
            }
            for vi in s2.seq2_start..self.num_seq_vars {
                for fi in 0..self.num_freqs {
                    s2.max_reduction2[fi] += self.amplitudes[vi * self.num_freqs + fi] as f64;
                }
            }
        }
    }

    /// Assign a variable (0-indexed middle position) to val (+1 or -1).
    /// Updates DFT sums incrementally.
    #[inline]
    pub fn assign(&mut self, var: usize, val: i8) {
        debug_assert!(!self.assigned[var]);
        self.assigned[var] = true;
        self.values[var] = val;
        let v = val as f64;
        let base = var * self.num_freqs;
        for fi in 0..self.num_freqs {
            self.re[fi] += v * self.cos_table[base + fi] as f64;
            self.im[fi] += v * self.sin_table[base + fi] as f64;
            self.max_reduction[fi] -= self.amplitudes[base + fi] as f64;
        }
        // Two-sequence mode: update the appropriate sequence's DFT
        if let Some(ref mut s2) = self.seq2 {
            if var < s2.seq2_start {
                for fi in 0..self.num_freqs {
                    s2.re1[fi] += v * self.cos_table[base + fi] as f64;
                    s2.im1[fi] += v * self.sin_table[base + fi] as f64;
                    s2.max_reduction1[fi] -= self.amplitudes[base + fi] as f64;
                }
            } else {
                for fi in 0..self.num_freqs {
                    s2.re2[fi] += v * self.cos_table[base + fi] as f64;
                    s2.im2[fi] += v * self.sin_table[base + fi] as f64;
                    s2.max_reduction2[fi] -= self.amplitudes[base + fi] as f64;
                }
            }
        }
    }

    /// Unassign a variable. Undoes DFT contribution.
    #[inline]
    pub fn unassign(&mut self, var: usize) {
        debug_assert!(self.assigned[var]);
        let v = self.values[var] as f64;
        let base = var * self.num_freqs;
        for fi in 0..self.num_freqs {
            self.re[fi] -= v * self.cos_table[base + fi] as f64;
            self.im[fi] -= v * self.sin_table[base + fi] as f64;
            self.max_reduction[fi] += self.amplitudes[base + fi] as f64;
        }
        if let Some(ref mut s2) = self.seq2 {
            if var < s2.seq2_start {
                for fi in 0..self.num_freqs {
                    s2.re1[fi] -= v * self.cos_table[base + fi] as f64;
                    s2.im1[fi] -= v * self.sin_table[base + fi] as f64;
                    s2.max_reduction1[fi] += self.amplitudes[base + fi] as f64;
                }
            } else {
                for fi in 0..self.num_freqs {
                    s2.re2[fi] -= v * self.cos_table[base + fi] as f64;
                    s2.im2[fi] -= v * self.sin_table[base + fi] as f64;
                    s2.max_reduction2[fi] += self.amplitudes[base + fi] as f64;
                }
            }
        }
        self.assigned[var] = false;
        self.values[var] = 0;
    }

    /// Check if current partial assignment violates the spectral bound.
    /// Returns the violating frequency index, or None if OK.
    ///
    /// For each frequency: current |DFT|² must not exceed bound even after
    /// the remaining unassigned variables optimally reduce the magnitude.
    /// Max reduction per var at freq fi: sqrt(cos² + sin²) = amplitude.
    /// Total max reduction: sum of amplitudes of unassigned vars.
    /// Conflict if: |DFT| - max_reduction > sqrt(bound) at any freq.
    /// O(num_freqs) conflict check using precomputed max_reduction.
    #[inline]
    pub fn check_conflict(&self) -> Option<usize> {
        if let Some(ref s2) = self.seq2 {
            // Three checks per frequency:
            // 1. |W(ω)|² ≤ individual_bound
            // 2. |Z(ω)|² ≤ individual_bound
            // 3. w1*|W(ω)|² + w2*|Z(ω)|² ≤ pair_bound
            let ib_sqrt = s2.individual_bound.sqrt();
            for fi in 0..self.num_freqs {
                let mag1 = (s2.re1[fi] * s2.re1[fi] + s2.im1[fi] * s2.im1[fi]).sqrt();
                let mag2 = (s2.re2[fi] * s2.re2[fi] + s2.im2[fi] * s2.im2[fi]).sqrt();
                let min1 = (mag1 - s2.max_reduction1[fi]).max(0.0);
                let min2 = (mag2 - s2.max_reduction2[fi]).max(0.0);
                // Individual W bound
                if min1 > ib_sqrt { return Some(fi); }
                // Individual Z bound
                if min2 > ib_sqrt { return Some(fi); }
                // Combined pair bound
                if s2.weight1 * min1 * min1 + s2.weight2 * min2 * min2 > self.bound {
                    return Some(fi);
                }
            }
            None
        } else {
            // Single-sequence mode (original)
            for fi in 0..self.num_freqs {
                let b = match self.per_freq_bound {
                    Some(ref pfb) => pfb[fi],
                    None => self.bound,
                };
                if b <= 0.0 { return Some(fi); }
                let mag = (self.re[fi] * self.re[fi] + self.im[fi] * self.im[fi]).sqrt();
                if mag - self.max_reduction[fi] > b.sqrt() {
                    return Some(fi);
                }
            }
            None
        }
    }
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
    lbd_seen: Vec<bool>,              // reusable buffer for compute_lbd (avoids per-conflict alloc)

    // XOR (GF(2)) constraints
    xor_constraints: Vec<XorConstraint>,
    xor_var_watches: Vec<Vec<u32>>,  // xor_var_watches[var] = list of XOR constraint indices

    // "Sum is in a set" constraints: #{i : lit_i true} ∈ V (sorted non-negative set).
    // Propagation: binary-search V for the alive subset under current (cnt_lo, cnt_hi);
    // conflict when V_alive == ∅; force-all when only one direction remains.
    pb_set_eq_constraints: Vec<PbSetEqConstraint>,
    pb_set_eq_var_watches: Vec<Vec<u32>>, // per-variable list of constraint indices

    // MDD constraint (at most one, optional)
    pub mdd: Option<MddConstraint>,

    // Propagation queue
    prop_head: usize, // next trail entry to propagate

    // Restart (Luby)
    conflicts: u64,
    restart_limit: u64,
    luby_index: u32,

    // Search stats (plain u64 — Solver is per-thread; aggregation at caller)
    decisions: u64,
    propagations: u64,

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
    pub ok: bool, // false if top-level conflict detected
    /// When true, skip quad PB incremental updates during backtrack.
    /// Used when the caller will reset quad PB state externally.
    pub skip_backtrack_quad_pb: bool,

    /// Optional spectral power constraint (for W/Z middle generation).
    pub spectral: Option<SpectralConstraint>,
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
            pb_set_eq_constraints: Vec::new(),
            pb_set_eq_var_watches: Vec::new(),
            analyze_seen: Vec::new(),
            analyze_reason_buf: Vec::new(),
            analyze_reason_buf2: Vec::new(),
            minimize_stack: Vec::new(),
            minimize_visited: Vec::new(),
            minimize_levels: Vec::new(),
            lbd_seen: Vec::new(),
            activity: Vec::new(),
            var_inc: 1.0,
            var_decay: 0.95,
            heap: Vec::new(),
            heap_pos: Vec::new(),
            prop_head: 0,
            conflicts: 0,
            restart_limit: 100,
            luby_index: 0,
            decisions: 0,
            propagations: 0,
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
            mdd: None,
            spectral: None,
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
            self.pb_set_eq_var_watches.push(Vec::new());
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
                // Reorder: move non-false literals to the front for 2WL.
                // This handles incremental clause addition after a partial/full solve.
                let mut lits = lits;
                let mut num_true = 0usize;
                let mut num_undef = 0usize;
                // Partition: true/undef literals first, false last
                let mut i = 0;
                for j in 0..lits.len() {
                    match self.lit_value(lits[j]) {
                        LBool::True => { lits.swap(i, j); num_true += 1; i += 1; }
                        LBool::Undef => { lits.swap(i, j); num_undef += 1; i += 1; }
                        LBool::False => {}
                    }
                }
                if num_true == 0 && num_undef == 0 {
                    // All literals false: conflict at current level
                    self.ok = false;
                    return;
                }
                if num_true == 0 && num_undef == 1 {
                    // Unit under current assignment: propagate
                    let ci = self.clause_meta.len() as u32;
                    let start = self.clause_lits.len() as u32;
                    self.clause_lits.extend_from_slice(&lits);
                    self.clause_meta.push(ClauseMeta { start, len: lits.len() as u16, learnt: false, lbd: 0, deleted: false });
                    self.enqueue(lits[0], Reason::Clause(ci));
                    if self.propagate().is_some() {
                        self.ok = false;
                    }
                    return;
                }
                // At least two non-false literals: normal 2WL setup
                let ci = self.clause_meta.len() as u32;
                let start = self.clause_lits.len() as u32;
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

    /// Add a "sum is in a set" constraint: `#{i : lit_i true} ∈ V`.
    ///
    /// `values` must be deduplicated cardinality targets in `0..=lits.len()`;
    /// the method sorts its own copy.  Empty `values` immediately marks the
    /// solver UNSAT (`ok = false`).  Each literal's variable is watched; the
    /// constraint propagates via binary search over V against the running
    /// `(cnt_lo, cnt_hi)` bounds (see `PbSetEqConstraint` for the rules).
    pub fn add_pb_set_eq(&mut self, lits: &[i32], values: &[u32]) {
        if !self.ok { return; }
        if values.is_empty() {
            self.ok = false;
            return;
        }
        // Ensure vars; reject zero literals.
        for &lit in lits {
            assert!(lit != 0, "0 is not a valid SAT literal");
            self.ensure_var(lit.unsigned_abs() as usize);
        }
        // Validate / dedupe / sort.
        let mut vals: Vec<u32> = values.to_vec();
        vals.sort_unstable();
        vals.dedup();
        let l_len = lits.len() as u32;
        // Drop any out-of-range values (defensive: caller may pass slack).
        vals.retain(|&v| v <= l_len);
        if vals.is_empty() {
            self.ok = false;
            return;
        }

        let pi = self.pb_set_eq_constraints.len() as u32;
        for &lit in lits {
            let v = var_of(lit);
            if !self.pb_set_eq_var_watches[v].contains(&pi) {
                self.pb_set_eq_var_watches[v].push(pi);
            }
        }
        self.pb_set_eq_constraints.push(PbSetEqConstraint {
            lits: lits.to_vec(),
            values: vals,
            num_true: 0,    // scratch — recomputed by propagate_pb_set_eq
            num_undef: 0,   // scratch — recomputed by propagate_pb_set_eq
        });
        if self.propagate_pb_set_eq(pi).is_some() {
            self.ok = false;
        }
    }

    /// Recompute `(num_true, num_undef)` from the current assignment.
    /// Called unconditionally at the start of every `propagate_pb_set_eq`.
    fn recompute_pb_set_eq(&mut self, pi: u32) {
        let n_lits = self.pb_set_eq_constraints[pi as usize].lits.len();
        let mut nt: u32 = 0;
        let mut nu: u32 = 0;
        for i in 0..n_lits {
            let lit = self.pb_set_eq_constraints[pi as usize].lits[i];
            match self.lit_value(lit) {
                LBool::True => nt += 1,
                LBool::Undef => nu += 1,
                LBool::False => {}
            }
        }
        let pc = &mut self.pb_set_eq_constraints[pi as usize];
        pc.num_true = nt;
        pc.num_undef = nu;
    }

    /// Propagate a PbSetEq constraint.  Returns `Some(Reason::PbSetEq(pi))`
    /// when the constraint is infeasible under the current assignment.
    ///
    /// NOTE (2026-04-15): always recount from the trail.  The incremental
    /// `(num_true, num_undef)` counters updated by the main propagate loop
    /// only reflect the single variable currently being processed — they
    /// can lag behind the real assignment state when prior propagators in
    /// the same iteration (e.g. QuadPb, or this PbSetEq's own
    /// `force_pb_set_eq_dir`) enqueued additional lits that haven't yet
    /// been picked up by the main loop.  Trusting the incremental counters
    /// here produced false-UNSAT conclusions (V_alive empty) when reality
    /// had plenty of valid counts.  Mirrors the XOR propagator's "recount
    /// unknowns from scratch" fix.
    fn propagate_pb_set_eq(&mut self, pi: u32) -> Option<Reason> {
        // Unconditional recount.  O(|lits|) per call; acceptable because
        // PbSetEq constraints are small (≤ 2n lits) and propagate fires
        // infrequently.
        self.recompute_pb_set_eq(pi);
        let pc = &self.pb_set_eq_constraints[pi as usize];
        let cnt_lo = pc.num_true;
        let cnt_hi = pc.num_true + pc.num_undef;

        // V_alive = values ∩ [cnt_lo, cnt_hi] via binary search on sorted values.
        let lo_idx = pc.values.partition_point(|&v| v < cnt_lo);
        let hi_idx = pc.values.partition_point(|&v| v <= cnt_hi);
        if lo_idx >= hi_idx {
            return Some(Reason::PbSetEq(pi)); // V_alive == ∅
        }
        let alive_len = hi_idx - lo_idx;
        let min_alive = pc.values[lo_idx];
        let max_alive = pc.values[hi_idx - 1];

        if alive_len == 1 {
            let v = min_alive;
            if v == cnt_lo {
                // all unassigned lits must be false
                return self.force_pb_set_eq_dir(pi, false);
            }
            if v == cnt_hi {
                // all unassigned lits must be true
                return self.force_pb_set_eq_dir(pi, true);
            }
            // need a mix — no unit propagation, SAT will branch
            return None;
        }
        // |V_alive| > 1: boundary forcings.
        if cnt_lo == max_alive {
            return self.force_pb_set_eq_dir(pi, false);
        }
        if cnt_hi == min_alive {
            return self.force_pb_set_eq_dir(pi, true);
        }
        None
    }

    /// Force every **unassigned** literal in the constraint to the given polarity.
    /// `true_dir = true` ⇒ enqueue the positive literal; `false` ⇒ its negation.
    /// Already-assigned lits are silently skipped — their contribution is
    /// already reflected in `(num_true, num_undef)` so they can't re-conflict
    /// via this path (an actual conflict shows up as empty `V_alive` at the
    /// next propagate call).
    fn force_pb_set_eq_dir(&mut self, pi: u32, true_dir: bool) -> Option<Reason> {
        let n_lits = self.pb_set_eq_constraints[pi as usize].lits.len();
        for i in 0..n_lits {
            let lit = self.pb_set_eq_constraints[pi as usize].lits[i];
            if self.lit_value(lit) != LBool::Undef { continue; }
            let forced = if true_dir { lit } else { -lit };
            self.enqueue(forced, Reason::PbSetEq(pi));
        }
        None
    }

    /// Add a quadratic PB equality: sum(coeffs[i] * lits_a[i] * lits_b[i]) = target.
    /// Each term is 1 iff both lits_a[i] and lits_b[i] are true (under their polarities).
    pub fn add_quad_pb_eq(&mut self, lits_a: &[i32], lits_b: &[i32], coeffs: &[u32], target: u32) {
        if !self.ok { return; }
        assert_eq!(lits_a.len(), lits_b.len());
        assert_eq!(lits_a.len(), coeffs.len());

        // Skip ensure_var when all variables are known to exist already
        let max_var = lits_a.iter().chain(lits_b.iter())
            .map(|&l| l.unsigned_abs() as usize).max().unwrap_or(0);
        if max_var > self.num_vars {
            for &lit in lits_a.iter().chain(lits_b.iter()) {
                self.ensure_var(lit.unsigned_abs() as usize);
            }
        }

        let qi = self.quad_pb_constraints.len() as u32;

        // Dedup watches via O(1) last() check (see add_quad_pb_range).
        for i in 0..lits_a.len() {
            let va = var_of(lits_a[i]);
            let vb = var_of(lits_b[i]);
            if self.quad_pb_var_watches[va].last() != Some(&qi) {
                self.quad_pb_var_watches[va].push(qi);
            }
            if self.quad_pb_var_watches[vb].last() != Some(&qi) {
                self.quad_pb_var_watches[vb].push(qi);
            }
            self.quad_pb_var_terms[va].push((qi, i as u16, true));
            self.quad_pb_var_terms[vb].push((qi, i as u16, false));
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
            target_hi: target,
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

    /// Add a quadratic PB range constraint: target_lo ≤ Σ(coeffs[i] * lits_a[i] * lits_b[i]) ≤ target_hi
    /// Same as add_quad_pb_eq but with a range instead of exact target.
    pub fn add_quad_pb_range(&mut self, lits_a: &[i32], lits_b: &[i32], coeffs: &[u32], target_lo: u32, target_hi: u32) {
        if !self.ok { return; }
        if target_lo == target_hi {
            self.add_quad_pb_eq(lits_a, lits_b, coeffs, target_lo);
            return;
        }
        assert_eq!(lits_a.len(), lits_b.len());
        assert_eq!(lits_a.len(), coeffs.len());

        // Skip ensure_var when all variables are known to exist already
        // (common in checkpoint/restore path where base solver has all vars)
        let max_var = lits_a.iter().chain(lits_b.iter())
            .map(|&l| l.unsigned_abs() as usize).max().unwrap_or(0);
        if max_var > self.num_vars {
            for &lit in lits_a.iter().chain(lits_b.iter()) {
                self.ensure_var(lit.unsigned_abs() as usize);
            }
        }

        let qi = self.quad_pb_constraints.len() as u32;

        // Dedup watches: qi is monotonically increasing across
        // add_quad_pb_range calls, so within this call qi can only be
        // present as the LAST entry of watches[v] (added by a prior
        // term of THIS constraint). An O(1) last() check replaces the
        // prior O(n) contains() scan.
        for i in 0..lits_a.len() {
            let va = var_of(lits_a[i]);
            let vb = var_of(lits_b[i]);
            if self.quad_pb_var_watches[va].last() != Some(&qi) {
                self.quad_pb_var_watches[va].push(qi);
            }
            if self.quad_pb_var_watches[vb].last() != Some(&qi) {
                self.quad_pb_var_watches[vb].push(qi);
            }
            self.quad_pb_var_terms[va].push((qi, i as u16, true));
            self.quad_pb_var_terms[vb].push((qi, i as u16, false));
        }

        let terms: Vec<QuadPbTerm> = (0..lits_a.len()).map(|i| {
            QuadPbTerm {
                lit_a: lits_a[i],
                lit_b: lits_b[i],
                coeff: coeffs[i] as u16,
                var_a: var_of(lits_a[i]) as u16,
                var_b: var_of(lits_b[i]) as u16,
                state: 1,
                tv_offset: (if lits_a[i] < 0 { 2u8 } else { 0 }) + (if lits_b[i] < 0 { 1 } else { 0 }),
            }
        }).collect();
        self.quad_pb_constraints.push(QuadPbConstraint {
            target: target_lo,
            target_hi,
            num_terms: terms.len() as u32,
            sums: [0, coeffs.iter().sum::<u32>() as i32, 0],
            terms,
            stale: true,
        });

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

    /// Add an MDD constraint over boundary variable pairs.
    /// `nodes` is the MDD node table (nodes[0] = dead sentinel).
    /// `level_x_vars` and `level_y_vars` are 1-based SAT variable IDs for each level.
    /// The solver will enforce that the boundary variables follow a valid MDD path.
    pub fn add_mdd_constraint(
        &mut self,
        nodes: &[[u32; 4]],
        root: u32,
        depth: usize,
        level_x_vars_1based: &[i32],
        level_y_vars_1based: &[i32],
    ) {
        assert_eq!(level_x_vars_1based.len(), depth);
        assert_eq!(level_y_vars_1based.len(), depth);

        // Ensure all variables exist
        for &v in level_x_vars_1based { self.ensure_var(v.unsigned_abs() as usize); }
        for &v in level_y_vars_1based { self.ensure_var(v.unsigned_abs() as usize); }

        let lx: Vec<usize> = level_x_vars_1based.iter().map(|&v| v.unsigned_abs() as usize - 1).collect();
        let ly: Vec<usize> = level_y_vars_1based.iter().map(|&v| v.unsigned_abs() as usize - 1).collect();

        let max_var = lx.iter().chain(ly.iter()).copied().max().unwrap_or(0);
        let mut var_to_level = vec![usize::MAX; max_var + 1];
        let mut var_is_x = vec![false; max_var + 1];
        for (level, &v) in lx.iter().enumerate() {
            var_to_level[v] = level;
            var_is_x[v] = true;
        }
        for (level, &v) in ly.iter().enumerate() {
            var_to_level[v] = level;
            var_is_x[v] = false;
        }

        let num_nodes = nodes.len();
        self.mdd = Some(MddConstraint {
            nodes: nodes.to_vec(),
            root, depth,
            level_x_var: lx,
            level_y_var: ly,
            var_to_level,
            var_is_x,
            level_frontier: {
                let mut f: Vec<Vec<u32>> = (0..=depth).map(|_| Vec::with_capacity(64)).collect();
                f[0].push(root);
                f
            },
            // Start dirty from level 0 so the first propagate_mdd populates
            // level_frontier[1..=depth] from root.
            dirty_level: 0,
            scratch_seen: vec![false; num_nodes],
            scratch_seen_list: Vec::with_capacity(64),
            scratch_next: Vec::with_capacity(64),
        });
        // Diagnostic (enable with MDD_DEBUG=1)
        if std::env::var("MDD_DEBUG").ok().as_deref() == Some("1") {
            let mdd = self.mdd.as_ref().unwrap();
            let mut count = 0;
            let mut stack = vec![mdd.root];
            let mut seen = std::collections::HashSet::new();
            while let Some(nid) = stack.pop() {
                if nid == 0 || nid == u32::MAX { continue; }
                if !seen.insert(nid) { continue; }
                count += 1;
                for &c in &mdd.nodes[nid as usize] { stack.push(c); }
            }
            eprintln!("[MDD] root={} depth={} reachable_nodes={} x_vars={:?} y_vars={:?}",
                mdd.root, mdd.depth, count, &mdd.level_x_var[..mdd.depth.min(4)], &mdd.level_y_var[..mdd.depth.min(4)]);
        }
    }

    /// Propagate MDD constraint. Returns conflict reason if dead-end, None otherwise.
    /// Uses top-down frontier BFS: walk MDD levels from `dirty_level` forward,
    /// filtering nodes by assigned vars. When only one branch is viable at a
    /// level, force the implied variable.
    ///
    /// Perf-critical: called on every assignment of an MDD variable. Uses
    /// `scratch_seen` bitset for O(1) next-frontier dedup (vs. O(n) contains),
    /// swap-based buffer reuse to avoid per-level Vec::clone, and incremental
    /// `dirty_level` maintenance on backtrack so we don't rewalk levels whose
    /// frontiers are still valid.
    fn propagate_mdd(&mut self) -> Option<Reason> {
        const MDD_DEAD: u32 = 0;
        const MDD_LEAF: u32 = u32::MAX;

        let mdd_ref = match self.mdd.as_ref() { Some(m) => m, None => return None };
        if mdd_ref.root == MDD_DEAD { return Some(Reason::Mdd); }

        // Read MDD fields via raw pointer to avoid borrow issues with self.assigns.
        let mdd_ptr = self.mdd.as_mut().unwrap() as *mut MddConstraint;
        let mdd: &mut MddConstraint = unsafe { &mut *mdd_ptr };
        let start = mdd.dirty_level;
        let depth = mdd.depth;
        let nodes = &mdd.nodes as *const Vec<[u32; 4]>;
        let level_x = &mdd.level_x_var as *const Vec<usize>;
        let level_y = &mdd.level_y_var as *const Vec<usize>;

        let mut forced: [Lit; 4] = [0; 4];
        let mut num_forced: usize = 0;
        let mut conflict = false;
        let mut last_computed_level: Option<usize> = None;

        for level in start..depth {
            let xv = unsafe { &*level_x }[level];
            let yv = unsafe { &*level_y }[level];
            let x_asgn = self.assigns[xv];
            let y_asgn = self.assigns[yv];

            let nodes_ref = unsafe { &*nodes };

            // Take scratch_next out for push access without borrow conflicts.
            let mut next = std::mem::take(&mut mdd.scratch_next);
            next.clear();
            // scratch_seen_list contains previously-set indices; clear them.
            for &idx in &mdd.scratch_seen_list { mdd.scratch_seen[idx as usize] = false; }
            mdd.scratch_seen_list.clear();

            // Dedup helper implemented inline (closures fight the borrow checker
            // here because `next` is a local but seen/seen_list live on mdd).
            // `mark_and_push(c)` pushes c iff not already seen at this level.
            macro_rules! push_dedup {
                ($c:expr) => {{
                    let c = $c;
                    if c == MDD_LEAF {
                        // LEAF sentinel collapses to "at most one per frontier"
                        // via a separate check — use a reserved high index in
                        // scratch_seen's last slot if needed. Simple path:
                        // scan only the small tail in rare LEAF runs.
                        if !next.contains(&MDD_LEAF) { next.push(MDD_LEAF); }
                    } else {
                        let ci = c as usize;
                        if !mdd.scratch_seen[ci] {
                            mdd.scratch_seen[ci] = true;
                            mdd.scratch_seen_list.push(c);
                            next.push(c);
                        }
                    }
                }};
            }

            let frontier: &Vec<u32> = &mdd.level_frontier[level];

            if x_asgn != LBool::Undef && y_asgn != LBool::Undef {
                let branch = (x_asgn == LBool::True) as usize | (((y_asgn == LBool::True) as usize) << 1);
                for &nid in frontier {
                    if nid == MDD_LEAF { push_dedup!(MDD_LEAF); }
                    else {
                        let c = nodes_ref[nid as usize][branch];
                        if c != MDD_DEAD { push_dedup!(c); }
                    }
                }
            } else if x_asgn != LBool::Undef {
                let b0 = (x_asgn == LBool::True) as usize;
                let b1 = b0 | 2;
                let (mut y0_ok, mut y1_ok) = (false, false);
                for &nid in frontier {
                    if nid == MDD_LEAF { y0_ok = true; y1_ok = true; push_dedup!(MDD_LEAF); }
                    else {
                        let (c0, c1) = (nodes_ref[nid as usize][b0], nodes_ref[nid as usize][b1]);
                        if c0 != MDD_DEAD { y0_ok = true; push_dedup!(c0); }
                        if c1 != MDD_DEAD { y1_ok = true; push_dedup!(c1); }
                    }
                }
                if !y0_ok && !y1_ok { conflict = true; }
                else if !y0_ok && self.assigns[yv] == LBool::Undef {
                    forced[num_forced] = (yv + 1) as Lit; num_forced += 1;
                } else if !y1_ok && self.assigns[yv] == LBool::Undef {
                    forced[num_forced] = -((yv + 1) as Lit); num_forced += 1;
                }
            } else if y_asgn != LBool::Undef {
                let b0 = ((y_asgn == LBool::True) as usize) << 1;
                let b1 = b0 | 1;
                let (mut x0_ok, mut x1_ok) = (false, false);
                for &nid in frontier {
                    if nid == MDD_LEAF { x0_ok = true; x1_ok = true; push_dedup!(MDD_LEAF); }
                    else {
                        let (c0, c1) = (nodes_ref[nid as usize][b0], nodes_ref[nid as usize][b1]);
                        if c0 != MDD_DEAD { x0_ok = true; push_dedup!(c0); }
                        if c1 != MDD_DEAD { x1_ok = true; push_dedup!(c1); }
                    }
                }
                if !x0_ok && !x1_ok { conflict = true; }
                else if !x0_ok && self.assigns[xv] == LBool::Undef {
                    forced[num_forced] = (xv + 1) as Lit; num_forced += 1;
                } else if !x1_ok && self.assigns[xv] == LBool::Undef {
                    forced[num_forced] = -((xv + 1) as Lit); num_forced += 1;
                }
            } else {
                let (mut x0_ok, mut x1_ok, mut y0_ok, mut y1_ok) = (false, false, false, false);
                for &nid in frontier {
                    if nid == MDD_LEAF {
                        x0_ok = true; x1_ok = true; y0_ok = true; y1_ok = true;
                        push_dedup!(MDD_LEAF);
                    } else {
                        for b in 0..4usize {
                            let c = nodes_ref[nid as usize][b];
                            if c != MDD_DEAD {
                                if b & 1 == 0 { x0_ok = true; } else { x1_ok = true; }
                                if b & 2 == 0 { y0_ok = true; } else { y1_ok = true; }
                                push_dedup!(c);
                            }
                        }
                    }
                }
                if !x0_ok && !x1_ok { conflict = true; }
                else if !y0_ok && !y1_ok { conflict = true; }
                else {
                    if !x0_ok && self.assigns[xv] == LBool::Undef {
                        forced[num_forced] = (xv + 1) as Lit; num_forced += 1;
                    }
                    if !x1_ok && self.assigns[xv] == LBool::Undef {
                        forced[num_forced] = -((xv + 1) as Lit); num_forced += 1;
                    }
                    if !y0_ok && self.assigns[yv] == LBool::Undef {
                        forced[num_forced] = (yv + 1) as Lit; num_forced += 1;
                    }
                    if !y1_ok && self.assigns[yv] == LBool::Undef {
                        forced[num_forced] = -((yv + 1) as Lit); num_forced += 1;
                    }
                }
            }

            // Swap the populated next-buffer into level_frontier[level+1] and
            // take the old vec out as the scratch for the next iteration.
            if !conflict && level + 1 <= depth {
                std::mem::swap(&mut mdd.level_frontier[level + 1], &mut next);
                last_computed_level = Some(level + 1);
            }
            // Return the (now-old) vec to scratch_next for reuse.
            mdd.scratch_next = next;

            if conflict { break; }
            if num_forced > 0 { break; } // let forced vars trigger re-propagation
        }
        if let Some(l) = last_computed_level { mdd.dirty_level = l; }

        if conflict { return Some(Reason::Mdd); }

        for i in 0..num_forced {
            let flit = forced[i];
            if self.lit_value(flit) == LBool::False { return Some(Reason::Mdd); }
            if self.lit_value(flit) == LBool::Undef {
                self.enqueue(flit, Reason::Mdd);
            }
        }

        None
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

        // Backtrack to level 0 before each solve to support incremental solving
        // (e.g. adding blocking clauses between solves). The previous SAT result
        // may have left a full assignment in place.
        if self.decision_level() > 0 {
            self.backtrack(0);
        }

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

    /// Unit-propagate under temporary assumptions — NO decisions made.
    ///
    /// Returns `Some(true)` if propagation saturated without conflict;
    /// caller may read `value(var)` to inspect literals forced by the
    /// assumptions. Returns `Some(false)` if propagation hits a conflict;
    /// in the conflict case a simple nogood (the disjunction of negated
    /// assumption literals) is added to the clause database so future
    /// calls with the same prefix short-circuit to UNSAT via a single
    /// propagation step. Returns `None` never.
    ///
    /// Unlike `solve_with_assumptions`, this never calls `solve_inner`
    /// so it never makes a CDCL decision. Cost is proportional to new
    /// propagation work.
    ///
    /// Does NOT learn clauses on conflict. A 1-UIP variant was tried and
    /// reverted: enqueuing an asserting literal with the learnt clause
    /// as its reason polluted the solver's internal invariants in a way
    /// that incorrectly rejected known-SAT prefixes on subsequent calls.
    /// See commit history. Caller should rely on the walker-side memo for
    /// dedup of UNSAT sub-trees instead.
    ///
    /// State after the call:
    /// - `Some(true)` + non-empty assumptions → solver at decision level 1.
    /// - `Some(true)` + empty assumptions → solver at decision level 0.
    /// - `Some(false)` → solver at decision level 0.
    pub fn propagate_only(&mut self, assumptions: &[Lit]) -> Option<bool> {
        if !self.ok { return Some(false); }

        if self.decision_level() > 0 {
            self.backtrack(0);
        }

        // Pre-size reusable buffers (mirrors solve_with_assumptions) so
        // propagators that touch them don't thrash on first call.
        if self.quad_pb_seen_buf.len() < self.num_vars {
            self.quad_pb_seen_buf.resize(self.num_vars, false);
        }
        if self.analyze_seen.len() < self.num_vars {
            self.analyze_seen.resize(self.num_vars, false);
        }
        if self.minimize_visited.len() < self.num_vars {
            self.minimize_visited.resize(self.num_vars, false);
        }

        // Drain any pending level-0 work (unit clauses added since the
        // last solve, etc.).
        if self.propagate().is_some() {
            self.ok = false;
            return Some(false);
        }

        if assumptions.is_empty() {
            return Some(true);
        }

        self.new_decision_level();
        for &lit in assumptions {
            self.ensure_var(lit.unsigned_abs() as usize);
            match self.lit_value(lit) {
                LBool::True => {}
                LBool::False => {
                    // The assumption itself contradicts a level-0 fact
                    // (or an earlier assumption in this batch). A clause
                    // that rules out this assumption already exists in
                    // the DB; no new learning needed.
                    self.backtrack(0);
                    return Some(false);
                }
                LBool::Undef => {
                    self.enqueue(lit, Reason::Decision);
                }
            }
        }

        if self.propagate().is_some() {
            // Nogood: the disjunction of negated assumption literals.
            // Sound because the conjunction of assumptions just hit a
            // solver-level conflict, so `¬a_1 ∨ … ∨ ¬a_k` is a valid
            // consequence of the root clause DB. Future calls with the
            // same (or overlapping) prefix short-circuit via unit
            // propagation on the nogood.
            //
            // We deliberately do NOT use analyze() here: its 1-UIP
            // logic takes a "Reason::Decision" shortcut at the first
            // decision it walks to, producing a UNIT clause that's
            // only valid under the OTHER assumptions still in scope.
            // That's unsound as a permanent (level-0) clause and in
            // earlier attempts caused known-SAT prefixes of TT(8)+
            // to be incorrectly rejected.
            self.backtrack(0);
            let mut nogood: Vec<Lit> = Vec::with_capacity(assumptions.len());
            for &lit in assumptions {
                match self.lit_value(lit) {
                    LBool::True | LBool::Undef => nogood.push(-lit),
                    LBool::False => {
                        // Assumption is already root-level false; the
                        // prefix is trivially UNSAT via an existing
                        // clause. No new learning needed.
                        return Some(false);
                    }
                }
            }
            if nogood.is_empty() {
                self.ok = false;
            } else {
                self.add_clause(nogood);
            }
            return Some(false);
        }

        Some(true)
    }

    /// Number of variables.
    pub fn num_vars(&self) -> usize { self.num_vars }
    /// Number of active (non-deleted) clauses.
    /// Verify all quad PB constraint states match actual variable assignments.
    /// Returns the number of mismatched constraints found.
    pub fn verify_quad_pb_state(&self) -> usize {
        let mut bad = 0;
        for (qi, qc) in self.quad_pb_constraints.iter().enumerate() {
            if qc.stale { continue; } // stale will be recomputed
            let mut expected_sums = [0i32, 0, 0];
            for ti in 0..qc.num_terms as usize {
                let t = &qc.terms[ti];
                let aa = self.assigns[t.var_a()];
                let ab = self.assigns[t.var_b()];
                let expected_state = t.compute_state(aa, ab);
                expected_sums[expected_state as usize] += t.coeff as i32;
                if t.state != expected_state {
                    if bad == 0 {
                        eprintln!("QUAD PB BUG: constraint {} term {} state={} expected={} (var_a={} val={:?}, var_b={} val={:?})",
                            qi, ti, t.state, expected_state, t.var_a(), aa, t.var_b(), ab);
                    }
                    bad += 1;
                }
            }
            if qc.sums != expected_sums {
                if bad == 0 {
                    eprintln!("QUAD PB BUG: constraint {} sums={:?} expected={:?}", qi, qc.sums, expected_sums);
                }
                bad += 1;
            }
        }
        bad
    }

    /// Get all learnt clauses as Vec<Vec<Lit>> (for debugging).
    pub fn get_learnt_clauses(&self) -> Vec<Vec<Lit>> {
        self.clause_meta.iter().filter(|cm| cm.learnt && !cm.deleted).map(|cm| {
            let s = cm.start as usize;
            self.clause_lits[s..s + cm.len as usize].to_vec()
        }).collect()
    }

    /// Force recompute of ALL quad PB constraints (public, for testing).
    pub fn recompute_all_quad_pb(&mut self) {
        for i in 0..self.quad_pb_constraints.len() {
            self.recompute_quad_pb(i as u32);
        }
    }

    pub fn num_clauses(&self) -> usize {
        self.clause_meta.iter().filter(|m| !m.deleted).count()
    }
    /// Number of conflicts so far.
    pub fn num_conflicts(&self) -> u64 { self.conflicts }
    /// Number of branching decisions made so far.
    pub fn num_decisions(&self) -> u64 { self.decisions }
    /// Number of variable assignments forced by propagation (clause BCP, PB,
    /// quad PB, XOR, MDD, spectral). Excludes branching decisions.
    pub fn num_propagations(&self) -> u64 { self.propagations }
    /// Number of variables currently assigned at decision level 0 (the
    /// "forced prefix"). Diff before/after a solve to see how many vars
    /// became permanently forced by initial propagation of assumptions.
    pub fn num_level0_vars(&self) -> usize {
        self.trail_lim.first().copied().unwrap_or(self.trail.len())
    }

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

    /// Set a variable's VSIDS activity score. Higher = decided earlier.
    /// Variable is 1-based (DIMACS convention).
    pub fn set_var_activity(&mut self, var: i32, activity: f64) {
        let v = var.unsigned_abs() as usize - 1;
        self.ensure_var(v + 1);
        self.activity[v] = activity;
        // Update heap position
        if self.heap_pos[v] < self.heap.len() {
            // Sift up if activity increased
            let mut pos = self.heap_pos[v];
            while pos > 0 {
                let parent = (pos - 1) / 2;
                if self.activity[self.heap[pos]] > self.activity[self.heap[parent]] {
                    self.heap.swap(pos, parent);
                    self.heap_pos[self.heap[pos]] = pos;
                    self.heap_pos[self.heap[parent]] = parent;
                    pos = parent;
                } else { break; }
            }
        }
    }

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
        self.rebuild_watches();

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
        self.rebuild_watches();

        eliminated
    }

    /// Rebuild all watch lists from the clause database.
    /// Clears existing watches and re-adds watches for all non-deleted clauses with >= 2 literals.
    fn rebuild_watches(&mut self) {
        for wl in &mut self.watches { wl.clear(); }
        for (ci, m) in self.clause_meta.iter().enumerate() {
            if m.deleted || m.len < 2 { continue; }
            let lits = &self.clause_lits[m.start as usize..(m.start as usize + m.len as usize)];
            self.watches[lit_index(negate(lits[0]))].push((ci as u32, lits[1]));
            self.watches[lit_index(negate(lits[1]))].push((ci as u32, lits[0]));
        }
    }

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
        self.rebuild_watches();
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

    /// Copy current phase into an existing buffer (avoids allocation).
    pub fn copy_phase_into(&self, buf: &mut Vec<bool>) {
        buf.clear();
        buf.extend_from_slice(&self.phase);
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

    /// Save a checkpoint of the constraint database sizes.
    /// After calling this, new clauses/PBs/quad PBs/XORs/PbSetEq can be added
    /// and later undone with `restore_checkpoint`. Cheap: just records 7 integers.
    pub fn save_checkpoint(&self) -> (usize, usize, usize, usize, usize, usize, usize) {
        (self.clause_meta.len(), self.clause_lits.len(),
         self.pb_constraints.len(), self.num_vars,
         self.quad_pb_constraints.len(), self.xor_constraints.len(),
         self.pb_set_eq_constraints.len())
    }

    /// Restore the solver to a previous checkpoint, removing all clauses/PBs/quad PBs/XORs/PbSetEq
    /// added after the checkpoint. Backtracks, then truncates and rebuilds watches.
    pub fn restore_checkpoint(&mut self, cp: (usize, usize, usize, usize, usize, usize, usize)) {
        let (n_clauses, n_lits, n_pbs, _n_vars, n_quad_pbs, n_xors, n_pbseq) = cp;
        self.backtrack(0);

        // Mark post-checkpoint clauses as deleted
        for i in n_clauses..self.clause_meta.len() {
            self.clause_meta[i].deleted = true;
        }
        // Truncate clause storage
        self.clause_meta.truncate(n_clauses);
        self.clause_lits.truncate(n_lits);

        // Rebuild watch lists (cheaper than trying to surgically remove entries)
        for wl in &mut self.watches {
            wl.retain(|&(ci, _)| (ci as usize) < n_clauses);
        }

        // Remove post-checkpoint PB constraints
        self.pb_constraints.truncate(n_pbs);
        for wl in &mut self.pb_watches {
            wl.retain(|&ci| (ci as usize) < n_pbs);
        }

        // Remove post-checkpoint quad PB constraints and their watch entries
        if n_quad_pbs < self.quad_pb_constraints.len() {
            self.quad_pb_constraints.truncate(n_quad_pbs);
            for wl in &mut self.quad_pb_var_watches {
                wl.retain(|&qi| (qi as usize) < n_quad_pbs);
            }
            for wl in &mut self.quad_pb_var_terms {
                wl.retain(|&(qi, _, _)| (qi as usize) < n_quad_pbs);
            }
        }

        // Remove post-checkpoint XOR constraints
        if n_xors < self.xor_constraints.len() {
            self.xor_constraints.truncate(n_xors);
            for wl in &mut self.xor_var_watches {
                wl.retain(|&xi| (xi as usize) < n_xors);
            }
        }

        // Remove post-checkpoint PbSetEq constraints and their watch entries.
        // No counter reset needed: `propagate_pb_set_eq` recomputes from the
        // trail on every call.
        if n_pbseq < self.pb_set_eq_constraints.len() {
            self.pb_set_eq_constraints.truncate(n_pbseq);
            for wl in &mut self.pb_set_eq_var_watches {
                wl.retain(|&pi| (pi as usize) < n_pbseq);
            }
        }

        // Reset spectral constraint to boundary-only state
        if let Some(ref mut spec) = self.spectral {
            spec.reset();
        }

        self.conflicts = 0;
        self.restart_limit = 100;
        self.luby_index = 0;
        self.ok = true;
    }

    /// Delete all learnt clauses, backtrack, and rebuild watches.
    /// Keeps original (non-learnt) clauses, PB, quad PB, XOR intact.
    /// Use between solve_with_assumptions calls to prevent learnt clause poisoning.
    pub fn clear_learnt_clauses(&mut self) {
        self.backtrack(0);
        // Mark learnt clauses as deleted
        for cm in &mut self.clause_meta {
            if cm.learnt { cm.deleted = true; }
        }
        // Rebuild watch lists (only non-deleted clauses)
        for wl in &mut self.watches { wl.clear(); }
        for (ci, cm) in self.clause_meta.iter().enumerate() {
            if cm.deleted || cm.len < 2 { continue; }
            let start = cm.start as usize;
            let l0 = self.clause_lits[start];
            let l1 = self.clause_lits[start + 1];
            self.watches[lit_index(l0)].push((ci as u32, l1));
            self.watches[lit_index(l1)].push((ci as u32, l0));
        }
        self.conflicts = 0;
        self.restart_limit = 100;
        self.luby_index = 0;
        self.ok = true;
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
                self.decisions += 1;
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
        if !matches!(reason, Reason::Decision) {
            self.propagations += 1;
        }
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
                let has_stale = (0..self.quad_pb_var_watches[v].len()).any(|idx| {
                    let qi = self.quad_pb_var_watches[v][idx];
                    self.quad_pb_constraints[qi as usize].stale
                });
                if has_stale {
                    self.recompute_stale_quad_pb();
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
                    // Recount unknowns from scratch. The incremental num_unknown
                    // can be stale when multiple variables are enqueued before
                    // propagation (e.g. solve_with_assumptions batches assumptions).
                    let mut real_unknown = 0u32;
                    let mut real_xor = false;
                    for &xv in &self.xor_constraints[xi as usize].vars {
                        if self.assigns[xv] == LBool::Undef {
                            real_unknown += 1;
                        } else if self.assigns[xv] == LBool::True {
                            real_xor ^= true;
                        }
                    }
                    let xc = &mut self.xor_constraints[xi as usize];
                    xc.num_unknown = real_unknown;
                    xc.assigned_xor = real_xor;

                    if real_unknown == 0 {
                        if real_xor != xc.parity {
                            return Some(Reason::Xor(xi));
                        }
                    } else if real_unknown == 1 {
                        let need_true = real_xor ^ xc.parity;
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
            // PbSetEq propagation: `#{i : lit_i true} ∈ V`.
            // `propagate_pb_set_eq` recomputes the counters from the trail
            // on entry; no incremental bookkeeping is needed (and a prior
            // attempt at incremental was unsound — prior propagators in
            // the same iteration can enqueue lits this block would miss).
            if !self.pb_set_eq_constraints.is_empty() {
                let v = var_of(lit);
                for idx in 0..self.pb_set_eq_var_watches[v].len() {
                    let pi = self.pb_set_eq_var_watches[v][idx];
                    if let Some(conflict) = self.propagate_pb_set_eq(pi) {
                        return Some(conflict);
                    }
                }
            }
            // MDD constraint propagation
            if self.mdd.is_some() {
                let v = var_of(lit);
                let is_mdd_var = {
                    let mdd = self.mdd.as_ref().unwrap();
                    v < mdd.var_to_level.len() && mdd.var_to_level[v] != usize::MAX
                };
                if is_mdd_var {
                    if let Some(conflict) = self.propagate_mdd() {
                        return Some(conflict);
                    }
                }
            }
            // Spectral constraint: incrementally update DFT, check conflict, propagate
            if self.spectral.is_some() {
                let v = var_of(lit);
                let spec = self.spectral.as_mut().unwrap();
                if v < spec.num_seq_vars && !spec.assigned[v] {
                    let val: i8 = if lit > 0 { 1 } else { -1 };
                    spec.assign(v, val);
                    if spec.check_conflict().is_some() {
                        // Build conflict clause from all assigned seq vars
                        let num_sv = spec.num_seq_vars;
                        let mut cl: Vec<Lit> = Vec::with_capacity(num_sv);
                        for sv in 0..num_sv {
                            if !spec.assigned[sv] { continue; }
                            let sv_lit = (sv + 1) as Lit;
                            cl.push(if spec.values[sv] > 0 { -sv_lit } else { sv_lit });
                        }
                        let ci = self.clause_meta.len() as u32;
                        let cs = self.clause_lits.len();
                        let cn = cl.len();
                        for &l in &cl { self.clause_lits.push(l); }
                        self.clause_meta.push(ClauseMeta {
                            start: cs as u32, len: cn as u16,
                            learnt: true, deleted: false, lbd: cn.min(255) as u8,
                        });
                        if cn >= 2 {
                            self.watches[lit_index(cl[0])].push((ci, cl[1]));
                            self.watches[lit_index(cl[1])].push((ci, cl[0]));
                        }
                        return Some(Reason::Clause(ci));
                    }

                    // Unit propagation disabled (clause-based propagation causes
                    // performance regression from clause DB bloat on restore).
                    // Conflict detection above is sufficient.
                    let num_assigned = spec.assigned.iter().filter(|&&a| a).count();
                    if false && num_assigned >= spec.num_seq_vars / 2 {
                        let nf = spec.num_freqs;
                        let sqrt_bound = spec.bound.sqrt();
                        let num_sv = spec.num_seq_vars;
                        let mut forced: Vec<Lit> = Vec::new();
                        let mut conflict = false;

                        for u in 0..num_sv {
                            if spec.assigned[u] { continue; }
                            if self.assigns[u] != LBool::Undef { continue; }
                            let base = u * nf;
                            let mut pos_bad = false;
                            let mut neg_bad = false;
                            for fi in 0..nf {
                                let c = spec.cos_table[base + fi] as f64;
                                let s = spec.sin_table[base + fi] as f64;
                                let amp = spec.amplitudes[base + fi] as f64;
                                let remaining = spec.max_reduction[fi] - amp;
                                if !pos_bad {
                                    let re = spec.re[fi] + c;
                                    let im = spec.im[fi] + s;
                                    if (re*re + im*im).sqrt() - remaining > sqrt_bound {
                                        pos_bad = true;
                                    }
                                }
                                if !neg_bad {
                                    let re = spec.re[fi] - c;
                                    let im = spec.im[fi] - s;
                                    if (re*re + im*im).sqrt() - remaining > sqrt_bound {
                                        neg_bad = true;
                                    }
                                }
                                if pos_bad && neg_bad { break; }
                            }
                            if pos_bad && neg_bad { conflict = true; break; }
                            if pos_bad { forced.push(-((u + 1) as Lit)); }
                            else if neg_bad { forced.push((u + 1) as Lit); }
                        }

                        if conflict { return Some(Reason::Spectral); }
                        for flit in forced {
                            if self.lit_value(flit) == LBool::Undef {
                                self.enqueue(flit, Reason::Spectral);
                            }
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

    /// Batch-recompute all stale quad PB constraints (better cache locality
    /// than recomputing one at a time as they're encountered).
    fn recompute_stale_quad_pb(&mut self) {
        for i in 0..self.quad_pb_constraints.len() {
            if self.quad_pb_constraints[i].stale {
                self.recompute_quad_pb(i as u32);
            }
        }
    }

    /// Single-pass: finds propagation and builds explanation in one fused scan.
    /// Supports range constraints: target <= sum <= target_hi.
    #[inline]
    fn propagate_quad_pb(&mut self, qi: u32) -> Option<Reason> {
        if self.quad_pb_constraints[qi as usize].stale {
            self.recompute_stale_quad_pb();
        }
        let qc = &self.quad_pb_constraints[qi as usize];
        let n = qc.num_terms as usize;
        let target_lo = qc.target as i64;
        let target_hi = qc.target_hi as i64;
        let sum_true = qc.sums[2] as i64;
        let sum_maybe = qc.sums[1] as i64;

        if sum_true + sum_maybe < target_lo || sum_true > target_hi {
            return Some(Reason::QuadPb(qi)); // conflict
        }

        // slack_up: how many more MAYBE terms can become TRUE before exceeding lower bound requirement
        // Actually: slack_up = (sum_true + sum_maybe) - target_lo = how much we can still "lose" from maybe
        let slack_up = sum_true + sum_maybe - target_lo;
        // slack_down: how many more can become TRUE before exceeding upper bound
        let slack_down = target_hi - sum_true;
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
        // Shared logic for processing each reason literal during 1-UIP analysis.
        // Marks the variable as seen, bumps its activity, and either increments
        // the current-level counter or adds the literal to the learnt clause.
        macro_rules! process_reason_lit {
            ($self:ident, $lit:expr, $p:expr, $counter:expr, $learnt:expr, $bt_level:expr) => {{
                let lit = $lit;
                if lit != $p {
                    let v = var_of(lit);
                    if !$self.analyze_seen[v] {
                        $self.analyze_seen[v] = true;
                        $self.bump_activity(v);
                        if $self.level[v] == $self.decision_level() {
                            $counter += 1;
                        } else if $self.level[v] > 0 {
                            $learnt.push(lit);
                            $bt_level = $bt_level.max($self.level[v]);
                        }
                    }
                }
            }};
        }
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
                        process_reason_lit!(self, self.clause_lits[cstart + idx], p, counter, learnt, bt_level);
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
                        process_reason_lit!(self, self.analyze_reason_buf[idx], p, counter, learnt, bt_level);
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
                        process_reason_lit!(self, buf[idx], p, counter, learnt, bt_level);
                    }
                    self.analyze_reason_buf = buf;
                }
                Reason::Xor(xi) => {
                    // XOR reason: variables assigned BEFORE the propagated variable
                    // form the reason. Must filter by trail_pos to avoid including
                    // variables assigned after the XOR propagation (which would produce
                    // an incorrect reason when interacting with QuadPB propagation).
                    let mut buf = std::mem::take(&mut self.analyze_reason_buf);
                    buf.clear();
                    let pv = if p != 0 { var_of(p) } else { usize::MAX };
                    let pv_pos = if pv < self.num_vars { self.trail_pos[pv] } else { usize::MAX };
                    let xc = &self.xor_constraints[xi as usize];
                    for &v in &xc.vars {
                        if v == pv { continue; }
                        if self.assigns[v] == LBool::Undef { continue; }
                        // For propagation reasons (p!=0): only include vars assigned
                        // before the propagated variable on the trail.
                        // For conflict reasons (p==0): include all assigned vars.
                        if p != 0 && self.trail_pos[v] >= pv_pos { continue; }
                        let lit_v = (v + 1) as Lit;
                        let neg_lit = if self.assigns[v] == LBool::True { -lit_v } else { lit_v };
                        buf.push(neg_lit);
                    }
                    for idx in 0..buf.len() {
                        process_reason_lit!(self, buf[idx], p, counter, learnt, bt_level);
                    }
                    self.analyze_reason_buf = buf;
                }
                Reason::PbSetEq(pi) => {
                    // PbSetEq reason: all currently-assigned literals in the
                    // constraint negated (trail-pos filtered for propagation
                    // reasons).  Same shape as the Xor arm — over-approximate
                    // but sound; tightening is a future optimisation.
                    let mut buf = std::mem::take(&mut self.analyze_reason_buf);
                    buf.clear();
                    let pv = if p != 0 { var_of(p) } else { usize::MAX };
                    let pv_pos = if pv < self.num_vars { self.trail_pos[pv] } else { usize::MAX };
                    let n_lits = self.pb_set_eq_constraints[pi as usize].lits.len();
                    for i in 0..n_lits {
                        let cl = self.pb_set_eq_constraints[pi as usize].lits[i];
                        let v = var_of(cl);
                        if v == pv { continue; }
                        if self.assigns[v] == LBool::Undef { continue; }
                        if p != 0 && self.trail_pos[v] >= pv_pos { continue; }
                        // Push the negation of the literal's current truth value.
                        let cur_true = self.lit_value(cl) == LBool::True;
                        let neg_lit = if cur_true { -cl } else { cl };
                        buf.push(neg_lit);
                    }
                    for idx in 0..buf.len() {
                        process_reason_lit!(self, buf[idx], p, counter, learnt, bt_level);
                    }
                    self.analyze_reason_buf = buf;
                }
                Reason::Spectral => {
                    // Spectral reason: all assigned sequence variables contributed
                    // to the DFT violation. Return them all as the reason.
                    let mut buf = std::mem::take(&mut self.analyze_reason_buf);
                    buf.clear();
                    if let Some(ref spec) = self.spectral {
                        for v in 0..spec.num_seq_vars {
                            if spec.assigned[v] {
                                let lit_v = (v + 1) as Lit;
                                let neg_lit = if spec.values[v] > 0 { -lit_v } else { lit_v };
                                buf.push(neg_lit);
                            }
                        }
                    }
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
                Reason::Mdd => {
                    // MDD reason: all assigned boundary variables
                    let mut buf = std::mem::take(&mut self.analyze_reason_buf);
                    buf.clear();
                    if let Some(ref mdd) = self.mdd {
                        for level in 0..mdd.depth {
                            for &v in &[mdd.level_x_var[level], mdd.level_y_var[level]] {
                                if self.assigns[v] != LBool::Undef {
                                    let lit_v = (v + 1) as Lit;
                                    buf.push(if self.assigns[v] == LBool::True { -lit_v } else { lit_v });
                                }
                            }
                        }
                    }
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
                            learnt.push(negate(lit));
                            if self.level[v] > bt_level { bt_level = self.level[v]; }
                        }
                    }
                    self.analyze_reason_buf = buf;
                }
                Reason::Decision => {
                    // Reached a decision variable — MDD explanation over-approximate.
                    // Unit learnt clause: just negate(p). Handles the empty-learnt
                    // case that showed up the first time this path was actually
                    // exercised against the XY MDD (commit TODO).
                    if learnt.is_empty() {
                        learnt.push(negate(p));
                    } else {
                        learnt[0] = negate(p);
                    }
                    return (learnt, bt_level);
                }
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
                Reason::Clause(_) | Reason::Pb(_) | Reason::QuadPb(_) | Reason::Xor(_) | Reason::Spectral | Reason::Mdd | Reason::PbSetEq(_) => {
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
        // Shared logic for checking one antecedent variable during minimization.
        // Sets `fail = true` and breaks if the variable blocks removal.
        macro_rules! check_minimize_var {
            ($self:ident, $u:expr, $cur:expr, $fail:ident) => {{
                let u = $u;
                if u != $cur && !$self.minimize_visited[u] {
                    $self.minimize_visited[u] = true;
                    if $self.level[u] != 0 && !$self.analyze_seen[u] {
                        let lv = $self.level[u] as usize;
                        if lv >= $self.minimize_levels.len() || !$self.minimize_levels[lv] {
                            $fail = true;
                        } else {
                            match $self.reason[u] {
                                Reason::Decision => { $fail = true; }
                                _ => { $self.minimize_stack.push(u); }
                            }
                        }
                    }
                }
            }};
        }

        self.minimize_stack.clear();
        self.minimize_stack.push(v);
        self.minimize_visited.resize(self.num_vars, false);
        self.minimize_visited.fill(false);
        self.minimize_visited[v] = true;

        while let Some(cur) = self.minimize_stack.pop() {
            let mut fail = false;
            // Process reason literals inline to avoid allocation
            match self.reason[cur] {
                Reason::Clause(ci) => {
                    let m = self.clause_meta[ci as usize];
                    let cstart = m.start as usize;
                    let clen = m.len as usize;
                    for idx in 0..clen {
                        check_minimize_var!(self, var_of(self.clause_lits[cstart + idx]), cur, fail);
                        if fail { return false; }
                    }
                }
                Reason::Pb(pbi) => {
                    let n = self.pb_constraints[pbi as usize].lits.len();
                    for i in 0..n {
                        let lit = self.pb_constraints[pbi as usize].lits[i];
                        if self.lit_value(lit) != LBool::False { continue; }
                        check_minimize_var!(self, var_of(lit), cur, fail);
                        if fail { return false; }
                    }
                }
                Reason::QuadPb(qi_encoded) => {
                    let mut buf2 = std::mem::take(&mut self.analyze_reason_buf2);
                    self.compute_quad_pb_explanation_into(qi_encoded, cur, &mut buf2);
                    for idx in 0..buf2.len() {
                        check_minimize_var!(self, var_of(buf2[idx]), cur, fail);
                        if fail { break; }
                    }
                    self.analyze_reason_buf2 = buf2;
                    if fail { return false; }
                }
                Reason::Xor(xi) => {
                    let xc = &self.xor_constraints[xi as usize];
                    for vi in 0..xc.vars.len() {
                        let u = xc.vars[vi];
                        if self.assigns[u] == LBool::Undef { continue; }
                        check_minimize_var!(self, u, cur, fail);
                        if fail { return false; }
                    }
                }
                Reason::PbSetEq(pi) => {
                    let n_lits = self.pb_set_eq_constraints[pi as usize].lits.len();
                    for i in 0..n_lits {
                        let lit = self.pb_set_eq_constraints[pi as usize].lits[i];
                        let u = var_of(lit);
                        if self.assigns[u] == LBool::Undef { continue; }
                        check_minimize_var!(self, u, cur, fail);
                        if fail { return false; }
                    }
                }
                Reason::Spectral => {
                    // Spectral reason: all assigned sequence vars
                    if let Some(ref spec) = self.spectral {
                        for v in 0..spec.num_seq_vars {
                            if !spec.assigned[v] { continue; }
                            if v == cur || self.minimize_visited[v] { continue; }
                            self.minimize_visited[v] = true;
                            if self.level[v] == 0 { continue; }
                            if self.analyze_seen[v] { continue; }
                            let lv = self.level[v] as usize;
                            if lv >= self.minimize_levels.len() || !self.minimize_levels[lv] { return false; }
                            match self.reason[v] {
                                Reason::Decision => return false,
                                _ => { self.minimize_stack.push(v); }
                            }
                        }
                    }
                }
                Reason::Mdd => {
                    if let Some(ref mdd) = self.mdd {
                        for level in 0..mdd.depth {
                            for &v in &[mdd.level_x_var[level], mdd.level_y_var[level]] {
                                if self.assigns[v] == LBool::Undef { continue; }
                                if v == cur || self.minimize_visited[v] { continue; }
                                self.minimize_visited[v] = true;
                                if self.level[v] == 0 { continue; }
                                if self.analyze_seen[v] { continue; }
                                let lv = self.level[v] as usize;
                                if lv >= self.minimize_levels.len() || !self.minimize_levels[lv] { return false; }
                                match self.reason[v] {
                                    Reason::Decision => return false,
                                    _ => { self.minimize_stack.push(v); }
                                }
                            }
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
            // Undo spectral constraint
            if let Some(ref mut spec) = self.spectral {
                if v < spec.num_seq_vars && spec.assigned[v] {
                    spec.unassign(v);
                }
            }
            // Raise MDD dirty_level to this variable's level: the frontier at
            // that level and above becomes stale (the assignment that produced
            // it is being undone), but frontiers below it are still valid.
            if let Some(ref mut mdd) = self.mdd {
                if v < mdd.var_to_level.len() && mdd.var_to_level[v] != usize::MAX {
                    let l = mdd.var_to_level[v];
                    if l < mdd.dirty_level { mdd.dirty_level = l; }
                }
            }
            // Mark quad PB constraints involving this variable as stale.
            // Skip for level 0 when caller manages state externally (table path).
            if !(level == 0 && self.skip_backtrack_quad_pb) {
                for idx in 0..self.quad_pb_var_watches[v].len() {
                    let qi = self.quad_pb_var_watches[v][idx];
                    self.quad_pb_constraints[qi as usize].stale = true;
                }
            }
            // No PbSetEq invalidation needed: `propagate_pb_set_eq`
            // recomputes counters from the trail on every call.
            self.heap_insert(v);
        }
        self.trail_lim.truncate(level as usize);
        self.prop_head = self.trail.len();

        // XOR incremental state is updated during propagation, not enqueue.
        // A conflict can arise before a freshly enqueued literal reaches the XOR
        // propagation phase, so blindly undoing all popped trail entries is
        // unsound. Recompute from the surviving assignment instead.
        if !self.xor_constraints.is_empty() {
            for xc in &mut self.xor_constraints {
                let mut num_unknown = xc.vars.len() as u32;
                let mut assigned_xor = false;
                for &v in &xc.vars {
                    if self.assigns[v] != LBool::Undef {
                        num_unknown -= 1;
                        if self.assigns[v] == LBool::True {
                            assigned_xor ^= true;
                        }
                    }
                }
                xc.num_unknown = num_unknown;
                xc.assigned_xor = assigned_xor;
            }
        }

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

    /// Add a learnt clause. If `enqueue_asserting` is true, enqueue lits[0] as
    /// the asserting literal (normal CDCL). If false, skip enqueueing (used for
    /// chronological backtracking where the clause isn't unit at the current level).
    fn add_learnt_clause_inner(&mut self, lits: Vec<Lit>, enqueue_asserting: bool) {
        if lits.len() == 1 {
            // Unit learnt clause: always enqueue at level 0
            self.enqueue(lits[0], Reason::Decision);
            return;
        }

        let ci = self.clause_meta.len() as u32;
        let lbd = self.compute_lbd(&lits);
        let start = self.clause_lits.len() as u32;

        // Watch the first two literals (blocker = the other watched lit)
        self.watches[lit_index(negate(lits[0]))].push((ci, lits[1]));
        self.watches[lit_index(negate(lits[1]))].push((ci, lits[0]));
        self.clause_lits.extend_from_slice(&lits);
        self.clause_meta.push(ClauseMeta { start, len: lits.len() as u16, learnt: true, lbd: lbd as u8, deleted: false });

        if enqueue_asserting {
            self.enqueue(lits[0], Reason::Clause(ci));
        }
    }

    /// Add a learnt clause and enqueue the asserting literal.
    fn add_learnt_clause(&mut self, lits: Vec<Lit>) {
        self.add_learnt_clause_inner(lits, true);
    }

    /// Add a learnt clause WITHOUT enqueueing the asserting literal.
    /// Used for chronological backtracking where the clause isn't unit.
    fn add_learnt_clause_no_enqueue(&mut self, lits: Vec<Lit>) {
        self.add_learnt_clause_inner(lits, false);
    }

    /// Compute LBD (Literal Block Distance) of a clause.
    fn compute_lbd(&mut self, lits: &[Lit]) -> u32 {
        let needed = self.decision_level() as usize + 1;
        if self.lbd_seen.len() < needed {
            self.lbd_seen.resize(needed, false);
        }
        let mut count = 0u32;
        for &lit in lits {
            let lv = self.level[var_of(lit)] as usize;
            if lv < needed && !self.lbd_seen[lv] {
                self.lbd_seen[lv] = true;
                count += 1;
            }
        }
        // Clear only touched entries
        for &lit in lits {
            let lv = self.level[var_of(lit)] as usize;
            if lv < needed {
                self.lbd_seen[lv] = false;
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

    fn build_xor_quad_pb_no_gj_n26_solver(enable_xor: bool) -> Solver {
        let n = 26usize;
        let m = 25usize;
        let z: Vec<i8> = "+++-+--++++++--++---+-+--+".chars().map(|c| if c=='+' { 1 } else { -1 }).collect();
        let w: Vec<i8> = "++++-+---+--+++--++++-+-+".chars().map(|c| if c=='+' { 1 } else { -1 }).collect();

        let mut s = Solver::new();
        s.config.xor_propagation = enable_xor;
        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };
        s.add_clause([x_var(0)]);
        s.add_clause([y_var(0)]);
        let x_lits: Vec<i32> = (0..n).map(|i| x_var(i)).collect();
        let y_lits: Vec<i32> = (0..n).map(|i| y_var(i)).collect();
        let ones_n: Vec<u32> = vec![1; n];
        s.add_pb_eq(&x_lits, &ones_n, 16);
        s.add_pb_eq(&y_lits, &ones_n, 16);

        let mut zw_ac = vec![0i32; n];
        for lag in 1..n {
            let nz: i32 = (0..n-lag).map(|i| z[i] as i32 * z[i+lag] as i32).sum();
            let nw: i32 = if lag < m { (0..m-lag).map(|i| w[i] as i32 * w[i+lag] as i32).sum() } else { 0 };
            zw_ac[lag] = 2*nz + 2*nw;
        }

        for lag in 1..n {
            let target = ((2*(n-lag) as i32 - zw_ac[lag]) / 2) as u32;
            let mut la = Vec::new();
            let mut lb = Vec::new();
            for i in 0..(n-lag) {
                la.push(x_var(i)); lb.push(x_var(i+lag));
                la.push(-x_var(i)); lb.push(-x_var(i+lag));
            }
            for i in 0..(n-lag) {
                la.push(y_var(i)); lb.push(y_var(i+lag));
                la.push(-y_var(i)); lb.push(-y_var(i+lag));
            }
            let coeffs: Vec<u32> = vec![1; la.len()];
            s.add_quad_pb_eq(&la, &lb, &coeffs, target);
        }

        if enable_xor {
            for lag in 1..n {
                let target = ((2*(n-lag) as i32 - zw_ac[lag]) / 2) as usize;
                let k = 2*(n-lag);
                let parity = ((target + k) % 2) == 1;
                let mut in_xor = vec![false; 2*n];
                for i in 0..(n-lag) {
                    in_xor[i] ^= true;
                    in_xor[i+lag] ^= true;
                }
                for i in 0..(n-lag) {
                    in_xor[n+i] ^= true;
                    in_xor[n+i+lag] ^= true;
                }
                let vars: Vec<i32> = in_xor.iter().enumerate()
                    .filter(|&(_, &v)| v)
                    .map(|(i, _)| (i + 1) as i32)
                    .collect();
                if !vars.is_empty() {
                    s.add_xor(&vars, parity);
                }
            }
        }

        s.reserve_for_search(200);
        s
    }

    fn model_lit(s: &Solver, var: usize) -> Lit {
        if s.value(var as i32) == Some(true) {
            var as Lit
        } else {
            -(var as Lit)
        }
    }

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
    fn search_stats_pure_propagation() {
        // Two unit clauses force both vars at add_clause time (level 0).
        // No branching should be needed at solve.
        let mut s = Solver::new();
        s.add_clause([1]);
        s.add_clause([2]);
        // Both vars already forced at root before solve.
        assert_eq!(s.num_level0_vars(), 2);
        let d_before = s.num_decisions();
        assert_eq!(s.solve(), Some(true));
        assert_eq!(s.num_decisions(), d_before, "no branching needed for pure unit propagation");
    }

    #[test]
    fn search_stats_assumption_propagates_at_level_1() {
        // Implication: x → y. With assumption [x], y becomes forced at level 1
        // (not level 0), so num_level0_vars stays at 0.
        let mut s = Solver::new();
        s.add_clause([-1, 2]); // ¬x ∨ y
        assert_eq!(s.num_level0_vars(), 0);
        let p_before = s.num_propagations();
        assert_eq!(s.solve_with_assumptions(&[1]), Some(true));
        // y is forced by propagation under the assumption.
        assert!(s.num_propagations() > p_before,
            "assumption [x] should force y via propagation");
        // Level-0 stays at 0 — assumptions live at level 1.
        assert_eq!(s.num_level0_vars(), 0);
    }

    #[test]
    fn search_stats_decisions_bounded() {
        // 4-var instance where every assignment is feasible (no constraints).
        // The solver branches until all vars assigned. decisions <= num_vars.
        let mut s = Solver::new();
        for v in 1..=4 { s.ensure_var(v); }
        assert_eq!(s.solve(), Some(true));
        let n = s.num_vars() as u64;
        assert!(s.num_decisions() <= n,
            "decisions={} exceeds num_vars={}", s.num_decisions(), n);
        // assignments accounted for: decisions + propagations + level-0 forced
        // should sum to at most the trail length (= num_vars when SAT).
        let total = s.num_decisions() + s.num_propagations();
        assert!(total <= n, "decisions+propagations={} exceeds num_vars={}", total, n);
    }

    #[test]
    fn search_stats_monotonic_across_solves() {
        // Counters accumulate across multiple solves on the same Solver.
        let mut s = Solver::new();
        s.add_clause([1, 2]);
        s.add_clause([-1, 2]);
        let _ = s.solve();
        let d1 = s.num_decisions();
        let p1 = s.num_propagations();
        // solve again with an extra assumption — counters should not decrease.
        let _ = s.solve_with_assumptions(&[1]);
        assert!(s.num_decisions() >= d1);
        assert!(s.num_propagations() >= p1);
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
    fn xor_reason_excludes_propagated_var() {
        // Minimal test: XOR constraint with 3 variables.
        // Fix 2 vars, XOR forces the third.
        // Then add a clause that conflicts with the forced value.
        // The conflict analysis should produce a correct learnt clause.
        let mut s = Solver::new();
        // x1 XOR x2 XOR x3 = true (odd parity)
        s.add_xor(&[1, 2, 3], true);
        // Force x1=true, x2=true → x3 must be true (T^T^x3=T → x3=T)
        s.add_clause([1]);
        s.add_clause([2]);
        // x3 should be forced true by XOR propagation
        assert_eq!(s.solve(), Some(true));
        assert_eq!(s.value(3), Some(true));
    }

    #[test]
    fn xor_with_pb_sat() {
        // XOR + PB interaction: the XOR forces a parity, PB constrains the sum.
        // This should be SAT but the XOR reason bug could cause false UNSAT.
        let mut s = Solver::new();
        // 4 variables: sum >= 2 (PB) and x1^x2^x3^x4 = false (even parity)
        s.add_pb_atleast(&[1, 2, 3, 4], &[1, 1, 1, 1], 2);
        s.add_xor(&[1, 2, 3, 4], false);
        // Solution: x1=T, x2=T, x3=F, x4=F (sum=2, XOR=T^T^F^F=false ✓)
        let result = s.solve();
        assert_eq!(result, Some(true), "XOR+PB should be SAT");
    }

    #[test]
    fn xor_with_quad_pb_sat_n26_oracle() {
        // Reduced TT(26) oracle: build the exact XY solver encoding for the
        // known TT(26) solution and verify the SAT solver finds it.
        // This is the test case that exposed the XOR soundness bug.
        use super::*;

        let mut s = Solver::new();
        s.config.xor_propagation = true;
        let n = 6; // Use small n=6 for minimal repro

        // Known TT(6): X=+++---, Y=++--+-, Z=+++-++, W=++-+-
        let x_vals: Vec<i8> = vec![1,1,1,-1,-1,-1];
        let y_vals: Vec<i8> = vec![1,1,-1,-1,1,-1];
        let z_vals: Vec<i8> = vec![1,1,1,-1,1,1];
        let w_vals: Vec<i8> = vec![1,1,-1,1,-1];

        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };

        // Symmetry breaking
        s.add_clause([x_var(0)]);
        s.add_clause([y_var(0)]);

        // Sum constraints
        let x_pos = x_vals.iter().filter(|&&v| v == 1).count();
        let y_pos = y_vals.iter().filter(|&&v| v == 1).count();
        let x_lits: Vec<i32> = (0..n).map(|i| x_var(i)).collect();
        let y_lits: Vec<i32> = (0..n).map(|i| y_var(i)).collect();
        let ones: Vec<u32> = vec![1; n];
        s.add_pb_eq(&x_lits, &ones, x_pos as u32);
        s.add_pb_eq(&y_lits, &ones, y_pos as u32);

        // Compute zw_autocorr
        let m = n - 1;
        let mut zw_ac = vec![0i32; n];
        for lag in 1..n {
            let nz: i32 = (0..n-lag).map(|i| z_vals[i] as i32 * z_vals[i+lag] as i32).sum();
            let nw: i32 = if lag < m { (0..m-lag).map(|i| w_vals[i] as i32 * w_vals[i+lag] as i32).sum() } else { 0 };
            zw_ac[lag] = 2*nz + 2*nw;
        }

        // Add quad PB agree constraints per lag
        for lag in 1..n {
            let target_raw = 2*(n-lag) as i32 - zw_ac[lag];
            if target_raw < 0 || target_raw % 2 != 0 { panic!("infeasible"); }
            let target = (target_raw / 2) as u32;

            let mut la = Vec::new();
            let mut lb = Vec::new();
            for i in 0..(n-lag) {
                la.push(x_var(i)); lb.push(x_var(i+lag));
                la.push(-x_var(i)); lb.push(-x_var(i+lag));
            }
            for i in 0..(n-lag) {
                la.push(y_var(i)); lb.push(y_var(i+lag));
                la.push(-y_var(i)); lb.push(-y_var(i+lag));
            }
            let coeffs: Vec<u32> = vec![1; la.len()];
            s.add_quad_pb_eq(&la, &lb, &coeffs, target);
        }

        // Add XOR parity constraints per lag (this is where the bug triggers)
        for lag in 1..n {
            let target_raw = 2*(n-lag) as i32 - zw_ac[lag];
            let target = (target_raw / 2) as usize;
            let k = 2*(n-lag);
            let parity = ((target + k) % 2) == 1;
            let mut in_xor = vec![false; 2*n];
            for i in 0..(n-lag) {
                in_xor[i] ^= true;
                in_xor[i+lag] ^= true;
            }
            for i in 0..(n-lag) {
                in_xor[n+i] ^= true;
                in_xor[n+i+lag] ^= true;
            }
            let vars: Vec<i32> = in_xor.iter().enumerate()
                .filter(|&(_, &v)| v)
                .map(|(i, _)| (i + 1) as i32)
                .collect();
            if !vars.is_empty() {
                s.add_xor(&vars, parity);
            }
        }

        let result = s.solve();
        assert_eq!(result, Some(true),
            "XOR+QuadPB encoding of known TT(6) should be SAT (XOR reason bug)");
    }

    #[test]
    fn xor_with_quad_pb_sat_n26_full_oracle() {
        // Full TT(26) XY encoding for the known solution's Z/W pair.
        // This MUST return SAT. With the XOR reason bug, it returns false UNSAT.
        use super::*;

        let n = 26usize;
        let m = 25usize;

        // Known TT(26) solution
        let z_str = "+++-+--++++++--++---+-+--+";
        let w_str = "++++-+---+--+++--++++-+-+";
        let z: Vec<i8> = z_str.chars().map(|c| if c=='+' { 1 } else { -1 }).collect();
        let w: Vec<i8> = w_str.chars().map(|c| if c=='+' { 1 } else { -1 }).collect();
        assert_eq!(z.len(), n);
        assert_eq!(w.len(), m);

        let mut s = Solver::new();
        s.config.xor_propagation = true;

        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };

        // Symmetry breaking: x[0]=+1, y[0]=+1
        s.add_clause([x_var(0)]);
        s.add_clause([y_var(0)]);

        // Sum constraints: x_sum=6, y_sum=6
        let x_pos = 16u32; // (6+26)/2
        let y_pos = 16u32;
        let x_lits: Vec<i32> = (0..n).map(|i| x_var(i)).collect();
        let y_lits: Vec<i32> = (0..n).map(|i| y_var(i)).collect();
        let ones: Vec<u32> = vec![1; n];
        s.add_pb_eq(&x_lits, &ones, x_pos);
        s.add_pb_eq(&y_lits, &ones, y_pos);

        // Compute zw_autocorr
        let mut zw_ac = vec![0i32; n];
        for lag in 1..n {
            let nz: i32 = (0..n-lag).map(|i| z[i] as i32 * z[i+lag] as i32).sum();
            let nw: i32 = if lag < m { (0..m-lag).map(|i| w[i] as i32 * w[i+lag] as i32).sum() } else { 0 };
            zw_ac[lag] = 2*nz + 2*nw;
        }

        // Quad PB agree constraints per lag
        for lag in 1..n {
            let target_raw = 2*(n-lag) as i32 - zw_ac[lag];
            assert!(target_raw >= 0 && target_raw % 2 == 0);
            let target = (target_raw / 2) as u32;

            let mut la = Vec::new();
            let mut lb = Vec::new();
            for i in 0..(n-lag) {
                la.push(x_var(i)); lb.push(x_var(i+lag));
                la.push(-x_var(i)); lb.push(-x_var(i+lag));
            }
            for i in 0..(n-lag) {
                la.push(y_var(i)); lb.push(y_var(i+lag));
                la.push(-y_var(i)); lb.push(-y_var(i+lag));
            }
            let coeffs: Vec<u32> = vec![1; la.len()];
            s.add_quad_pb_eq(&la, &lb, &coeffs, target);
        }

        // XOR parity constraints per lag
        for lag in 1..n {
            let target_raw = 2*(n-lag) as i32 - zw_ac[lag];
            let target = (target_raw / 2) as usize;
            let k = 2*(n-lag);
            let parity = ((target + k) % 2) == 1;
            let mut in_xor = vec![false; 2*n];
            for i in 0..(n-lag) {
                in_xor[i] ^= true;
                in_xor[i+lag] ^= true;
            }
            for i in 0..(n-lag) {
                in_xor[n+i] ^= true;
                in_xor[n+i+lag] ^= true;
            }
            let vars: Vec<i32> = in_xor.iter().enumerate()
                .filter(|&(_, &v)| v)
                .map(|(i, _)| (i + 1) as i32)
                .collect();
            if !vars.is_empty() {
                s.add_xor(&vars, parity);
            }
        }

        s.reserve_for_search(200);
        let result = s.solve();
        assert_eq!(result, Some(true),
            "XOR+QuadPB encoding of known TT(26) Z/W must be SAT");
    }

    #[test]
    fn xor_quad_pb_single_lag4() {
        // Minimal: QuadPB for all lags, but XOR ONLY for lag 4.
        use super::*;
        let n = 26usize;
        let m = 25usize;
        let z: Vec<i8> = "+++-+--++++++--++---+-+--+".chars().map(|c| if c=='+' { 1 } else { -1 }).collect();
        let w: Vec<i8> = "++++-+---+--+++--++++-+-+".chars().map(|c| if c=='+' { 1 } else { -1 }).collect();

        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };

        let mut zw_ac = vec![0i32; n];
        for lag in 1..n {
            let nz: i32 = (0..n-lag).map(|i| z[i] as i32 * z[i+lag] as i32).sum();
            let nw: i32 = if lag < m { (0..m-lag).map(|i| w[i] as i32 * w[i+lag] as i32).sum() } else { 0 };
            zw_ac[lag] = 2*nz + 2*nw;
        }

        let mut s = Solver::new();
        s.config.xor_propagation = true;
        s.add_clause([x_var(0)]);
        s.add_clause([y_var(0)]);
        let x_lits: Vec<i32> = (0..n).map(|i| x_var(i)).collect();
        let y_lits: Vec<i32> = (0..n).map(|i| y_var(i)).collect();
        let ones_n: Vec<u32> = vec![1; n];
        s.add_pb_eq(&x_lits, &ones_n, 16);
        s.add_pb_eq(&y_lits, &ones_n, 16);

        // All quad PB
        for lag in 1..n {
            let target = ((2*(n-lag) as i32 - zw_ac[lag]) / 2) as u32;
            let mut la = Vec::new();
            let mut lb = Vec::new();
            for i in 0..(n-lag) {
                la.push(x_var(i)); lb.push(x_var(i+lag));
                la.push(-x_var(i)); lb.push(-x_var(i+lag));
            }
            for i in 0..(n-lag) {
                la.push(y_var(i)); lb.push(y_var(i+lag));
                la.push(-y_var(i)); lb.push(-y_var(i+lag));
            }
            let coeffs: Vec<u32> = vec![1; la.len()];
            s.add_quad_pb_eq(&la, &lb, &coeffs, target);
        }

        // XOR ONLY for lag 4
        let lag = 4;
        let target = ((2*(n-lag) as i32 - zw_ac[lag]) / 2) as usize;
        let k = 2*(n-lag);
        let parity = ((target + k) % 2) == 1;
        let mut in_xor = vec![false; 2*n];
        for i in 0..(n-lag) { in_xor[i] ^= true; in_xor[i+lag] ^= true; }
        for i in 0..(n-lag) { in_xor[n+i] ^= true; in_xor[n+i+lag] ^= true; }
        let vars: Vec<i32> = in_xor.iter().enumerate()
            .filter(|&(_, &v)| v).map(|(i, _)| (i + 1) as i32).collect();
        s.add_xor(&vars, parity);

        s.reserve_for_search(200);
        s.set_conflict_limit(50000);
        let result = s.solve();
        assert_eq!(result, Some(true), "QuadPB + single lag-4 XOR should be SAT");
    }

    #[test]
    fn xor_quad_pb_forced_solution() {
        // Force the known TT(26) X/Y solution via assumptions.
        // If UNSAT: the constraints themselves are wrong (encoding bug).
        // If SAT: the constraints are correct and the search is wrong.
        let mut s = build_xor_quad_pb_no_gj_n26_solver(true);
        let x: Vec<i8> = "++--+--+++++++-+-++--+-++-".chars().map(|c| if c=='+' { 1 } else { -1 }).collect();
        let y: Vec<i8> = "+++-+-++++++-++-+---+-++--".chars().map(|c| if c=='+' { 1 } else { -1 }).collect();
        let n = 26;
        let mut assumptions = Vec::new();
        for i in 0..n {
            let lit = (i + 1) as i32;
            assumptions.push(if x[i] == 1 { lit } else { -lit });
        }
        for i in 0..n {
            let lit = (n + i + 1) as i32;
            assumptions.push(if y[i] == 1 { lit } else { -lit });
        }
        let result = s.solve_with_assumptions(&assumptions);
        assert_eq!(result, Some(true),
            "Forcing the known TT(26) solution should be SAT even with XOR+QuadPB");
    }

    #[test]
    fn xor_quad_pb_bisect_lag() {
        // Binary search: add XOR constraints one lag at a time to find which breaks.
        use super::*;
        let n = 26usize;
        let m = 25usize;
        let z: Vec<i8> = "+++-+--++++++--++---+-+--+".chars().map(|c| if c=='+' { 1 } else { -1 }).collect();
        let w: Vec<i8> = "++++-+---+--+++--++++-+-+".chars().map(|c| if c=='+' { 1 } else { -1 }).collect();

        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };

        let mut zw_ac = vec![0i32; n];
        for lag in 1..n {
            let nz: i32 = (0..n-lag).map(|i| z[i] as i32 * z[i+lag] as i32).sum();
            let nw: i32 = if lag < m { (0..m-lag).map(|i| w[i] as i32 * w[i+lag] as i32).sum() } else { 0 };
            zw_ac[lag] = 2*nz + 2*nw;
        }

        for max_lag in 1..n {
            let mut s = Solver::new();
            s.config.xor_propagation = true;
            s.add_clause([x_var(0)]);
            s.add_clause([y_var(0)]);
            let x_lits: Vec<i32> = (0..n).map(|i| x_var(i)).collect();
            let y_lits: Vec<i32> = (0..n).map(|i| y_var(i)).collect();
            let ones_n: Vec<u32> = vec![1; n];
            s.add_pb_eq(&x_lits, &ones_n, 16);
            s.add_pb_eq(&y_lits, &ones_n, 16);

            for lag in 1..n {
                let target = ((2*(n-lag) as i32 - zw_ac[lag]) / 2) as u32;
                let mut la = Vec::new();
                let mut lb = Vec::new();
                for i in 0..(n-lag) {
                    la.push(x_var(i)); lb.push(x_var(i+lag));
                    la.push(-x_var(i)); lb.push(-x_var(i+lag));
                }
                for i in 0..(n-lag) {
                    la.push(y_var(i)); lb.push(y_var(i+lag));
                    la.push(-y_var(i)); lb.push(-y_var(i+lag));
                }
                let coeffs: Vec<u32> = vec![1; la.len()];
                s.add_quad_pb_eq(&la, &lb, &coeffs, target);
            }

            for lag in 1..=max_lag {
                let target = ((2*(n-lag) as i32 - zw_ac[lag]) / 2) as usize;
                let k = 2*(n-lag);
                let parity = ((target + k) % 2) == 1;
                let mut in_xor = vec![false; 2*n];
                for i in 0..(n-lag) { in_xor[i] ^= true; in_xor[i+lag] ^= true; }
                for i in 0..(n-lag) { in_xor[n+i] ^= true; in_xor[n+i+lag] ^= true; }
                let vars: Vec<i32> = in_xor.iter().enumerate()
                    .filter(|&(_, &v)| v).map(|(i, _)| (i + 1) as i32).collect();
                if !vars.is_empty() { s.add_xor(&vars, parity); }
            }

            s.reserve_for_search(200);
            s.set_conflict_limit(50000);
            let result = s.solve();
            if result != Some(true) {
                panic!("FAILS at max_lag={}: result={:?}", max_lag, result);
            }
        }
    }

    #[test]

    fn xor_quad_pb_no_gj_n26_oracle() {
        let mut s = build_xor_quad_pb_no_gj_n26_solver(true);
        let result = s.solve();
        assert_eq!(result, Some(true), "XOR+QuadPB (no GJ) TT(26) should be SAT");
    }

    #[test]

    fn xor_quad_pb_no_gj_n26_reference_branch_oracle() {
        let mut reference = build_xor_quad_pb_no_gj_n26_solver(false);
        assert_eq!(reference.solve(), Some(true), "reference X/Y model should exist without XOR");

        // Variable 51 is the first explicit branch in the failing run; use the
        // polarity from a real X/Y witness so this assumption stays SAT-consistent.
        let branch_lit = model_lit(&reference, 51);

        let mut s = build_xor_quad_pb_no_gj_n26_solver(true);
        let result = s.solve_with_assumptions(&[branch_lit]);
        assert_eq!(result, Some(true),
            "XOR+QuadPB should stay SAT under a branch literal taken from a reference X/Y model");
    }

    #[test]
    fn xor_only_n26_oracle() {
        // Same as n26_full but WITHOUT quad PB — just PB + XOR.
        // If this passes, the bug is in XOR+QuadPB interaction.
        use super::*;
        let n = 26usize;
        let m = 25usize;
        let z: Vec<i8> = "+++-+--++++++--++---+-+--+".chars().map(|c| if c=='+' { 1 } else { -1 }).collect();
        let w: Vec<i8> = "++++-+---+--+++--++++-+-+".chars().map(|c| if c=='+' { 1 } else { -1 }).collect();

        let mut s = Solver::new();
        s.config.xor_propagation = true;
        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };
        s.add_clause([x_var(0)]);
        s.add_clause([y_var(0)]);
        let x_lits: Vec<i32> = (0..n).map(|i| x_var(i)).collect();
        let y_lits: Vec<i32> = (0..n).map(|i| y_var(i)).collect();
        let ones: Vec<u32> = vec![1; n];
        s.add_pb_eq(&x_lits, &ones, 16);
        s.add_pb_eq(&y_lits, &ones, 16);

        let mut zw_ac = vec![0i32; n];
        for lag in 1..n {
            let nz: i32 = (0..n-lag).map(|i| z[i] as i32 * z[i+lag] as i32).sum();
            let nw: i32 = if lag < m { (0..m-lag).map(|i| w[i] as i32 * w[i+lag] as i32).sum() } else { 0 };
            zw_ac[lag] = 2*nz + 2*nw;
        }

        // XOR parity constraints ONLY (no quad PB)
        for lag in 1..n {
            let target = ((2*(n-lag) as i32 - zw_ac[lag]) / 2) as usize;
            let k = 2*(n-lag);
            let parity = ((target + k) % 2) == 1;
            let mut in_xor = vec![false; 2*n];
            for i in 0..(n-lag) {
                in_xor[i] ^= true; in_xor[i+lag] ^= true;
            }
            for i in 0..(n-lag) {
                in_xor[n+i] ^= true; in_xor[n+i+lag] ^= true;
            }
            let vars: Vec<i32> = in_xor.iter().enumerate()
                .filter(|&(_, &v)| v).map(|(i, _)| (i + 1) as i32).collect();
            if !vars.is_empty() { s.add_xor(&vars, parity); }
        }

        s.reserve_for_search(200);
        let result = s.solve();
        assert_eq!(result, Some(true), "XOR-only TT(26) should be SAT");
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

    // ---- PbSetEq tests --------------------------------------------------

    #[test]
    fn pb_set_eq_singleton_works_like_pb_eq() {
        let mut s = Solver::new();
        s.add_pb_set_eq(&[1, 2, 3, 4], &[2]);
        assert_eq!(s.solve(), Some(true));
        let trues = (1..=4).filter(|&v| s.value(v) == Some(true)).count();
        assert_eq!(trues, 2);
    }

    #[test]
    fn pb_set_eq_multi_admits_each_value() {
        let mut s = Solver::new();
        s.add_pb_set_eq(&[1, 2, 3, 4], &[1, 3]);
        assert_eq!(s.solve(), Some(true));
        let trues = (1..=4).filter(|&v| s.value(v) == Some(true)).count();
        assert!(trues == 1 || trues == 3, "got {trues}");
    }

    #[test]
    fn pb_set_eq_propagates_when_set_collapses() {
        // V = {1,3} over 4 lits: forcing 2 true leaves only target=3 valid,
        // so the remaining unassigned lit must be true.
        let mut s = Solver::new();
        s.add_pb_set_eq(&[1, 2, 3, 4], &[1, 3]);
        s.add_clause([1]);
        s.add_clause([2]);
        assert_eq!(s.solve(), Some(true));
        assert_eq!(s.value(4), Some(true));
    }

    #[test]
    fn pb_set_eq_unsat_when_set_empty_after_assignment() {
        // V = {1,3} over 4 lits: force 2 true, others false → #true = 2 ∉ V.
        let mut s = Solver::new();
        s.add_pb_set_eq(&[1, 2, 3, 4], &[1, 3]);
        s.add_clause([1]);
        s.add_clause([2]);
        s.add_clause([-3]);
        s.add_clause([-4]);
        assert_eq!(s.solve(), Some(false));
    }

    #[test]
    fn pb_set_eq_empty_v_is_unsat() {
        let mut s = Solver::new();
        s.add_pb_set_eq(&[1, 2], &[]);
        assert_eq!(s.solve(), Some(false));
    }

    #[test]
    fn pb_set_eq_force_all_false_when_at_max() {
        // V = {2, 5} over 5 lits: if 2 are true already, cnt_lo = 2 = max(V_alive
        // since 5 would need all remaining true). Force one set to false →
        // remaining undef must be false too.
        let mut s = Solver::new();
        s.add_pb_set_eq(&[1, 2, 3, 4, 5], &[2, 5]);
        s.add_clause([1]);
        s.add_clause([2]);
        s.add_clause([-3]);
        s.add_clause([-4]);
        // V_alive collapses to {2}, cnt_lo = 2 ⇒ x5 must be false.
        assert_eq!(s.solve(), Some(true));
        assert_eq!(s.value(5), Some(false));
    }

    #[test]
    fn pb_set_eq_force_all_true_when_at_min() {
        // V = {3, 5} over 5 lits: if 3 are true already, V_alive = {3, 5}
        // but cnt_hi = 3 when only the 3 lits with forced-trues are set and
        // the rest are forced to undef → force true.  We instead test: force
        // 2 lits false and let 3 others be decided; V_alive = {3} because
        // cnt_hi = 3.  Then all remaining undef must be true.
        let mut s = Solver::new();
        s.add_pb_set_eq(&[1, 2, 3, 4, 5], &[3, 5]);
        s.add_clause([-4]);
        s.add_clause([-5]);
        assert_eq!(s.solve(), Some(true));
        assert_eq!(s.value(1), Some(true));
        assert_eq!(s.value(2), Some(true));
        assert_eq!(s.value(3), Some(true));
    }

    #[test]
    fn pb_set_eq_checkpoint_restore() {
        let mut s = Solver::new();
        s.add_clause([1]);
        let cp = s.save_checkpoint();
        s.add_pb_set_eq(&[1, 2, 3], &[2]);
        assert_eq!(s.solve(), Some(true));
        // After restore the PbSetEq is gone; only x1=+1 remains.
        s.restore_checkpoint(cp);
        assert_eq!(s.solve(), Some(true));
        assert_eq!(s.value(1), Some(true));
    }

    /// Regression test (currently failing) for the n=18 turyn XY regression.
    /// Hardcoded data reproducing the smallest known instance where
    /// `add_pb_set_eq` + `add_quad_pb_eq` jointly return UNSAT while each
    /// subset is SAT and an explicit satisfying assignment exists.
    ///
    /// Construction:
    /// - 36 variables: X = vars 1..=18, Y = vars 19..=36 (1-based).
    /// - PbSetEq over X with V_x = {14}: exactly 14 of the X vars are true.
    /// - PbSetEq over Y with V_y = {8}:  exactly 8  of the Y vars are true.
    /// - For each lag s in 1..=17, a `add_quad_pb_eq` over
    ///   `{(x_i, x_{i+s}), (¬x_i, ¬x_{i+s}), (y_i, y_{i+s}), (¬y_i, ¬y_{i+s})}`
    ///   for i in 0..(18-s), with target chosen to match the canonical Turyn
    ///   (X, Y, Z, W) at n=18.
    /// - Boundary unit clauses: X and Y positions 0..=4 and 13..=17 pinned
    ///   to the canonical values.
    /// - Middle positions 5..=12 left free for the SAT.
    ///
    /// Expected: SAT (the canonical middle is a valid completion).
    /// Actual:   UNSAT (soundness bug in PbSetEq + QuadPb interaction).
    ///
    /// Diagnostic data points (from the turyn test suite):
    /// - Replace `add_pb_set_eq([14])` with `add_pb_eq` target 14 → SAT.
    /// - Remove PbSetEq entirely → SAT.
    /// - Keep PbSetEq, use only lags [1..=11] of quad_pb → SAT.
    /// - Keep PbSetEq, use only lags [1..=12] of quad_pb → UNSAT.
    ///
    /// So the bug triggers when PbSetEq is combined with ≥12 quad_pb
    /// constraints.  Individual lags in isolation are SAT.
    ///
    /// Root cause (fixed 2026-04-15): `propagate_pb_set_eq` trusted the
    /// incremental `(num_true, num_undef)` counters, but those only
    /// reflect the single lit currently being processed by the main
    /// propagate loop.  When prior propagators in the same iteration
    /// (QuadPb, or this PbSetEq's own `force_pb_set_eq_dir`) had already
    /// enqueued additional lits, their effect was not yet in the
    /// counters — the propagator saw a stale `(num_true, num_undef)` and
    /// concluded V_alive = ∅ even though the real assignment had plenty
    /// of valid counts.  Fix: always recompute from the trail.  Same
    /// workaround the XOR propagator already used.
    #[test]
    fn pb_set_eq_plus_quad_pb_tt18_regression() {
        let n = 18usize;
        // Canonical TT(18).  X[i] = +1 if bit i is 1.
        let x_vals: [i8; 18] = [ 1,  1, -1,  1,  1,  1,  1,  1,  1,  1,  1,  1, -1,  1, -1, -1,  1,  1];
        let y_vals: [i8; 18] = [ 1,  1, -1, -1, -1, -1,  1,  1, -1,  1, -1, -1, -1,  1, -1,  1, -1,  1];
        let z_vals: [i8; 18] = [ 1,  1, -1,  1,  1,  1, -1, -1, -1, -1,  1, -1,  1, -1,  1,  1, -1, -1];
        let w_vals: [i8; 17] = [ 1,  1, -1, -1, -1, -1,  1, -1, -1,  1, -1, -1,  1,  1,  1, -1,  1];

        // zw_autocorr[s] = 2 * N_Z(s) + 2 * N_W(s), where N_A(s) = Σ A[i]*A[i+s]
        let mut zw_autocorr = vec![0i32; n];
        for s in 1..n {
            let mut nz = 0i32;
            for i in 0..(n - s) { nz += (z_vals[i] as i32) * (z_vals[i + s] as i32); }
            let mut nw = 0i32;
            if s < 17 {
                for i in 0..(17 - s) { nw += (w_vals[i] as i32) * (w_vals[i + s] as i32); }
            }
            zw_autocorr[s] = 2 * nz + 2 * nw;
        }
        // Verify Turyn identity for X, Y: N_X + N_Y + zw = 0 for s >= 1.
        for s in 1..n {
            let mut nx = 0i32;
            for i in 0..(n - s) { nx += (x_vals[i] as i32) * (x_vals[i + s] as i32); }
            let mut ny = 0i32;
            for i in 0..(n - s) { ny += (y_vals[i] as i32) * (y_vals[i + s] as i32); }
            assert_eq!(nx + ny + zw_autocorr[s], 0,
                "Turyn identity fails at s={s}: N_X={nx}, N_Y={ny}, zw_autocorr={}",
                zw_autocorr[s]);
        }

        let x_var = |i: usize| -> i32 { (i + 1) as i32 };          // 1..=18
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };       // 19..=36

        let mut s = Solver::new();
        // Ensure all 36 vars exist.
        for v in 1..=(2 * n) as i32 { s.add_clause([v, -v]); }

        // PbSetEq on X: exactly 14 true.  Canonical σ_X = +10, so count = 14.
        let x_lits: Vec<i32> = (0..n).map(|i| x_var(i)).collect();
        s.add_pb_set_eq(&x_lits, &[14]);
        // PbSetEq on Y: exactly 8 true.  Canonical σ_Y = -2, so count = 8.
        let y_lits: Vec<i32> = (0..n).map(|i| y_var(i)).collect();
        s.add_pb_set_eq(&y_lits, &[8]);

        // quad_pb for each lag s in 1..n.  target = (2(n-s) - zw[s]) / 2.
        for lag in 1..n {
            let target_raw = 2 * (n - lag) as i32 - zw_autocorr[lag];
            assert!(target_raw >= 0 && target_raw % 2 == 0);
            let target = (target_raw / 2) as u32;
            let mut lits_a: Vec<i32> = Vec::with_capacity(4 * (n - lag));
            let mut lits_b: Vec<i32> = Vec::with_capacity(4 * (n - lag));
            for i in 0..(n - lag) {
                lits_a.push(x_var(i)); lits_b.push(x_var(i + lag));
                lits_a.push(-x_var(i)); lits_b.push(-x_var(i + lag));
            }
            for i in 0..(n - lag) {
                lits_a.push(y_var(i)); lits_b.push(y_var(i + lag));
                lits_a.push(-y_var(i)); lits_b.push(-y_var(i + lag));
            }
            let ones: Vec<u32> = vec![1; lits_a.len()];
            s.add_quad_pb_eq(&lits_a, &lits_b, &ones, target);
        }

        // Boundary unit clauses: pin first 5 and last 5 of both X and Y.
        let k = 5usize;
        for i in 0..k {
            s.add_clause([if x_vals[i] == 1 { x_var(i) } else { -x_var(i) }]);
            s.add_clause([if x_vals[n - k + i] == 1 { x_var(n - k + i) } else { -x_var(n - k + i) }]);
            s.add_clause([if y_vals[i] == 1 { y_var(i) } else { -y_var(i) }]);
            s.add_clause([if y_vals[n - k + i] == 1 { y_var(n - k + i) } else { -y_var(n - k + i) }]);
        }

        let result = s.solve();
        assert_eq!(result, Some(true),
            "PbSetEq + quad_pb + canonical boundary should be SAT — the canonical middle X, Y is a valid completion.  \
             This is the n=18 turyn open-search regression manifesting as a pure radical-level test.");
    }
}
