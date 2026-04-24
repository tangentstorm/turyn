/// SAT encoding for Z middle given fixed Z boundary and known W.
///
/// Variables: z_mid[0..middle_n-1] (true = +1, false = -1)
/// Constraints:
///   - Sum: exactly z_mid_ones of middle_n vars are +1
///   - For each lag s: N_Z(s) in [lo, hi] where bounds come from N_W(s) and XY feasibility
///
/// N_Z(s) = Σ z[i]*z[i+s] decomposes into:
///   - const: boundary×boundary pairs (known)
///   - linear: boundary×middle pairs (±mid_var)
///   - quad: middle×middle pairs (mid_var_a * mid_var_b)

/// Precomputed lag decomposition for a given (n, k).
/// The position classification is purely geometric — independent of boundary values.
pub struct LagTemplate {
    pub lags: Vec<LagInfo>,
}

pub struct LagInfo {
    /// (i, j) pairs where both are boundary positions
    pub bnd_bnd: Vec<(usize, usize)>,
    /// (bnd_pos, mid_idx) pairs — bnd_pos is the boundary position whose value
    /// determines the literal polarity; mid_idx is the middle variable index
    pub bnd_mid: Vec<(usize, usize)>,
    /// (mid_a, mid_b) pairs — both middle, encoded as XNOR aux vars
    pub mid_mid: Vec<(usize, usize)>,
    /// Aux var base for this lag's XNOR encoding
    pub aux_base: i32,
    /// Total number of pairs at this lag
    pub num_pairs: usize,
}

impl LagTemplate {
    /// Build template for a sequence of given length and boundary width k.
    /// Works for both Z (length n) and W (length m).
    pub fn new(seq_len: usize, k: usize) -> Self {
        let middle_len = seq_len - 2 * k;
        let is_mid = |pos: usize| -> bool { pos >= k && pos < seq_len - k };

        let mut lags = Vec::with_capacity(seq_len - 1);
        for s in 1..seq_len {
            let num_pairs = seq_len - s;
            let mut bnd_bnd = Vec::new();
            let mut bnd_mid = Vec::new();
            let mut mid_mid = Vec::new();

            for i in 0..num_pairs {
                let j = i + s;
                let i_mid = is_mid(i);
                let j_mid = is_mid(j);

                if !i_mid && !j_mid {
                    bnd_bnd.push((i, j));
                } else if i_mid && !j_mid {
                    bnd_mid.push((j, i - k));
                } else if !i_mid && j_mid {
                    bnd_mid.push((i, j - k));
                } else {
                    mid_mid.push((i - k, j - k));
                }
            }

            let aux_base = (middle_len + 1 + s * seq_len) as i32;
            lags.push(LagInfo {
                bnd_bnd,
                bnd_mid,
                mid_mid,
                aux_base,
                num_pairs,
            });
        }

        LagTemplate { lags }
    }

    /// Build a base solver with sum constraint (boundary-independent).
    /// If `use_quad_pb` is true, skip XNOR aux clauses — the fill functions
    /// will use native quad PB range constraints instead.
    pub fn build_base_solver(&self, middle_len: usize, mid_sum: i32) -> radical::Solver {
        self.build_base_solver_inner(middle_len, mid_sum, false)
    }

    /// Quad PB mode: no XNOR aux vars, adds a "true" helper variable for linear terms.
    pub fn build_base_solver_quad_pb(&self, middle_len: usize, mid_sum: i32) -> radical::Solver {
        self.build_base_solver_inner(middle_len, mid_sum, true)
    }

    fn build_base_solver_inner(
        &self,
        middle_len: usize,
        mid_sum: i32,
        use_quad_pb: bool,
    ) -> radical::Solver {
        let mut solver = radical::Solver::new();
        let mid_var = |i: usize| -> i32 { (i + 1) as i32 };

        // Sum constraint
        let mid_ones = ((mid_sum + middle_len as i32) / 2) as usize;
        let lits: Vec<i32> = (0..middle_len).map(|i| mid_var(i)).collect();
        let ones: Vec<u32> = vec![1; middle_len];
        solver.add_pb_eq(&lits, &ones, mid_ones as u32);

        if use_quad_pb {
            // Add a "true" helper variable for encoding linear terms as products.
            // var (middle_len+1) is forced to true.
            let true_var = (middle_len + 1) as i32;
            solver.add_clause([true_var]);
        } else {
            // Legacy: XNOR aux clauses for all mid×mid pairs
            for lag in &self.lags {
                for (qi, &(mid_a, mid_b)) in lag.mid_mid.iter().enumerate() {
                    let a = mid_var(mid_a);
                    let b = mid_var(mid_b);
                    let aux = lag.aux_base + qi as i32;
                    solver.add_clause([-aux, -a, b]);
                    solver.add_clause([-aux, a, -b]);
                    solver.add_clause([a, b, aux]);
                    solver.add_clause([-a, -b, aux]);
                }
            }
        }

        solver
    }

    /// Variable ID for the "true" helper variable (only valid in quad_pb mode).
    pub fn true_var(&self, middle_len: usize) -> i32 {
        (middle_len + 1) as i32
    }

    /// Like `build_base_solver` but replaces the single-target sum PB with a
    /// `PbSetEq` over multiple valid counts.  Used by the multi-σ W middle
    /// SAT — the SAT may then pick either sign of σ_W (or any σ_W compatible
    /// with the `valid_counts` set).
    pub fn build_base_solver_pb_set(
        &self,
        middle_len: usize,
        valid_counts: &[u32],
    ) -> radical::Solver {
        let mut solver = radical::Solver::new();
        let mid_var = |i: usize| -> i32 { (i + 1) as i32 };
        let lits: Vec<i32> = (0..middle_len).map(mid_var).collect();
        solver.add_pb_set_eq(&lits, valid_counts);
        // Legacy XNOR aux clauses for all mid×mid pairs — matches the
        // non-quad-pb path in `build_base_solver_inner`.
        for lag in &self.lags {
            for (qi, &(mid_a, mid_b)) in lag.mid_mid.iter().enumerate() {
                let a = mid_var(mid_a);
                let b = mid_var(mid_b);
                let aux = lag.aux_base + qi as i32;
                solver.add_clause([-aux, -a, b]);
                solver.add_clause([-aux, a, -b]);
                solver.add_clause([a, b, aux]);
                solver.add_clause([-a, -b, aux]);
            }
        }
        solver
    }

    /// Like `build_base_solver_quad_pb` but with a `PbSetEq` middle-sum
    /// constraint.  Used by the multi-σ Z middle SAT.
    pub fn build_base_solver_quad_pb_pb_set(
        &self,
        middle_len: usize,
        valid_counts: &[u32],
    ) -> radical::Solver {
        let mut solver = radical::Solver::new();
        let mid_var = |i: usize| -> i32 { (i + 1) as i32 };
        let lits: Vec<i32> = (0..middle_len).map(mid_var).collect();
        solver.add_pb_set_eq(&lits, valid_counts);
        // Quad PB mode: "true" helper var.
        let true_var = (middle_len + 1) as i32;
        solver.add_clause([true_var]);
        solver
    }
}

/// Fill a cloned base solver with boundary-specific constraints.
/// For Z middle: bounds come from known W via N_W(s).
pub fn fill_z_solver(
    solver: &mut radical::Solver,
    tmpl: &LagTemplate,
    n: usize,
    m: usize,
    z_boundary: &[i8],
    w_vals: &[i8],
) {
    let mid_var = |i: usize| -> i32 { (i + 1) as i32 };

    for (s, lag) in tmpl.lags.iter().enumerate() {
        let s = s + 1; // lags[0] corresponds to s=1

        // Compute N_W(s)
        let nw_s: i32 = if s < m {
            (0..m - s)
                .map(|i| w_vals[i] as i32 * w_vals[i + s] as i32)
                .sum()
        } else {
            0
        };

        let max_nz = (n - s) as i32;
        let lo = (-max_nz).max(-max_nz - nw_s);
        let hi = max_nz.min(max_nz - nw_s);

        if lo > hi {
            solver.add_clause(std::iter::empty::<i32>());
            return;
        }

        let agree_lo = ((lo + max_nz) / 2) as u32;
        let agree_hi = ((hi + max_nz) / 2) as u32;

        // Compute agree_const from bnd×bnd pairs
        let mut agree_const: u32 = 0;
        for &(i, j) in &lag.bnd_bnd {
            if z_boundary[i] == z_boundary[j] {
                agree_const += 1;
            }
        }

        // Build linear literals from bnd×mid pairs
        let mut agree_lits: Vec<i32> = Vec::with_capacity(lag.bnd_mid.len());
        for &(bnd_pos, mid_idx) in &lag.bnd_mid {
            if z_boundary[bnd_pos] == 1 {
                agree_lits.push(mid_var(mid_idx));
            } else {
                agree_lits.push(-mid_var(mid_idx));
            }
        }

        let max_variable = agree_lits.len() as u32 + lag.mid_mid.len() as u32;

        if agree_lo > agree_const + max_variable {
            solver.add_clause(std::iter::empty::<i32>());
            return;
        }

        let adj_lo = agree_lo.saturating_sub(agree_const);
        let adj_hi = agree_hi - agree_const;

        if agree_lits.is_empty() && lag.mid_mid.is_empty() {
            if agree_const < agree_lo || agree_const > agree_hi {
                solver.add_clause(std::iter::empty::<i32>());
                return;
            }
            continue;
        }

        // Skip trivially satisfied constraints
        if adj_lo == 0 && adj_hi >= max_variable {
            continue;
        }

        if lag.mid_mid.is_empty() {
            // Linear only
            let ones: Vec<u32> = vec![1; agree_lits.len()];
            if adj_lo > 0 {
                solver.add_pb_atleast(&agree_lits, &ones, adj_lo);
            }
            if adj_hi < agree_lits.len() as u32 {
                let neg_lits: Vec<i32> = agree_lits.iter().map(|&l| -l).collect();
                solver.add_pb_atleast(&neg_lits, &ones, agree_lits.len() as u32 - adj_hi);
            }
        } else {
            // Linear + quad (XNOR aux vars already in base solver)
            let mut all_lits = agree_lits;
            for (qi, _) in lag.mid_mid.iter().enumerate() {
                all_lits.push(lag.aux_base + qi as i32);
            }
            let ones: Vec<u32> = vec![1; all_lits.len()];
            if adj_lo > 0 {
                solver.add_pb_atleast(&all_lits, &ones, adj_lo);
            }
            if adj_hi < all_lits.len() as u32 {
                let neg_all: Vec<i32> = all_lits.iter().map(|&l| -l).collect();
                solver.add_pb_atleast(&neg_all, &ones, all_lits.len() as u32 - adj_hi);
            }
        }
    }
}

/// Fill a base solver with boundary-specific quad PB range constraints for Z middle.
/// Uses native quad PB instead of XNOR aux vars — fewer variables, native propagation.
/// Precomputed z_boundary-dependent constraint data for each lag.
///
/// Built once per (z_bits, middle_len) pair in the SolveW stage and reused
/// across every SolveZ item that shares the same z_boundary. The expensive
/// parts — computing `agree_const` (a bnd×bnd scan per lag) and building
/// the per-lag literal lists (bnd_mid sign flips + mid_mid pairs) — are
/// hoisted out of the per-item hot path.
///
/// Only the per-W bounds (`nw_s`, `adj_lo`, `adj_hi`) still need to be
/// computed per-SolveZ-item.
pub struct ZBoundaryPrep {
    /// Per-lag bnd×bnd constant (count of boundary pairs that already match).
    pub agree_const: Vec<u32>,
    /// Per-lag lits_a list (for quad PB terms). Static across W.
    pub lits_a: Vec<Vec<i32>>,
    /// Per-lag lits_b list (for quad PB terms). Static across W.
    pub lits_b: Vec<Vec<i32>>,
    /// Per-lag coefficient list (always all 1s, reused).
    pub coeffs: Vec<Vec<u32>>,
}

impl ZBoundaryPrep {
    /// Allocate empty buffers sized to hold the per-lag data for the given
    /// template. Call `rebuild` to populate.
    pub fn with_template(tmpl: &LagTemplate) -> Self {
        let num_lags = tmpl.lags.len();
        ZBoundaryPrep {
            agree_const: vec![0; num_lags],
            lits_a: (0..num_lags).map(|_| Vec::new()).collect(),
            lits_b: (0..num_lags).map(|_| Vec::new()).collect(),
            coeffs: (0..num_lags).map(|_| Vec::new()).collect(),
        }
    }

    pub fn new(tmpl: &LagTemplate, middle_len: usize, z_boundary: &[i8]) -> Self {
        let mut prep = Self::with_template(tmpl);
        prep.rebuild(tmpl, middle_len, z_boundary);
        prep
    }

    /// Re-populate the per-lag data for a new z_boundary, reusing the
    /// existing Vec allocations. No heap traffic on the common path.
    pub fn rebuild(&mut self, tmpl: &LagTemplate, middle_len: usize, z_boundary: &[i8]) {
        let mid_var = |i: usize| -> i32 { (i + 1) as i32 };
        let true_var = tmpl.true_var(middle_len);

        for (s_idx, lag) in tmpl.lags.iter().enumerate() {
            let mut agc: u32 = 0;
            for &(i, j) in &lag.bnd_bnd {
                if z_boundary[i] == z_boundary[j] {
                    agc += 1;
                }
            }
            self.agree_const[s_idx] = agc;

            let la = &mut self.lits_a[s_idx];
            let lb = &mut self.lits_b[s_idx];
            let c = &mut self.coeffs[s_idx];
            la.clear();
            lb.clear();
            c.clear();

            for &(bnd_pos, mid_idx) in &lag.bnd_mid {
                let lit = if z_boundary[bnd_pos] == 1 {
                    mid_var(mid_idx)
                } else {
                    -mid_var(mid_idx)
                };
                la.push(lit);
                lb.push(true_var);
            }
            for &(mid_a, mid_b) in &lag.mid_mid {
                la.push(mid_var(mid_a));
                lb.push(mid_var(mid_b));
                la.push(-mid_var(mid_a));
                lb.push(-mid_var(mid_b));
            }

            c.resize(la.len(), 1);
        }
    }
}

/// Convenience wrapper: build `ZBoundaryPrep` from `z_boundary` and call
/// the prep-taking variant. Used by tests and one-off paths where caching
/// the prep isn't worthwhile.
pub fn fill_z_solver_quad_pb_with_boundary(
    solver: &mut radical::Solver,
    tmpl: &LagTemplate,
    n: usize,
    m: usize,
    middle_len: usize,
    z_boundary: &[i8],
    w_vals: &[i8],
) {
    let prep = ZBoundaryPrep::new(tmpl, middle_len, z_boundary);
    fill_z_solver_quad_pb(solver, tmpl, n, m, middle_len, &prep, w_vals);
}

pub fn fill_z_solver_quad_pb(
    solver: &mut radical::Solver,
    tmpl: &LagTemplate,
    n: usize,
    m: usize,
    _middle_len: usize,
    prep: &ZBoundaryPrep,
    w_vals: &[i8],
) {
    for (s_idx, lag) in tmpl.lags.iter().enumerate() {
        let s = s_idx + 1;

        let nw_s: i32 = if s < m {
            (0..m - s)
                .map(|i| w_vals[i] as i32 * w_vals[i + s] as i32)
                .sum()
        } else {
            0
        };

        let max_nz = (n - s) as i32;
        let lo = (-max_nz).max(-max_nz - nw_s);
        let hi = max_nz.min(max_nz - nw_s);

        if lo > hi {
            solver.add_clause(std::iter::empty::<i32>());
            return;
        }

        let agree_lo = ((lo + max_nz) / 2) as u32;
        let agree_hi = ((hi + max_nz) / 2) as u32;

        let agree_const = prep.agree_const[s_idx];
        let max_variable = lag.bnd_mid.len() as u32 + lag.mid_mid.len() as u32;

        if agree_lo > agree_const + max_variable {
            solver.add_clause(std::iter::empty::<i32>());
            return;
        }

        let adj_lo = agree_lo.saturating_sub(agree_const);
        let adj_hi = agree_hi - agree_const;

        if lag.bnd_mid.is_empty() && lag.mid_mid.is_empty() {
            if agree_const < agree_lo || agree_const > agree_hi {
                solver.add_clause(std::iter::empty::<i32>());
                return;
            }
            continue;
        }

        if adj_lo == 0 && adj_hi >= max_variable {
            continue;
        }

        solver.add_quad_pb_range(
            &prep.lits_a[s_idx],
            &prep.lits_b[s_idx],
            &prep.coeffs[s_idx],
            adj_lo,
            adj_hi,
        );
    }
}

/// Fill a cloned base solver with W-specific constraints (trivial bounds).
pub fn fill_w_solver(
    solver: &mut radical::Solver,
    tmpl: &LagTemplate,
    _seq_len: usize,
    boundary: &[i8],
) {
    let mid_var = |i: usize| -> i32 { (i + 1) as i32 };

    for (_s, lag) in tmpl.lags.iter().enumerate() {
        let agree_lo = 0u32;
        let agree_hi = lag.num_pairs as u32;

        let mut agree_const: u32 = 0;
        for &(i, j) in &lag.bnd_bnd {
            if boundary[i] == boundary[j] {
                agree_const += 1;
            }
        }

        let mut agree_lits: Vec<i32> = Vec::with_capacity(lag.bnd_mid.len());
        for &(bnd_pos, mid_idx) in &lag.bnd_mid {
            if boundary[bnd_pos] == 1 {
                agree_lits.push(mid_var(mid_idx));
            } else {
                agree_lits.push(-mid_var(mid_idx));
            }
        }

        let max_variable = agree_lits.len() as u32 + lag.mid_mid.len() as u32;
        let adj_lo = agree_lo.saturating_sub(agree_const);
        let adj_hi = agree_hi - agree_const;

        if adj_lo == 0 && adj_hi >= max_variable {
            continue;
        }

        if agree_lits.is_empty() && lag.mid_mid.is_empty() {
            if agree_const < agree_lo || agree_const > agree_hi {
                solver.add_clause(std::iter::empty::<i32>());
                return;
            }
            continue;
        }

        if adj_lo > max_variable {
            solver.add_clause(std::iter::empty::<i32>());
            return;
        }

        if lag.mid_mid.is_empty() {
            let ones: Vec<u32> = vec![1; agree_lits.len()];
            if adj_lo > 0 {
                solver.add_pb_atleast(&agree_lits, &ones, adj_lo);
            }
            if adj_hi < agree_lits.len() as u32 {
                let neg_lits: Vec<i32> = agree_lits.iter().map(|&l| -l).collect();
                solver.add_pb_atleast(&neg_lits, &ones, agree_lits.len() as u32 - adj_hi);
            }
        } else {
            let mut all_lits = agree_lits;
            for (qi, _) in lag.mid_mid.iter().enumerate() {
                all_lits.push(lag.aux_base + qi as i32);
            }
            let ones: Vec<u32> = vec![1; all_lits.len()];
            if adj_lo > 0 {
                solver.add_pb_atleast(&all_lits, &ones, adj_lo);
            }
            if adj_hi < all_lits.len() as u32 {
                let neg_all: Vec<i32> = all_lits.iter().map(|&l| -l).collect();
                solver.add_pb_atleast(&neg_all, &ones, all_lits.len() as u32 - adj_hi);
            }
        }
    }
}

/// Add spectral frequency constraints to the W solver.
/// For each sampled frequency ω, encodes:
///   P(ω) = m + 2*Σ_s N_W(s)*cos(2πsω/m) ≤ spectral_bound
/// as a weighted PB constraint on the agree literals.
///
/// Each agree literal (linear from bnd×mid, aux from mid×mid) contributes
/// a weight of 2*cos(2πsω/m) at frequency ω for its lag s. The constant
/// part from bnd×bnd pairs is folded into the threshold.
///
/// Integer scaling (SCALE=1000) converts float cosine weights to u32 coeffs.
pub fn fill_w_spectral(
    solver: &mut radical::Solver,
    tmpl: &LagTemplate,
    seq_len: usize, // m (W length)
    boundary: &[i8],
    spectral_bound: f64, // (6n-2)/2
    num_freqs: usize,    // how many frequency constraints to add
) {
    let mid_var = |i: usize| -> i32 { (i + 1) as i32 };
    let m = seq_len;
    let pi2 = 2.0 * std::f64::consts::PI;
    const SCALE: f64 = 1000.0;

    // Budget: P(ω) = m + 2*Σ_s N_W(s)*cos ≤ B
    // => Σ_s N_W(s)*cos ≤ (B - m) / 2
    // N_W(s) = 2*agree(s) - num_pairs(s)
    // => 2*Σ_s agree(s)*cos - Σ_s num_pairs(s)*cos ≤ (B-m)/2
    // => Σ_s agree(s)*cos ≤ ((B-m)/2 + Σ_s num_pairs(s)*cos) / 2
    //
    // Split agree(s) = agree_const(s) + variable_agree(s)
    // => Σ_s variable_agree(s)*cos ≤ threshold - Σ_s agree_const(s)*cos

    for fi in 0..num_freqs {
        // Sample frequencies evenly in (0, 0.5) — avoid ω=0 (trivially loose)
        let omega = (fi as f64 + 1.0) / (num_freqs as f64 + 1.0) * 0.5;

        let mut const_weighted = 0.0f64; // Σ agree_const(s) * cos(s,ω)
        let mut baseline = 0.0f64; // Σ num_pairs(s) * cos(s,ω)

        // Collect (literal, float_weight) pairs for variable agree terms
        let mut lit_weights: Vec<(i32, f64)> = Vec::new();

        for (si, lag) in tmpl.lags.iter().enumerate() {
            let s = si + 1;
            let cos_val = (pi2 * s as f64 * omega / m as f64).cos();

            baseline += lag.num_pairs as f64 * cos_val;

            // bnd×bnd constant contribution
            let mut agree_const = 0u32;
            for &(i, j) in &lag.bnd_bnd {
                if boundary[i] == boundary[j] {
                    agree_const += 1;
                }
            }
            const_weighted += agree_const as f64 * cos_val;

            // bnd×mid variable terms
            for &(bnd_pos, mid_idx) in &lag.bnd_mid {
                let lit = if boundary[bnd_pos] == 1 {
                    mid_var(mid_idx)
                } else {
                    -mid_var(mid_idx)
                };
                lit_weights.push((lit, cos_val));
            }

            // mid×mid aux var terms
            for (qi, _) in lag.mid_mid.iter().enumerate() {
                lit_weights.push((lag.aux_base + qi as i32, cos_val));
            }
        }

        if lit_weights.is_empty() {
            continue;
        }

        // Threshold for variable part:
        // Σ variable_agree * cos ≤ ((B-m)/2 + baseline) / 2 - const_weighted
        let threshold = ((spectral_bound - m as f64) / 2.0 + baseline) / 2.0 - const_weighted;

        // Convert "Σ w_i * x_i ≤ threshold" (w_i can be negative) to PB atleast.
        // For positive w_i: contribute w_i when x_i=1, so negate lit for atleast.
        // For negative w_i: contribute |w_i| when x_i=0, so keep lit for atleast.
        // PB: Σ_{w>0} w*¬x + Σ_{w<0} |w|*x ≥ Σ_{w>0} w - threshold
        let mut pb_lits: Vec<i32> = Vec::with_capacity(lit_weights.len());
        let mut pb_coeffs: Vec<u32> = Vec::with_capacity(lit_weights.len());
        let mut sum_positive = 0.0f64;

        for &(lit, w) in &lit_weights {
            let scaled_w = (w * SCALE).round();
            if scaled_w.abs() < 1.0 {
                continue;
            } // skip near-zero weights

            if scaled_w > 0.0 {
                pb_lits.push(-lit); // negate: count when x_i=0
                pb_coeffs.push(scaled_w as u32);
                sum_positive += scaled_w;
            } else {
                pb_lits.push(lit);
                pb_coeffs.push((-scaled_w) as u32);
            }
        }

        let bound = sum_positive - threshold * SCALE;
        if bound <= 0.0 {
            continue;
        } // trivially satisfied
        let bound = bound.ceil() as u32;

        if !pb_lits.is_empty() {
            solver.add_pb_atleast(&pb_lits, &pb_coeffs, bound);
        }
    }
}

/// Result of a boundary-side rule (iv)/(v) check.  Used by the Z and W
/// middle SAT builders to fold rule (iv)/(v) into the SAT encoding, and
/// by the MDD walker as an O(k) pre-filter that avoids spinning up the
/// middle SAT at all when the boundary already violates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BoundaryRuleState {
    /// The rule's first-violation index is strictly inside the boundary
    /// AND the boundary value at that index is correct (+1).  The rule
    /// is already satisfied; no middle-SAT clauses need to be emitted.
    SatisfiedAtBoundary,
    /// The rule's first-violation index is strictly inside the boundary
    /// AND the boundary value at that index is wrong (-1).  The whole
    /// boundary is infeasible — middle SAT should not be built.
    ViolatedAtBoundary,
    /// No first-violation index falls inside the boundary.  The rule
    /// may still fire at a middle index, so the middle SAT must emit
    /// its own first-violation clauses for the middle pairs.
    DeferredToMiddle,
}

/// BDKR rule (iv) — Z palindromic-equality break, applied to the
/// boundary only (O(k)).  Scans pair indices `j = 0..k-1` in order
/// and returns the first-violation state of the boundary.
pub fn check_z_boundary_rule_iv(n: usize, k: usize, z_boundary: &[i8]) -> BoundaryRuleState {
    let last_j = (n - 2) / 2;
    let bnd_end = k.min(last_j + 1);
    for j in 0..bnd_end {
        if z_boundary[j] == z_boundary[n - 1 - j] {
            return if z_boundary[j] == 1 {
                BoundaryRuleState::SatisfiedAtBoundary
            } else {
                BoundaryRuleState::ViolatedAtBoundary
            };
        }
    }
    BoundaryRuleState::DeferredToMiddle
}

/// BDKR rule (v) — W alternation break, applied to the boundary only.
/// d[m-1] is in the suffix boundary so its sign is known; the first-
/// violation at a boundary pair k < K is thus fully determined.
pub fn check_w_boundary_rule_v(m: usize, k: usize, w_boundary: &[i8]) -> BoundaryRuleState {
    if m < 3 {
        return BoundaryRuleState::DeferredToMiddle;
    }
    let last_p = (m - 2) / 2;
    let tail = w_boundary[m - 1];
    let bnd_end = k.min(last_p + 1);
    for p in 0..bnd_end {
        let prod = (w_boundary[p] as i32) * (w_boundary[m - 1 - p] as i32);
        if prod as i8 != tail {
            return if w_boundary[p] == 1 {
                BoundaryRuleState::SatisfiedAtBoundary
            } else {
                BoundaryRuleState::ViolatedAtBoundary
            };
        }
    }
    BoundaryRuleState::DeferredToMiddle
}

/// Emit rule-(iv) middle-pair clauses into the Z-middle solver.  Only
/// called when `check_z_boundary_rule_iv` returns `DeferredToMiddle`,
/// i.e., every boundary palindrome pair has diff=T (non-palindromic),
/// so boundary literals contribute nothing to the disjunction.
///
/// `mid_var` maps a full-sequence position (in the middle range
/// `[k, n-k-1]`) to a SAT variable ID.  This lets the same helper
/// work for the separate Z-middle SAT (`mid_var(jf) = jf - k + 1`)
/// and the combined W+Z SolveWZ SAT (`mid_var(jf) = middle_m + jf - k + 1`).
///
/// `next_var` is advanced by the number of aux vars consumed.
pub fn add_rule_iv_middle_clauses(
    solver: &mut radical::Solver,
    n: usize,
    k: usize,
    mid_var: impl Fn(usize) -> i32,
    next_var: &mut i32,
) {
    let last_j = (n - 2) / 2;
    if k > last_j {
        return;
    }
    let mid_start = k;
    let mid_end = last_j;
    let n_aux = mid_end - mid_start + 1;
    let base = *next_var;
    *next_var += n_aux as i32;
    let diff = |jf: usize| base + (jf - mid_start) as i32;
    for j in mid_start..=mid_end {
        let a = mid_var(j);
        let b = mid_var(n - 1 - j);
        solver.add_clause([-diff(j), a, b]);
        solver.add_clause([-diff(j), -a, -b]);
        solver.add_clause([diff(j), a, -b]);
        solver.add_clause([diff(j), -a, b]);
    }
    for i in mid_start..=mid_end {
        let mut clause: Vec<i32> = Vec::with_capacity(i - mid_start + 2);
        for j in mid_start..i {
            clause.push(-diff(j));
        }
        clause.push(diff(i));
        clause.push(mid_var(i));
        solver.add_clause(clause);
    }
}

/// Emit rule-(v) middle-pair clauses into the W-middle solver.  Only
/// called when `check_w_boundary_rule_v` returns `DeferredToMiddle`.
/// `d[m-1]` is a boundary constant, which folds into the XOR
/// definition — v_k depends only on the two middle vars when the tail
/// is +1, and is negated when the tail is -1.
///
/// `mid_var` maps a full-sequence position to a SAT var, same
/// convention as `add_rule_iv_middle_clauses`.
pub fn add_rule_v_middle_clauses(
    solver: &mut radical::Solver,
    m: usize,
    k: usize,
    w_boundary: &[i8],
    mid_var: impl Fn(usize) -> i32,
    next_var: &mut i32,
) {
    if m < 3 {
        return;
    }
    let last_p = (m - 2) / 2;
    if k > last_p {
        return;
    }
    let mid_start = k;
    let mid_end = last_p;
    let n_aux = mid_end - mid_start + 1;
    let base_u = *next_var;
    *next_var += n_aux as i32;
    let base_v = *next_var;
    *next_var += n_aux as i32;
    let u = |p: usize| base_u + (p - mid_start) as i32;
    let v = |p: usize| base_v + (p - mid_start) as i32;
    let tail_sign = w_boundary[m - 1];
    for p in mid_start..=mid_end {
        let a = mid_var(p);
        let b = mid_var(m - 1 - p);
        // u_p ↔ a XOR b
        solver.add_clause([-u(p), a, b]);
        solver.add_clause([-u(p), -a, -b]);
        solver.add_clause([u(p), a, -b]);
        solver.add_clause([u(p), -a, b]);
        // v_p ↔ u_p XOR tail.  tail is a constant ±1; when tail=+1,
        // v_p = u_p; when tail=-1, v_p = ¬u_p.
        if tail_sign == 1 {
            solver.add_clause([-v(p), u(p)]);
            solver.add_clause([v(p), -u(p)]);
        } else {
            solver.add_clause([-v(p), -u(p)]);
            solver.add_clause([v(p), u(p)]);
        }
    }
    // Rule (v): least i with inequality (w[i]·w[m-1-i] != tail) has
    // w[i]=+1.  v(p)=TRUE encodes "inequality at p".  The clause says:
    //   (∃ j<i : inequality at j)  ∨  (no inequality at i)  ∨  w[i]=+1
    // i.e., "if i is the first inequality then w[i]=+1".  Note the v
    // literals here are the OPPOSITE sign to rule (iv)'s diff literals,
    // because rule (iv) watches EQUALITY (diff=FALSE) and rule (v)
    // watches INEQUALITY (v=TRUE).
    for i in mid_start..=mid_end {
        let mut clause: Vec<i32> = Vec::with_capacity(i - mid_start + 2);
        for j in mid_start..i {
            clause.push(v(j));
        }
        clause.push(-v(i));
        clause.push(mid_var(i));
        solver.add_clause(clause);
    }
}

/// Legacy: build Z middle solver from scratch (no template).
/// Kept for the `--phase-b --wz=apart` diagnostic path.
pub fn build_z_middle_solver(
    n: usize,
    m: usize,
    k: usize,
    z_boundary: &[i8],
    w_vals: &[i8],
    z_mid_sum: i32,
) -> radical::Solver {
    let middle_n = n - 2 * k;
    let tmpl = LagTemplate::new(n, k);
    let mut solver = tmpl.build_base_solver(middle_n, z_mid_sum);
    fill_z_solver(&mut solver, &tmpl, n, m, z_boundary, w_vals);
    solver
}
