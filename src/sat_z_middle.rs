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
    /// Build template for Z middle (length n, boundary width k).
    pub fn new_z(n: usize, k: usize) -> Self {
        let middle_n = n - 2 * k;
        let is_mid = |pos: usize| -> bool { pos >= k && pos < n - k };

        let mut lags = Vec::with_capacity(n - 1);
        for s in 1..n {
            let num_pairs = n - s;
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
                    bnd_mid.push((j, i - k)); // (bnd_pos, mid_idx)
                } else if !i_mid && j_mid {
                    bnd_mid.push((i, j - k));
                } else {
                    mid_mid.push((i - k, j - k));
                }
            }

            let aux_base = (middle_n + 1 + s * n) as i32;
            lags.push(LagInfo { bnd_bnd, bnd_mid, mid_mid, aux_base, num_pairs });
        }

        LagTemplate { lags }
    }

    /// Build template for W middle (length m, boundary width k).
    pub fn new_w(m: usize, k: usize) -> Self {
        let middle_m = m - 2 * k;
        let is_mid = |pos: usize| -> bool { pos >= k && pos < m - k };

        let mut lags = Vec::with_capacity(m - 1);
        for s in 1..m {
            let num_pairs = m - s;
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

            let aux_base = (middle_m + 1 + s * m) as i32;
            lags.push(LagInfo { bnd_bnd, bnd_mid, mid_mid, aux_base, num_pairs });
        }

        LagTemplate { lags }
    }

    /// Build a base solver with sum constraint + XNOR aux clauses (boundary-independent).
    /// Clone this and call `fill_for_boundary` to get a boundary-specific solver.
    pub fn build_base_solver(&self, middle_len: usize, mid_sum: i32) -> radical::Solver {
        let mut solver = radical::Solver::new();
        let mid_var = |i: usize| -> i32 { (i + 1) as i32 };

        // Sum constraint
        let mid_ones = ((mid_sum + middle_len as i32) / 2) as usize;
        let lits: Vec<i32> = (0..middle_len).map(|i| mid_var(i)).collect();
        let ones: Vec<u32> = vec![1; middle_len];
        solver.add_pb_eq(&lits, &ones, mid_ones as u32);

        // XNOR aux clauses for all mid×mid pairs (boundary-independent)
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
            (0..m - s).map(|i| w_vals[i] as i32 * w_vals[i + s] as i32).sum()
        } else { 0 };

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
        if adj_lo == 0 && adj_hi >= max_variable { continue; }

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
            if boundary[i] == boundary[j] { agree_const += 1; }
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

        if adj_lo == 0 && adj_hi >= max_variable { continue; }

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
    seq_len: usize,       // m (W length)
    boundary: &[i8],
    spectral_bound: f64,  // (6n-2)/2
    num_freqs: usize,     // how many frequency constraints to add
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

        let mut const_weighted = 0.0f64;  // Σ agree_const(s) * cos(s,ω)
        let mut baseline = 0.0f64;        // Σ num_pairs(s) * cos(s,ω)

        // Collect (literal, float_weight) pairs for variable agree terms
        let mut lit_weights: Vec<(i32, f64)> = Vec::new();

        for (si, lag) in tmpl.lags.iter().enumerate() {
            let s = si + 1;
            let cos_val = (pi2 * s as f64 * omega / m as f64).cos();

            baseline += lag.num_pairs as f64 * cos_val;

            // bnd×bnd constant contribution
            let mut agree_const = 0u32;
            for &(i, j) in &lag.bnd_bnd {
                if boundary[i] == boundary[j] { agree_const += 1; }
            }
            const_weighted += agree_const as f64 * cos_val;

            // bnd×mid variable terms
            for &(bnd_pos, mid_idx) in &lag.bnd_mid {
                let lit = if boundary[bnd_pos] == 1 { mid_var(mid_idx) } else { -mid_var(mid_idx) };
                lit_weights.push((lit, cos_val));
            }

            // mid×mid aux var terms
            for (qi, _) in lag.mid_mid.iter().enumerate() {
                lit_weights.push((lag.aux_base + qi as i32, cos_val));
            }
        }

        if lit_weights.is_empty() { continue; }

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
            if scaled_w.abs() < 1.0 { continue; } // skip near-zero weights

            if scaled_w > 0.0 {
                pb_lits.push(-lit);  // negate: count when x_i=0
                pb_coeffs.push(scaled_w as u32);
                sum_positive += scaled_w;
            } else {
                pb_lits.push(lit);
                pb_coeffs.push((-scaled_w) as u32);
            }
        }

        let bound = sum_positive - threshold * SCALE;
        if bound <= 0.0 { continue; } // trivially satisfied
        let bound = bound.ceil() as u32;

        if !pb_lits.is_empty() {
            solver.add_pb_atleast(&pb_lits, &pb_coeffs, bound);
        }
    }
}

/// Legacy: build Z middle solver from scratch (no template).
/// Kept for the --phase-b --mdd path.
pub fn build_z_middle_solver(
    n: usize,
    m: usize,
    k: usize,
    z_boundary: &[i8],
    w_vals: &[i8],
    z_mid_sum: i32,
) -> radical::Solver {
    let middle_n = n - 2 * k;
    let tmpl = LagTemplate::new_z(n, k);
    let mut solver = tmpl.build_base_solver(middle_n, z_mid_sum);
    fill_z_solver(&mut solver, &tmpl, n, m, z_boundary, w_vals);
    solver
}
