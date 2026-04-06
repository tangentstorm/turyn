/// SAT encoding for W middle given fixed W boundary.
///
/// Variables: w_mid[0..middle_m-1] (true = +1, false = -1)
/// Constraints:
///   - Sum: exactly w_mid_ones of middle_m vars are +1
///   - For each lag s: N_W(s) agree count in [agree_lo, agree_hi]
///     where bounds come from the trivial range |N_W(s)| ≤ m-s.
///     The decomposition into boundary×boundary (const), boundary×middle
///     (linear), and middle×middle (quadratic) terms creates CDCL-exploitable
///     variable interactions that approximate spectral filtering.
///
/// N_W(s) = Σ w[i]*w[i+s] decomposes into:
///   - const: boundary×boundary pairs (known)
///   - linear: boundary×middle pairs (±mid_var)
///   - quad: middle×middle pairs (mid_var_a * mid_var_b)

/// Build a SAT solver for W middle and return it.
/// k: boundary width
/// w_boundary: w[0..m] with boundary positions filled, middle = 0
/// Returns solver with w_mid vars as variables 1..middle_m
pub fn build_w_middle_solver(
    m: usize,
    k: usize,
    w_mid_sum: i32,
    w_boundary: &[i8],
) -> radical::Solver {
    let middle_m = m - 2 * k;
    let mut solver = radical::Solver::new();

    let mid_var = |i: usize| -> i32 { (i + 1) as i32 };

    // Sum constraint: exactly w_mid_ones of middle_m vars are +1
    let w_mid_ones = ((w_mid_sum + middle_m as i32) / 2) as usize;
    {
        let lits: Vec<i32> = (0..middle_m).map(|i| mid_var(i)).collect();
        let ones: Vec<u32> = vec![1; middle_m];
        solver.add_pb_eq(&lits, &ones, w_mid_ones as u32);
    }

    // For each lag s, encode agree-count range constraint on N_W(s).
    // N_W(s) ∈ [-(m-s), m-s] (trivially), but the decomposition into
    // const + linear + quad tightens the adjusted range and creates
    // variable interactions the CDCL solver exploits.
    let is_mid = |pos: usize| -> bool { pos >= k && pos < m - k };

    for s in 1..m {
        let num_pairs = m - s;
        // N_W(s) ∈ [-(num_pairs as i32), num_pairs as i32]
        let agree_lo = 0u32;
        let agree_hi = num_pairs as u32;

        let mut agree_lits: Vec<i32> = Vec::new();
        let mut agree_const: u32 = 0;
        let mut quad_a: Vec<i32> = Vec::new();
        let mut quad_b: Vec<i32> = Vec::new();

        for i in 0..num_pairs {
            let j = i + s;
            let i_mid = is_mid(i);
            let j_mid = is_mid(j);

            if !i_mid && !j_mid {
                if w_boundary[i] == w_boundary[j] {
                    agree_const += 1;
                }
            } else if i_mid && !j_mid {
                let mid_idx = i - k;
                if w_boundary[j] == 1 {
                    agree_lits.push(mid_var(mid_idx));
                } else {
                    agree_lits.push(-mid_var(mid_idx));
                }
            } else if !i_mid && j_mid {
                let mid_idx = j - k;
                if w_boundary[i] == 1 {
                    agree_lits.push(mid_var(mid_idx));
                } else {
                    agree_lits.push(-mid_var(mid_idx));
                }
            } else {
                let mid_a = i - k;
                let mid_b = j - k;
                quad_a.push(mid_var(mid_a));
                quad_b.push(mid_var(mid_b));
            }
        }

        // Adjusted range after removing boundary×boundary constant
        let adj_lo = agree_lo.saturating_sub(agree_const);
        let adj_hi = agree_hi - agree_const;
        let max_variable = agree_lits.len() as u32 + quad_a.len() as u32;

        // Skip if constraints are trivially satisfied
        if adj_lo == 0 && adj_hi >= max_variable { continue; }

        if agree_lits.is_empty() && quad_a.is_empty() {
            if agree_const < agree_lo || agree_const > agree_hi {
                solver.add_clause(std::iter::empty::<i32>());
                return solver;
            }
            continue;
        }

        if adj_lo > max_variable {
            solver.add_clause(std::iter::empty::<i32>());
            return solver;
        }

        if quad_a.is_empty() {
            let ones: Vec<u32> = vec![1; agree_lits.len()];
            if adj_lo > 0 {
                solver.add_pb_atleast(&agree_lits, &ones, adj_lo);
            }
            if adj_hi < agree_lits.len() as u32 {
                let neg_lits: Vec<i32> = agree_lits.iter().map(|&l| -l).collect();
                solver.add_pb_atleast(&neg_lits, &ones, agree_lits.len() as u32 - adj_hi);
            }
        } else {
            let mut all_lits = agree_lits.clone();
            let aux_base = (middle_m + 1 + s * m) as i32;

            for (qi, (&a, &b)) in quad_a.iter().zip(quad_b.iter()).enumerate() {
                let aux = aux_base + qi as i32;
                solver.add_clause([-aux, -a, b]);
                solver.add_clause([-aux, a, -b]);
                solver.add_clause([a, b, aux]);
                solver.add_clause([-a, -b, aux]);
                all_lits.push(aux);
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

    solver
}

/// Simple sum-only W middle solver (no autocorrelation constraints).
/// Used when boundary is not yet known (shared across entries).
pub fn build_w_middle_solver_sum_only(
    m: usize,
    k: usize,
    w_mid_sum: i32,
) -> radical::Solver {
    let middle_m = m - 2 * k;
    let mut solver = radical::Solver::new();

    let w_mid_ones = ((w_mid_sum + middle_m as i32) / 2) as usize;
    let lits: Vec<i32> = (0..middle_m).map(|i| (i + 1) as i32).collect();
    let ones: Vec<u32> = vec![1; middle_m];
    solver.add_pb_eq(&lits, &ones, w_mid_ones as u32);

    solver
}
