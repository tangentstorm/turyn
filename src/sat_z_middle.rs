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

/// Build a SAT solver for Z middle and return it.
/// z_boundary: full z values with middle positions set to 0 (placeholder)
/// w_vals: complete W sequence
/// k: boundary width
/// Returns solver with z_mid vars as variables 1..middle_n
pub fn build_z_middle_solver(
    n: usize,
    m: usize,
    k: usize,
    z_boundary: &[i8],   // z[0..n], boundary positions filled, middle = 0
    w_vals: &[i8],       // complete W of length m
    z_mid_sum: i32,       // required sum of z middle positions
) -> radical::Solver {
    let middle_n = n - 2 * k;
    let mut solver = radical::Solver::new();

    // Variables: 1..middle_n represent z_mid[0]..z_mid[middle_n-1]
    // z_mid[i] corresponds to z[k+i] in the full sequence
    let mid_var = |i: usize| -> i32 { (i + 1) as i32 };

    // Sum constraint: exactly z_mid_ones of middle_n vars are +1
    let z_mid_ones = ((z_mid_sum + middle_n as i32) / 2) as usize;
    {
        let lits: Vec<i32> = (0..middle_n).map(|i| mid_var(i)).collect();
        let ones: Vec<u32> = vec![1; middle_n];
        solver.add_pb_eq(&lits, &ones, z_mid_ones as u32);
    }

    // For each lag s (1..n-1), encode range constraint on N_Z(s)
    // N_W(s) is known from w_vals
    for s in 1..n {
        // Compute N_W(s)
        let nw_s: i32 = if s < m {
            (0..m - s).map(|i| w_vals[i] as i32 * w_vals[i + s] as i32).sum()
        } else { 0 };

        // Range for N_Z(s): 2*N_Z(s) + 2*N_W(s) must be in [-2*(n-s), 2*(n-s)]
        // => N_Z(s) in [-(n-s) - N_W(s), (n-s) - N_W(s)]
        let max_nz = (n - s) as i32;
        let lo = (-max_nz).max(-max_nz - nw_s);
        let hi = max_nz.min(max_nz - nw_s);
        // Also parity: N_Z(s) has same parity as (n-s)
        // And 2*N_Z(s) + 2*N_W(s) must have same parity as 2*(n-s) (always even)

        if lo > hi {
            // Infeasible — add empty clause
            solver.add_clause(std::iter::empty::<i32>());
            return solver;
        }

        // Decompose N_Z(s) = Σ_{i=0}^{n-s-1} z[i]*z[i+s]
        // Each pair (i, i+s): classify as (bnd,bnd), (bnd,mid), (mid,mid)
        let is_mid = |pos: usize| -> bool { pos >= k && pos < n - k };

        let mut const_contrib: i32 = 0;
        // For PB: agree_count = number of pairs where z[i]==z[i+s]
        // N_Z(s) = 2*agree_count - (n-s)
        // So agree_count = (N_Z(s) + (n-s)) / 2
        // Range on agree_count: [(lo + max_nz) / 2, (hi + max_nz) / 2]
        // But lo and max_nz have same parity, so division is exact.
        let agree_lo = ((lo + max_nz) / 2) as u32;
        let agree_hi = ((hi + max_nz) / 2) as u32;

        let mut agree_lits: Vec<i32> = Vec::new(); // literals that are true when pair agrees
        let mut agree_const: u32 = 0; // constant agree count from bnd×bnd pairs
        let mut quad_a: Vec<i32> = Vec::new(); // quad PB: lits_a
        let mut quad_b: Vec<i32> = Vec::new(); // quad PB: lits_b

        for i in 0..n - s {
            let j = i + s;
            let i_mid = is_mid(i);
            let j_mid = is_mid(j);

            if !i_mid && !j_mid {
                // Both boundary: constant
                if z_boundary[i] == z_boundary[j] {
                    agree_const += 1;
                }
            } else if i_mid && !j_mid {
                // i is middle, j is boundary
                let mid_idx = i - k;
                let bnd_val = z_boundary[j];
                // agree iff z_mid[mid_idx] == bnd_val
                // If bnd_val = +1: agree iff mid_var is true → literal = mid_var
                // If bnd_val = -1: agree iff mid_var is false → literal = -mid_var
                if bnd_val == 1 {
                    agree_lits.push(mid_var(mid_idx));
                } else {
                    agree_lits.push(-mid_var(mid_idx));
                }
            } else if !i_mid && j_mid {
                // i is boundary, j is middle
                let mid_idx = j - k;
                let bnd_val = z_boundary[i];
                if bnd_val == 1 {
                    agree_lits.push(mid_var(mid_idx));
                } else {
                    agree_lits.push(-mid_var(mid_idx));
                }
            } else {
                // Both middle: quadratic
                let mid_a = i - k;
                let mid_b = j - k;
                // agree iff z_mid[a] == z_mid[b]
                // This is XNOR: need aux var or quad PB
                // For quad PB: agree = mid_a XNOR mid_b
                // Store for quad PB encoding
                quad_a.push(mid_var(mid_a));
                quad_b.push(mid_var(mid_b));
            }
        }

        // Now: agree_count = agree_const + count(agree_lits true) + count(quad agrees)
        // Target: agree_lo ≤ total ≤ agree_hi
        // Adjusted for const: (agree_lo - agree_const) ≤ linear + quad ≤ (agree_hi - agree_const)

        if agree_lo > agree_const + agree_lits.len() as u32 + quad_a.len() as u32 {
            // Infeasible even if all agree
            solver.add_clause(std::iter::empty::<i32>());
            return solver;
        }

        let adj_lo = agree_lo.saturating_sub(agree_const);
        let adj_hi = agree_hi - agree_const;

        if agree_lits.is_empty() && quad_a.is_empty() {
            // Only constant terms — just check feasibility
            if agree_const < agree_lo || agree_const > agree_hi {
                solver.add_clause(std::iter::empty::<i32>());
                return solver;
            }
            continue;
        }

        if quad_a.is_empty() {
            // Only linear terms — use PB constraints
            let ones: Vec<u32> = vec![1; agree_lits.len()];
            if adj_lo > 0 {
                solver.add_pb_atleast(&agree_lits, &ones, adj_lo);
            }
            if adj_hi < agree_lits.len() as u32 {
                // at-most = negate all lits and use atleast(n - hi)
                let neg_lits: Vec<i32> = agree_lits.iter().map(|&l| -l).collect();
                solver.add_pb_atleast(&neg_lits, &ones, agree_lits.len() as u32 - adj_hi);
            }
        } else {
            // Has quadratic terms — use quad PB
            // Total agree = linear_agree + quad_agree
            // We need: adj_lo ≤ linear + quad ≤ adj_hi
            //
            // For the quad PB encoding: each quad term is agree(a,b) = a XNOR b.
            // Use XNOR aux variables:
            //   aux_i ↔ (a_i ↔ b_i)  [4 clauses each]
            // Then total = sum(agree_lits true) + sum(aux_i true)
            // Encode as PB: sum(all) ∈ [adj_lo, adj_hi]

            let mut all_lits = agree_lits.clone();
            let base_var = middle_n as i32 + 1; // aux vars start after mid vars
            // We need a unique range of aux vars per lag. Use a global counter.
            // For simplicity, use var IDs starting from middle_n + lag_offset.
            // This is fragile — better to track next_var.
            // For now, use a high offset per lag.
            let aux_base = (middle_n + 1 + s * n) as i32; // should be unique per lag

            for (qi, (&a, &b)) in quad_a.iter().zip(quad_b.iter()).enumerate() {
                let aux = aux_base + qi as i32;
                // aux ↔ (a ↔ b): XNOR encoding
                // aux → (a ↔ b): (-aux ∨ -a ∨ b) ∧ (-aux ∨ a ∨ -b)
                // (a ↔ b) → aux: (a ∨ b ∨ aux) ∧ (-a ∨ -b ∨ aux)
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
