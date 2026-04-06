/// SAT encoding for W middle given fixed W boundary.
///
/// Variables: w_mid[0..middle_m-1] (true = +1, false = -1)
/// Constraints:
///   - Sum: exactly w_mid_ones of middle_m vars are +1
///
/// Unlike Z middle (which knows the full W and can encode tight autocorrelation
/// range constraints), W middle has no external sequence to constrain against.
/// The sum constraint is the primary hard constraint; spectral filtering is
/// applied post-hoc after extracting each solution.

/// Build a SAT solver for W middle and return it.
/// w_boundary: full w values with middle positions set to 0 (placeholder)
/// k: boundary width
/// Returns solver with w_mid vars as variables 1..middle_m
pub fn build_w_middle_solver(
    m: usize,
    k: usize,
    w_mid_sum: i32,
) -> radical::Solver {
    let middle_m = m - 2 * k;
    let mut solver = radical::Solver::new();

    // Variables: 1..middle_m represent w_mid[0]..w_mid[middle_m-1]
    // w_mid[i] corresponds to w[k+i] in the full sequence

    // Sum constraint: exactly w_mid_ones of middle_m vars are +1
    let w_mid_ones = ((w_mid_sum + middle_m as i32) / 2) as usize;
    {
        let lits: Vec<i32> = (0..middle_m).map(|i| (i + 1) as i32).collect();
        let ones: Vec<u32> = vec![1; middle_m];
        solver.add_pb_eq(&lits, &ones, w_mid_ones as u32);
    }

    solver
}
