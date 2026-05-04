//! Stage 3 prototype for the inside-out MDD design (see
//! `docs/INSIDE-OUT-MDD.md`).
//!
//! Implements a joint 4-sequence inside-out walker that:
//!   1. Walks middle positions outward from the centre, placing one
//!      pair-of-bits per sequence at each level (16 children per
//!      node before pruning).
//!   2. Tracks the Turyn-weighted middle-middle lag-sum vector
//!      `mm_sum[s]` for `s = 1..n-1` at every node.
//!   3. Prunes branches where `|mm_sum[s]|` exceeds the maximum
//!      possible compensation from the boundary (a bound that
//!      tightens as we approach the boundary).
//!   4. At each leaf, computes the high-lag target the boundary
//!      must produce and queries the `T_xy` / `T_zw` boundary
//!      index built in Stage 1+2 (see `lag_sum_decomp.rs`).
//!   5. Reports leaves visited, leaves with non-empty boundary
//!      candidate sets, and average candidates per leaf.
//!
//! Usage:
//!   target/release/inside_out_walk <n> <k>
//!
//! Tractable scales: n=10 k=3, n=14 k=4 (24-bit middle space, 16M
//! leaves max), n=18 k=4 only with strong pruning.

use std::collections::HashMap;
use std::fs;

fn parse_seq(s: &str) -> Vec<i32> {
    s.chars()
        .map(|c| match c {
            '+' => 1i32,
            '-' => -1i32,
            _ => panic!("bad char in seq"),
        })
        .collect()
}

fn read_known(n: usize) -> Option<(Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>)> {
    let body = fs::read_to_string("known_solutions.txt").ok()?;
    for line in body.lines() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        let mut parts = line.split_whitespace();
        let n_str = parts.next()?;
        if n_str.parse::<usize>().ok()? != n {
            continue;
        }
        let x = parse_seq(parts.next()?);
        let y = parse_seq(parts.next()?);
        let z = parse_seq(parts.next()?);
        let w = parse_seq(parts.next()?);
        return Some((x, y, z, w));
    }
    None
}

fn autocorr_bb(x: &[i32], s: usize, k: usize) -> i32 {
    let n = x.len();
    if s >= n {
        return 0;
    }
    let in_bd = |i: usize| i < k || i >= n - k;
    (0..n - s)
        .filter(|&i| in_bd(i) && in_bd(i + s))
        .map(|i| x[i] * x[i + s])
        .sum()
}

/// Build a length-`seq_len` sequence with the boundary set from
/// `2k` bits (low-k bits then high-k bits) and zeros elsewhere.
fn make_bd(seq_len: usize, bits: u32, k: usize) -> Vec<i32> {
    let mut s = vec![0i32; seq_len];
    for i in 0..k {
        let bit = (bits >> i) & 1;
        s[i] = if bit == 1 { 1 } else { -1 };
        let bit2 = (bits >> (k + i)) & 1;
        s[seq_len - k + i] = if bit2 == 1 { 1 } else { -1 };
    }
    s
}

/// "Very-high" lag range: `[n-k, n-1]`. At these lags the cross
/// term (boundary × middle) is exactly zero, because the only pairs
/// at lag s ≥ n-k with at least one position in the boundary
/// require both positions in the boundary (cross would need
/// j = i + s ≥ n-k with i in boundary [0..k) and j in middle [k..n-k)
/// — but j ≥ n-k is outside middle). So the index keyed on
/// very-high-lag bb is *exact*: no cross-term correction needed.
fn vh_lag_range(n: usize, k: usize) -> std::ops::RangeInclusive<usize> {
    (n - k)..=(n - 1)
}

/// Build boundary index `T_xy[v]` = list of `(X-bd-bits, Y-bd-bits)`
/// keyed on the very-high-lag bb-vector `bb_X + bb_Y` at lags
/// `[n-k..n-1]`. Length k.
fn build_xy_table(k: usize, n: usize) -> HashMap<Vec<i32>, Vec<(u32, u32)>> {
    let mut t: HashMap<Vec<i32>, Vec<(u32, u32)>> = HashMap::new();
    let bd_count = 1u64 << (2 * k);
    let vh = vh_lag_range(n, k);
    for x_bits in 0..bd_count {
        let xb = make_bd(n, x_bits as u32, k);
        for y_bits in 0..bd_count {
            let yb = make_bd(n, y_bits as u32, k);
            let key: Vec<i32> = vh
                .clone()
                .map(|s| autocorr_bb(&xb, s, k) + autocorr_bb(&yb, s, k))
                .collect();
            t.entry(key)
                .or_default()
                .push((x_bits as u32, y_bits as u32));
        }
    }
    t
}

/// Build boundary index `T_zw[v]` keyed on `2*bb_Z + 2*bb_W` at
/// the very-high-lag range `[n-k..n-1]`. W has length `m = n-1` and
/// only contributes for lags `s < m`.
fn build_zw_table(k: usize, n: usize) -> HashMap<Vec<i32>, Vec<(u32, u32)>> {
    let mut t: HashMap<Vec<i32>, Vec<(u32, u32)>> = HashMap::new();
    let m = n - 1;
    let bd_count = 1u64 << (2 * k);
    let vh = vh_lag_range(n, k);
    for z_bits in 0..bd_count {
        let zb = make_bd(n, z_bits as u32, k);
        for w_bits in 0..bd_count {
            let wb = make_bd(m, w_bits as u32, k);
            let key: Vec<i32> = vh
                .clone()
                .map(|s| {
                    let bz = 2 * autocorr_bb(&zb, s, k);
                    let bw = if s < m { 2 * autocorr_bb(&wb, s, k) } else { 0 };
                    bz + bw
                })
                .collect();
            t.entry(key)
                .or_default()
                .push((z_bits as u32, w_bits as u32));
        }
    }
    t
}

/// Per-node walker state at the inside-out walk.
#[derive(Clone)]
struct WalkerState {
    /// Turyn-weighted partial mm_sum at lag s, s in 1..n-1.
    /// Includes contributions from middle bits placed so far for all 4
    /// sequences with the (1, 1, 2, 2) Turyn weights.
    mm_sum: Vec<i32>,
    /// Number of pair-levels placed (each level adds 1 position to
    /// each side of the centre, in each of 4 sequences). When
    /// `level == n_levels`, the entire middle is placed.
    level: usize,
    /// Currently-placed middle bits per sequence. `seqs[k]` is the
    /// current full-length sequence buffer (positions outside the
    /// placed middle are zeros).
    seqs: [Vec<i32>; 4],
}

/// Inside-out walker: places middle positions in centre-outward
/// order. For middle `[k..n-k)` of length `mid_len = n - 2k`, we
/// process levels `0..n_levels` where `n_levels = mid_len / 2`
/// (assumes mid_len even; for odd we handle the centre singleton
/// at level 0).
fn pair_positions(level: usize, n: usize, k: usize) -> (Option<usize>, Option<usize>) {
    // mid range is [k, n-k)
    // pair walk: at level d, place positions (centre - d - 1, centre + d) where
    // centre = (k + (n-k)) / 2 = n/2.
    // mid_len even: at level 0, place (n/2 - 1, n/2). at level 1, place (n/2 - 2, n/2 + 1). etc.
    // mid_len odd: centre is single position n/2, place at level 0; then pairs.
    let mid_len = n - 2 * k;
    if mid_len % 2 == 0 {
        let half = mid_len / 2;
        if level >= half {
            return (None, None);
        }
        let lo = k + half - 1 - level;
        let hi = k + half + level;
        (Some(lo), Some(hi))
    } else {
        // odd: level 0 places single centre position
        if level == 0 {
            (Some(k + mid_len / 2), None)
        } else {
            let half = mid_len / 2;
            let lo = k + half - 1 - (level - 1);
            let hi = k + half + 1 + (level - 1);
            (Some(lo), Some(hi))
        }
    }
}

fn n_levels(n: usize, k: usize) -> usize {
    let mid_len = n - 2 * k;
    if mid_len % 2 == 0 {
        mid_len / 2
    } else {
        mid_len / 2 + 1
    }
}

/// Maximum |mm_sum[s]| achievable from any completion of the middle.
/// Conservative bound: for one sequence, |mm[s]| ≤ #(middle pairs at lag s).
/// Number of mid-mid pairs at lag s in middle [k..n-k) = max(0, n-2k-s).
/// Turyn-weighted total bound = (1+1+2+2) * (n-2k-s) = 6 * (n-2k-s).
/// We tighten this by accounting for already-placed bits whose
/// contribution is fixed: but for the first prune cut, the static
/// bound suffices.
fn mm_bound_static(n: usize, k: usize, s: usize) -> i32 {
    let mid_len = (n - 2 * k) as i32;
    if (s as i32) >= mid_len {
        0
    } else {
        6 * (mid_len - s as i32)
    }
}

/// Given the mm_sum at a leaf (full middle placed), compute the
/// very-high-lag target the boundary's bb must produce:
/// `bb_vh(s) = -mm_sum(s) - cross_vh(s)`. At very-high lags
/// `s ≥ n-k`, cross is exactly zero, so `bb_vh = -mm_vh`. The index
/// lookup is therefore *exact* on this restricted range.
fn vh_lag_target_from_leaf(state: &WalkerState, n: usize, k: usize) -> Vec<i32> {
    vh_lag_range(n, k).map(|s| -state.mm_sum[s - 1]).collect()
}

/// Pre-convolve `T_xy` and `T_zw` into a single map
/// `target_to_count[v] = Σ_{a+b=v} |T_xy[a]| * |T_zw[b]|`. This is
/// the count of 4-tuple boundaries whose combined Turyn-weighted
/// very-high-lag bb-vector is `v`. Replaces O(|T_zw|) per-leaf
/// lookup with O(1).
fn build_target_to_count(
    t_xy: &HashMap<Vec<i32>, Vec<(u32, u32)>>,
    t_zw: &HashMap<Vec<i32>, Vec<(u32, u32)>>,
) -> HashMap<Vec<i32>, u64> {
    let mut counts: HashMap<Vec<i32>, u64> = HashMap::new();
    for (xy_v, xy_pairs) in t_xy {
        let xy_n = xy_pairs.len() as u64;
        for (zw_v, zw_pairs) in t_zw {
            let v: Vec<i32> = xy_v.iter().zip(zw_v).map(|(a, b)| a + b).collect();
            *counts.entry(v).or_insert(0) += xy_n * zw_pairs.len() as u64;
        }
    }
    counts
}

/// Recursive inside-out walk. Returns a tuple of
/// (leaves_visited, leaves_with_match, total_candidates).
fn walk(
    state: &mut WalkerState,
    n: usize,
    k: usize,
    nlev: usize,
    target_to_count: &HashMap<Vec<i32>, u64>,
    pruned_out: &mut u64,
) -> (u64, u64, u64) {
    // Leaf?
    if state.level >= nlev {
        // Compute very-high-lag target (exact: cross = 0 here)
        let target = vh_lag_target_from_leaf(state, n, k);
        let total_cand = target_to_count.get(&target).copied().unwrap_or(0);
        return (1, if total_cand > 0 { 1 } else { 0 }, total_cand);
    }

    // Pruning: can the current mm_sum still satisfy
    //   mm_sum[s] + cross[s] + bb[s] = 0  for every lag s?
    // Conservative: |mm_sum[s]| ≤ |bb[s]| + |cross[s]| + (remaining mm contribution).
    // Static bound: |bb_total[s]| ≤ 8k + ... but easier — use the
    // global Turyn bound `|sum_all_terms| ≤ 6 * n` and prune anything
    // already obviously bad.
    let m = n - 1;
    for s in 1..n {
        let bound_mm_remaining = mm_bound_static(n, k, s);
        // If even with best-case cancellation the boundary can't fix
        // mm_sum[s], prune.
        // Approximate boundary capability: at most 6*k pair-products
        // at any single lag (X 2 + Y 2 + Z 2 + W 2 with weights 1,1,2,2 → max 12 pairs at distance s).
        // So |bb[s]| + |cross[s]| ≤ 12k for typical lag. For high lag s, fewer pairs.
        let bd_capacity = 12 * (k as i32);
        let _ = m;
        if (state.mm_sum[s - 1].abs() - bound_mm_remaining).abs() > bd_capacity * 2 {
            *pruned_out += 1;
            return (0, 0, 0);
        }
    }

    // Branch: assign next pair-of-positions for each of 4 sequences.
    // 4 sequences × 2 positions each = 8 bits = 256 branches at most.
    // For odd-mid level 0, only 1 position (singleton).
    let (lo, hi) = pair_positions(state.level, n, k);
    let n_bits_per_seq = match (lo, hi) {
        (Some(_), Some(_)) => 2,
        (Some(_), None) => 1,
        (None, _) => unreachable!(),
    };
    let total_bits = 4 * n_bits_per_seq;
    let n_branches = 1u32 << total_bits;

    let mut total_visited = 0u64;
    let mut total_match = 0u64;
    let mut total_cand = 0u64;

    for branch in 0..n_branches {
        // Assign bits per sequence
        for seq_i in 0..4 {
            let bits = (branch >> (seq_i * n_bits_per_seq)) & ((1u32 << n_bits_per_seq) - 1);
            let val_lo = if (bits & 1) == 1 { 1i32 } else { -1 };
            let val_hi = if n_bits_per_seq > 1 && ((bits >> 1) & 1) == 1 {
                1i32
            } else {
                -1i32
            };
            // For seq W (idx 3), the position must be < m = n-1.
            let seq_len = if seq_i == 3 { n - 1 } else { n };
            if let Some(p_lo) = lo {
                if p_lo < seq_len {
                    state.seqs[seq_i][p_lo] = val_lo;
                }
            }
            if n_bits_per_seq > 1 {
                if let Some(p_hi) = hi {
                    if p_hi < seq_len {
                        state.seqs[seq_i][p_hi] = val_hi;
                    }
                }
            }
        }

        // Update mm_sum incrementally: this is expensive to do
        // exactly at each step (O(n*k) per step); the prototype just
        // recomputes from scratch.
        let mut new_mm = vec![0i32; n - 1];
        for s in 1..n {
            // mm pair (i, j=i+s) with both i, j in mid [k..n-k).
            // For W (length n-1), mid is [k..(n-1)-k).
            for seq_i in 0..4 {
                let weight = if seq_i < 2 { 1 } else { 2 };
                let seq_len = if seq_i == 3 { n - 1 } else { n };
                let mid_lo = k;
                let mid_hi = seq_len - k;
                if mid_lo + s >= mid_hi {
                    continue;
                }
                let mut sum = 0i32;
                for i in mid_lo..(mid_hi - s) {
                    sum += state.seqs[seq_i][i] * state.seqs[seq_i][i + s];
                }
                new_mm[s - 1] += weight * sum;
            }
        }
        let saved_mm = std::mem::replace(&mut state.mm_sum, new_mm);
        state.level += 1;

        let (v, m, c) = walk(state, n, k, nlev, target_to_count, pruned_out);
        total_visited += v;
        total_match += m;
        total_cand += c;

        state.level -= 1;
        state.mm_sum = saved_mm;
    }

    (total_visited, total_match, total_cand)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args
        .get(1)
        .and_then(|s| s.parse().ok())
        .expect("usage: inside_out_walk <n> <k>");
    let k: usize = args
        .get(2)
        .and_then(|s| s.parse().ok())
        .expect("usage: inside_out_walk <n> <k>");
    if 2 * k >= n {
        panic!("need 2*k < n");
    }
    if 4 * k > 24 {
        panic!(
            "k={} too large; would need {} bits per pair table — try smaller",
            k,
            4 * k
        );
    }

    let m = n - 1;
    let nlev = n_levels(n, k);
    eprintln!("=== Inside-out walker for n={} k={} ===", n, k);
    eprintln!(
        "middle length = {}, n_levels = {}, total leaves (no pruning) ≤ 16^{} = {}",
        n - 2 * k,
        nlev,
        nlev,
        16u128.pow(nlev as u32)
    );

    eprintln!("Building boundary index T_xy ...");
    let t0 = std::time::Instant::now();
    let t_xy = build_xy_table(k, n);
    eprintln!(
        "  T_xy: {} keys, {} entries, built in {:.2}s",
        t_xy.len(),
        t_xy.values().map(|v| v.len()).sum::<usize>(),
        t0.elapsed().as_secs_f64()
    );
    let t1 = std::time::Instant::now();
    let t_zw = build_zw_table(k, n);
    eprintln!(
        "  T_zw: {} keys, {} entries, built in {:.2}s",
        t_zw.len(),
        t_zw.values().map(|v| v.len()).sum::<usize>(),
        t1.elapsed().as_secs_f64()
    );

    // Initial state: empty middle.
    let mut state = WalkerState {
        mm_sum: vec![0i32; n - 1],
        level: 0,
        seqs: [
            vec![0; n],
            vec![0; n],
            vec![0; n],
            vec![0; m],
        ],
    };

    eprintln!("Pre-convolving T_xy ⊕ T_zw into target_to_count ...");
    let t_conv = std::time::Instant::now();
    let target_to_count = build_target_to_count(&t_xy, &t_zw);
    let total_4tuples: u64 = target_to_count.values().sum();
    eprintln!(
        "  target_to_count: {} keys, {} 4-tuple entries, built in {:.2}s",
        target_to_count.len(),
        total_4tuples,
        t_conv.elapsed().as_secs_f64()
    );

    let mut pruned = 0u64;
    let t_walk = std::time::Instant::now();
    let (visited, matched, cand) = walk(&mut state, n, k, nlev, &target_to_count, &mut pruned);
    let walk_secs = t_walk.elapsed().as_secs_f64();

    eprintln!("\n=== Walker results ===");
    eprintln!("leaves visited     = {}", visited);
    eprintln!("leaves with match  = {}", matched);
    eprintln!("total candidates   = {}", cand);
    eprintln!(
        "avg candidates/leaf = {:.2}",
        if visited > 0 {
            cand as f64 / visited as f64
        } else {
            0.0
        }
    );
    eprintln!("subtree prunes     = {}", pruned);
    eprintln!("walk time          = {:.2}s", walk_secs);
    eprintln!(
        "naive  total leaves = {} (16^{})",
        16u128.pow(nlev as u32),
        nlev
    );

    // Sanity check: the known TT(n) solution's middle should be in
    // the leaves visited. We don't enumerate all leaves to check
    // membership (too expensive); instead, confirm the leaf for the
    // known middle would have been a feasible path (i.e., has a
    // non-empty boundary candidate set including the known boundary).
    if let Some((x, y, z, w)) = read_known(n) {
        eprintln!("\n=== Sanity: known TT({}) leaf check ===", n);
        // Compute mm_sum for the known middle
        let mut known_state = WalkerState {
            mm_sum: vec![0; n - 1],
            level: 0,
            seqs: [x.clone(), y.clone(), z.clone(), w.clone()],
        };
        // Set boundary bits to 0 in known_state's seqs
        for seq_i in 0..4 {
            let seq_len = if seq_i == 3 { n - 1 } else { n };
            for i in 0..k {
                known_state.seqs[seq_i][i] = 0;
                known_state.seqs[seq_i][seq_len - 1 - i] = 0;
            }
        }
        // Compute mm_sum from middle-only seqs
        for s in 1..n {
            let mut total = 0i32;
            for seq_i in 0..4 {
                let weight = if seq_i < 2 { 1 } else { 2 };
                let seq_len = if seq_i == 3 { n - 1 } else { n };
                let mid_lo = k;
                let mid_hi = seq_len - k;
                if mid_lo + s >= mid_hi {
                    continue;
                }
                for i in mid_lo..(mid_hi - s) {
                    total += weight * known_state.seqs[seq_i][i] * known_state.seqs[seq_i][i + s];
                }
            }
            known_state.mm_sum[s - 1] = total;
        }
        eprintln!(
            "known middle mm_sum = {:?}",
            &known_state.mm_sum[..]
        );
        let target = vh_lag_target_from_leaf(&known_state, n, k);
        eprintln!("known leaf very-high-lag target (= -mm_vh) = {:?}", target);
        let hits = target_to_count.get(&target).copied().unwrap_or(0);
        eprintln!("boundary candidates at known leaf  = {}", hits);
        // Confirm the known boundary tuple is in there
        let known_x_bits: u32 = (0..k)
            .map(|i| if x[i] == 1 { 1u32 << i } else { 0 })
            .sum::<u32>()
            + (0..k)
                .map(|i| if x[n - k + i] == 1 { 1u32 << (k + i) } else { 0 })
                .sum::<u32>();
        let known_y_bits: u32 = (0..k)
            .map(|i| if y[i] == 1 { 1u32 << i } else { 0 })
            .sum::<u32>()
            + (0..k)
                .map(|i| if y[n - k + i] == 1 { 1u32 << (k + i) } else { 0 })
                .sum::<u32>();
        let known_z_bits: u32 = (0..k)
            .map(|i| if z[i] == 1 { 1u32 << i } else { 0 })
            .sum::<u32>()
            + (0..k)
                .map(|i| if z[n - k + i] == 1 { 1u32 << (k + i) } else { 0 })
                .sum::<u32>();
        let known_w_bits: u32 = (0..k)
            .map(|i| if w[i] == 1 { 1u32 << i } else { 0 })
            .sum::<u32>()
            + (0..k)
                .map(|i| if w[m - k + i] == 1 { 1u32 << (k + i) } else { 0 })
                .sum::<u32>();
        // The split of `target` is into `xy_v + zw_v = target`.
        // The known XY contribution at very-high lags is xy_v_known.
        let xy_v_known: Vec<i32> = vh_lag_range(n, k)
            .map(|s| autocorr_bb(&x, s, k) + autocorr_bb(&y, s, k))
            .collect();
        let zw_v_known: Vec<i32> = vh_lag_range(n, k)
            .map(|s| {
                2 * autocorr_bb(&z, s, k)
                    + if s < m { 2 * autocorr_bb(&w, s, k) } else { 0 }
            })
            .collect();
        let known_pair_in_xy = t_xy
            .get(&xy_v_known)
            .map(|v| v.contains(&(known_x_bits, known_y_bits)))
            .unwrap_or(false);
        let known_pair_in_zw = t_zw
            .get(&zw_v_known)
            .map(|v| v.contains(&(known_z_bits, known_w_bits)))
            .unwrap_or(false);
        if known_pair_in_xy && known_pair_in_zw {
            eprintln!("PASS: known (X,Y) found at xy_v_known and (Z,W) found at zw_v_known");
        } else {
            eprintln!(
                "FAIL: known_pair_in_xy={}, known_pair_in_zw={}",
                known_pair_in_xy, known_pair_in_zw
            );
        }
        let sum_check: Vec<i32> = xy_v_known.iter().zip(&zw_v_known).map(|(a, b)| a + b).collect();
        eprintln!(
            "known xy_v + zw_v = {:?}  (target was {:?})  match={}",
            sum_check,
            target,
            sum_check == target
        );
    } else {
        eprintln!("\n(no known TT({}) solution available for sanity check)", n);
    }
}
