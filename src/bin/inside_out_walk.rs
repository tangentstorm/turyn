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

use rayon::prelude::*;
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

/// Bit-reverse the low `k` bits of `x`. Bits k..32 are zeroed.
fn reverse_k_bits(x: u32, k: usize) -> u32 {
    let mut r = 0u32;
    for i in 0..k {
        if (x >> i) & 1 == 1 {
            r |= 1u32 << (k - 1 - i);
        }
    }
    r
}

/// Reversal of a 2k-bit boundary representation. The full sequence
/// reversal `seq[i] -> seq[n-1-i]` corresponds, for the boundary
/// (low_0..low_{k-1}, high_0..high_{k-1}), to swapping the two
/// halves AND bit-reversing each.
fn reverse_bd(bits: u32, k: usize) -> u32 {
    let mask = (1u32 << k) - 1;
    let low = bits & mask;
    let high = (bits >> k) & mask;
    reverse_k_bits(high, k) | (reverse_k_bits(low, k) << k)
}

/// True iff this boundary is the canonical (lex-min) representative
/// under T1 (sequence reversal). Equivalent boundaries `bd` and
/// `reverse_bd(bd, k)` produce the same bb-vector at every lag, so
/// dropping the larger-keyed one is a 2× pruning per sequence.
fn is_t1_canonical(bits: u32, k: usize) -> bool {
    bits <= reverse_bd(bits, k)
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

/// Build boundary index `T_xy[v]` keyed on very-high-lag
/// `bb_X + bb_Y` (length k vector). Canonicalises every per-sequence
/// T1 (reversal) and T2 (sign flip):
/// - T2: `X[0] = +1`, `Y[0] = +1` (bit 0 set in low half)
/// - T1: `bd_X ≤ reverse(bd_X)`, `bd_Y ≤ reverse(bd_Y)`
///
/// Each gives 2× pruning per sequence; 16× total reduction of the
/// XY-pair index.
fn build_xy_table(k: usize, n: usize) -> HashMap<Vec<i32>, Vec<(u32, u32)>> {
    let mut t: HashMap<Vec<i32>, Vec<(u32, u32)>> = HashMap::new();
    let bd_count = 1u64 << (2 * k);
    let vh = vh_lag_range(n, k);
    for x_bits in 0..bd_count {
        let xb_u32 = x_bits as u32;
        if (x_bits & 1) == 0 {
            continue;
        }
        if !is_t1_canonical(xb_u32, k) {
            continue;
        }
        let xb = make_bd(n, xb_u32, k);
        for y_bits in 0..bd_count {
            let yb_u32 = y_bits as u32;
            if (y_bits & 1) == 0 {
                continue;
            }
            if !is_t1_canonical(yb_u32, k) {
                continue;
            }
            let yb = make_bd(n, yb_u32, k);
            let key: Vec<i32> = vh
                .clone()
                .map(|s| autocorr_bb(&xb, s, k) + autocorr_bb(&yb, s, k))
                .collect();
            t.entry(key).or_default().push((xb_u32, yb_u32));
        }
    }
    t
}

/// Build boundary index `T_zw[v]` keyed on very-high-lag
/// `2*bb_Z + 2*bb_W`. Canonicalised under T1+T2 for both Z and W.
fn build_zw_table(k: usize, n: usize) -> HashMap<Vec<i32>, Vec<(u32, u32)>> {
    let mut t: HashMap<Vec<i32>, Vec<(u32, u32)>> = HashMap::new();
    let m = n - 1;
    let bd_count = 1u64 << (2 * k);
    let vh = vh_lag_range(n, k);
    for z_bits in 0..bd_count {
        let zb_u32 = z_bits as u32;
        if (z_bits & 1) == 0 {
            continue;
        }
        if !is_t1_canonical(zb_u32, k) {
            continue;
        }
        let zb = make_bd(n, zb_u32, k);
        for w_bits in 0..bd_count {
            let wb_u32 = w_bits as u32;
            if (w_bits & 1) == 0 {
                continue;
            }
            if !is_t1_canonical(wb_u32, k) {
                continue;
            }
            let wb = make_bd(m, wb_u32, k);
            let key: Vec<i32> = vh
                .clone()
                .map(|s| {
                    let bz = 2 * autocorr_bb(&zb, s, k);
                    let bw = if s < m { 2 * autocorr_bb(&wb, s, k) } else { 0 };
                    bz + bw
                })
                .collect();
            t.entry(key).or_default().push((zb_u32, wb_u32));
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

/// Count of mm-pairs at lag s that are still UNPLACED in the partial
/// middle. For each sequence: number of pairs (i, j=i+s) in middle
/// where at least one of i, j is currently unset (= 0 in `state.seqs`).
/// Bound: each unplaced pair can contribute ±1 to mm[s] for that
/// sequence (so ±weight to Turyn-weighted total).
fn future_mm_bound(state: &WalkerState, n: usize, k: usize, s: usize) -> i32 {
    let mut bound = 0i32;
    for seq_i in 0..4 {
        let weight = if seq_i < 2 { 1 } else { 2 };
        let seq_len = if seq_i == 3 { n - 1 } else { n };
        let mid_lo = k;
        let mid_hi = seq_len - k;
        if mid_lo + s >= mid_hi {
            continue;
        }
        let mut unplaced = 0i32;
        for i in mid_lo..(mid_hi - s) {
            if state.seqs[seq_i][i] == 0 || state.seqs[seq_i][i + s] == 0 {
                unplaced += 1;
            }
        }
        bound += weight * unplaced;
    }
    bound
}

/// Maximum |bb[s] + cross[s]| achievable across all 4-sequence
/// boundary tuples at lag `s` (Turyn-weighted). bb pairs are
/// `(i, j=i+s)` with both endpoints in boundary; cross are pairs
/// straddling boundary/middle. Each pair contributes ±1; the bound
/// is the count of pairs times the Turyn weight.
fn bd_capacity_at_lag(n: usize, k: usize, s: usize) -> i32 {
    let mut cap = 0i32;
    for seq_i in 0..4 {
        let weight = if seq_i < 2 { 1 } else { 2 };
        let seq_len = if seq_i == 3 { n - 1 } else { n };
        let mid_lo = k;
        let mid_hi = seq_len - k;
        // bb pairs: i in low-bd [0..k), j=i+s in high-bd [seq_len-k..seq_len)
        let mut bb_pairs = 0i32;
        for i in 0..k {
            let j = i + s;
            if j >= seq_len {
                break;
            }
            if (j >= mid_hi) || (j < k && i < k) {
                // both in boundary
                bb_pairs += 1;
            }
        }
        // cross pairs: straddle bd/mid
        let mut cross_pairs = 0i32;
        if s < seq_len {
            for i in 0..(seq_len - s) {
                let j = i + s;
                let i_bd = i < k || i >= mid_hi;
                let i_mid = i >= mid_lo && i < mid_hi;
                let j_bd = j < k || j >= mid_hi;
                let j_mid = j >= mid_lo && j < mid_hi;
                if (i_bd && j_mid) || (i_mid && j_bd) {
                    cross_pairs += 1;
                }
            }
        }
        cap += weight * (bb_pairs + cross_pairs);
    }
    cap
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

/// Bit-packed sequence: bit i = 0 means -1, bit i = 1 means +1.
/// Valid for sequence length ≤ 64.
type PackedSeq = u64;

/// Convert a `Vec<i32>` of ±1 (and possibly 0 for unset) to a
/// PackedSeq. Treats 0 as +1 so unset positions don't influence
/// autocorrelation in a hard-to-debug way; callers should only pass
/// fully-placed sequences.
fn pack_seq(seq: &[i32]) -> PackedSeq {
    debug_assert!(seq.len() <= 64);
    let mut bits = 0u64;
    for (i, &v) in seq.iter().enumerate() {
        if v == 1 {
            bits |= 1u64 << i;
        }
    }
    bits
}

/// Bit-packed autocorrelation at lag `s` for sequence of length
/// `len` packed into low `len` bits of `seq` (bit i = ±1).
///
/// Σ_{i=0..len-s} seq_value(i) · seq_value(i+s)
///
/// where seq_value(i) = 2*bit(i) - 1 ∈ {-1, +1}.
///
/// The product seq_value(i)·seq_value(i+s) = +1 iff bits agree,
/// -1 iff disagree. So:
///   sum = (#agree) - (#disagree)
///       = (len - s) - 2 * (#disagree)
///       = (len - s) - 2 * popcount((seq XOR (seq>>s)) & mask)
///
/// where mask is the low (len - s) bits.
#[inline]
fn autocorr_packed(seq: PackedSeq, len: usize, s: usize) -> i32 {
    if s >= len {
        return 0;
    }
    let nvalid = len - s;
    let mask = if nvalid >= 64 { !0u64 } else { (1u64 << nvalid) - 1 };
    let xor = seq ^ (seq >> s);
    let diffs = (xor & mask).count_ones() as i32;
    (nvalid as i32) - 2 * diffs
}

/// Bit-packed full Turyn check.
fn verify_full_turyn_packed(
    state_packed: &LeafPacked,
    n: usize,
    k: usize,
    bx_bits: u32,
    by_bits: u32,
    bz_bits: u32,
    bw_bits: u32,
) -> bool {
    let m = n - 1;
    // Boundary mask for length-n sequences (bits in [0..k) ∪ [n-k..n)).
    let bd_mask_n = state_packed.bd_mask_n;
    let bd_mask_m = state_packed.bd_mask_m;

    // Build full packed seqs: middle (from state_packed) | boundary (from bits).
    // bx_bits/by_bits/bz_bits has the low-k bits in positions [0..k) and the
    // high-k bits in positions [k..2k). They map to sequence positions
    // [0..k) and [n-k..n) respectively.
    let bx_low = (bx_bits as u64) & ((1u64 << k) - 1);
    let bx_high = ((bx_bits >> k) as u64) & ((1u64 << k) - 1);
    let bx_full = bx_low | (bx_high << (n - k));
    let by_low = (by_bits as u64) & ((1u64 << k) - 1);
    let by_high = ((by_bits >> k) as u64) & ((1u64 << k) - 1);
    let by_full = by_low | (by_high << (n - k));
    let bz_low = (bz_bits as u64) & ((1u64 << k) - 1);
    let bz_high = ((bz_bits >> k) as u64) & ((1u64 << k) - 1);
    let bz_full = bz_low | (bz_high << (n - k));
    let bw_low = (bw_bits as u64) & ((1u64 << k) - 1);
    let bw_high = ((bw_bits >> k) as u64) & ((1u64 << k) - 1);
    let bw_full = bw_low | (bw_high << (m - k));

    let sx = (state_packed.mid_x & !bd_mask_n) | bx_full;
    let sy = (state_packed.mid_y & !bd_mask_n) | by_full;
    let sz = (state_packed.mid_z & !bd_mask_n) | bz_full;
    let sw = (state_packed.mid_w & !bd_mask_m) | bw_full;

    for s in 1..n {
        let ax = autocorr_packed(sx, n, s);
        let ay = autocorr_packed(sy, n, s);
        let az = autocorr_packed(sz, n, s);
        let aw = if s < m { autocorr_packed(sw, m, s) } else { 0 };
        if ax + ay + 2 * az + 2 * aw != 0 {
            return false;
        }
    }
    true
}

/// Per-leaf packed state, computed once at the leaf and reused across
/// all candidate boundary tuples.
struct LeafPacked {
    mid_x: PackedSeq,
    mid_y: PackedSeq,
    mid_z: PackedSeq,
    mid_w: PackedSeq,
    bd_mask_n: u64, // low-k + high-k bits set, length-n
    bd_mask_m: u64, // low-k + high-k bits set, length-m
}

impl LeafPacked {
    fn from_state(state: &WalkerState, n: usize, k: usize) -> Self {
        let m = n - 1;
        let bd_mask_n =
            ((1u64 << k) - 1) | (((1u64 << k) - 1) << (n - k));
        let bd_mask_m =
            ((1u64 << k) - 1) | (((1u64 << k) - 1) << (m - k));
        Self {
            mid_x: pack_seq(&state.seqs[0]),
            mid_y: pack_seq(&state.seqs[1]),
            mid_z: pack_seq(&state.seqs[2]),
            mid_w: pack_seq(&state.seqs[3]),
            bd_mask_n,
            bd_mask_m,
        }
    }
}

/// At a leaf, exhaustively check every (B_X, B_Y, B_Z, B_W)
/// 4-tuple that passes the very-high-lag pre-filter. Returns
/// (pre_filter_count, exact_solution_count). Uses bit-packed
/// autocorrelation for speed (n ≤ 64 only).
fn leaf_full_check(
    state: &WalkerState,
    n: usize,
    k: usize,
    target: &[i32],
    t_xy: &HashMap<Vec<i32>, Vec<(u32, u32)>>,
    t_zw: &HashMap<Vec<i32>, Vec<(u32, u32)>>,
    _bufs: &mut LeafBufs,
) -> (u64, u64) {
    let leaf = LeafPacked::from_state(state, n, k);
    let mut pre_filter = 0u64;
    let mut exact = 0u64;
    for (zw_v, zw_pairs) in t_zw {
        let xy_target: Vec<i32> = target.iter().zip(zw_v).map(|(a, b)| a - b).collect();
        let xy_pairs = match t_xy.get(&xy_target) {
            Some(p) => p,
            None => continue,
        };
        for &(bx, by) in xy_pairs {
            for &(bz, bw) in zw_pairs {
                pre_filter += 1;
                if verify_full_turyn_packed(&leaf, n, k, bx, by, bz, bw) {
                    exact += 1;
                }
            }
        }
    }
    (pre_filter, exact)
}

/// Reusable per-leaf scratch buffers for `verify_full_turyn_into`.
struct LeafBufs {
    sx: Vec<i32>,
    sy: Vec<i32>,
    sz: Vec<i32>,
    sw: Vec<i32>,
}

impl LeafBufs {
    fn new(n: usize) -> Self {
        Self {
            sx: Vec::with_capacity(n),
            sy: Vec::with_capacity(n),
            sz: Vec::with_capacity(n),
            sw: Vec::with_capacity(n),
        }
    }
}

/// Recursive inside-out walk. Returns a tuple of
/// (leaves_visited, leaves_with_pre_match, leaves_with_exact_match, total_pre, total_exact).
fn walk(
    state: &mut WalkerState,
    n: usize,
    k: usize,
    nlev: usize,
    target_to_count: &HashMap<Vec<i32>, u64>,
    pruned_out: &mut u64,
    full_check: bool,
    t_xy: &HashMap<Vec<i32>, Vec<(u32, u32)>>,
    t_zw: &HashMap<Vec<i32>, Vec<(u32, u32)>>,
    bufs: &mut LeafBufs,
) -> (u64, u64, u64, u64, u64) {
    // Leaf?
    if state.level >= nlev {
        let target = vh_lag_target_from_leaf(state, n, k);
        let total_cand = target_to_count.get(&target).copied().unwrap_or(0);
        let exact = if full_check && total_cand > 0 {
            leaf_full_check(state, n, k, &target, t_xy, t_zw, bufs).1
        } else {
            0
        };
        let leaves_pre = if total_cand > 0 { 1 } else { 0 };
        let leaves_exact = if exact > 0 { 1 } else { 0 };
        return (1, leaves_pre, leaves_exact, total_cand, exact);
    }

    // Pruning: can the current mm_sum still land within the
    // boundary's compensation capacity at every lag?
    //
    // Constraint per lag s:  mm[s] + bb[s] + cross[s] = 0  ==>
    //   mm_total_at_leaf[s]  =  -(bb + cross)
    //   |mm_total_at_leaf[s]| ≤ bd_capacity[s]
    //
    // At the current node (depth d), partial_mm[s] is fixed; future
    // mm contribution can swing total mm by at most ± future_bound[s].
    //
    // Prune if  |partial_mm[s]| - future_bound[s] > bd_capacity[s].
    for s in 1..n {
        let future_bound = future_mm_bound(state, n, k, s);
        let bd_cap = bd_capacity_at_lag(n, k, s);
        if state.mm_sum[s - 1].abs() - future_bound > bd_cap {
            *pruned_out += 1;
            return (0, 0, 0, 0, 0);
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
    let mut total_match_exact = 0u64;
    let mut total_cand = 0u64;
    let mut total_exact = 0u64;

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

        let (v, lp, le, tp, te) = walk(
            state,
            n,
            k,
            nlev,
            target_to_count,
            pruned_out,
            full_check,
            t_xy,
            t_zw,
            bufs,
        );
        total_visited += v;
        total_match += lp;
        total_match_exact += le;
        total_cand += tp;
        total_exact += te;

        state.level -= 1;
        state.mm_sum = saved_mm;
    }

    (total_visited, total_match, total_match_exact, total_cand, total_exact)
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

    // Decide whether to do per-leaf full Turyn check during the walk.
    // Only feasible at small n (per-leaf cost is O(pre_filter * n)).
    let full_check_during_walk = std::env::var("FULL_CHECK").is_ok();
    if full_check_during_walk {
        eprintln!("(FULL_CHECK=1: running full Turyn check at every leaf — slow at larger scales)");
    }

    // Parallelise the level-0 branch fan-out: there are 256 children
    // at level 0 (one for each 8-bit assignment to the 4 sequences x
    // 2 positions). Dispatch each as a separate rayon task. Each
    // task gets its own walker state + buffers + counters; we
    // sum-reduce at the end. Top-level parallelism only — within
    // each branch the recursion is sequential.
    let t_walk = std::time::Instant::now();
    let (lo0, hi0) = pair_positions(0, n, k);
    let n_bits_per_seq_l0 = match (lo0, hi0) {
        (Some(_), Some(_)) => 2,
        (Some(_), None) => 1,
        (None, _) => unreachable!(),
    };
    let n_branches_l0 = 1u32 << (4 * n_bits_per_seq_l0);

    let level0_state = state.clone();
    let aggregate: (u64, u64, u64, u64, u64, u64) = (0..n_branches_l0)
        .into_par_iter()
        .map(|branch| {
            let mut local_state = level0_state.clone();
            let mut local_pruned = 0u64;
            let mut local_bufs = LeafBufs::new(n);
            // Apply this level-0 branch's bits to local_state.
            for seq_i in 0..4 {
                let bits = (branch >> (seq_i * n_bits_per_seq_l0))
                    & ((1u32 << n_bits_per_seq_l0) - 1);
                let val_lo = if (bits & 1) == 1 { 1i32 } else { -1 };
                let val_hi = if n_bits_per_seq_l0 > 1 && ((bits >> 1) & 1) == 1 {
                    1i32
                } else {
                    -1i32
                };
                let seq_len = if seq_i == 3 { n - 1 } else { n };
                if let Some(p_lo) = lo0 {
                    if p_lo < seq_len {
                        local_state.seqs[seq_i][p_lo] = val_lo;
                    }
                }
                if n_bits_per_seq_l0 > 1 {
                    if let Some(p_hi) = hi0 {
                        if p_hi < seq_len {
                            local_state.seqs[seq_i][p_hi] = val_hi;
                        }
                    }
                }
            }
            // Recompute mm_sum from scratch (matches what `walk` does).
            let mut new_mm = vec![0i32; n - 1];
            for s in 1..n {
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
                        sum += local_state.seqs[seq_i][i] * local_state.seqs[seq_i][i + s];
                    }
                    new_mm[s - 1] += weight * sum;
                }
            }
            local_state.mm_sum = new_mm;
            local_state.level = 1;
            // Recurse on remaining levels.
            let (v, lp, le, tp, te) = walk(
                &mut local_state,
                n,
                k,
                nlev,
                &target_to_count,
                &mut local_pruned,
                full_check_during_walk,
                &t_xy,
                &t_zw,
                &mut local_bufs,
            );
            (v, lp, le, tp, te, local_pruned)
        })
        .reduce(
            || (0, 0, 0, 0, 0, 0),
            |(a1, a2, a3, a4, a5, a6), (b1, b2, b3, b4, b5, b6)| {
                (a1 + b1, a2 + b2, a3 + b3, a4 + b4, a5 + b5, a6 + b6)
            },
        );
    let (visited, matched, matched_exact, cand, exact, pruned) = aggregate;
    let walk_secs = t_walk.elapsed().as_secs_f64();
    let _ = state; // suppress unused warning

    eprintln!("\n=== Walker results ===");
    eprintln!("leaves visited        = {}", visited);
    eprintln!("leaves with pre-match = {}", matched);
    eprintln!("total pre candidates  = {}", cand);
    eprintln!(
        "avg pre candidates/leaf = {:.2}",
        if visited > 0 {
            cand as f64 / visited as f64
        } else {
            0.0
        }
    );
    if full_check_during_walk {
        eprintln!("leaves with exact (full Turyn) = {}", matched_exact);
        eprintln!("total exact survivors = {}", exact);
        eprintln!(
            "pre-filter overhead   = {:.0}x (pre / exact)",
            if exact > 0 { cand as f64 / exact as f64 } else { 0.0 }
        );
    }
    eprintln!("subtree prunes        = {}", pruned);
    eprintln!("walk time             = {:.2}s", walk_secs);
    eprintln!(
        "naive  total leaves   = {} (256^{})",
        256u128.pow(nlev as u32),
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
        eprintln!("boundary candidates at known leaf (vh-bb pre-filter) = {}", hits);

        // Stage 4 demo: at the known leaf, exhaustively run the full
        // Turyn check on every pre-filtered candidate and report the
        // exact survivor count.
        let t_full = std::time::Instant::now();
        let mut sanity_bufs = LeafBufs::new(n);
        let (pre_filter, exact) =
            leaf_full_check(&known_state, n, k, &target, &t_xy, &t_zw, &mut sanity_bufs);
        eprintln!(
            "Stage-4 full check at known leaf:  {} pre-filter -> {} pass full Turyn  ({:.2}s)",
            pre_filter,
            exact,
            t_full.elapsed().as_secs_f64()
        );
        if exact > 0 {
            eprintln!("  Filter ratio at known leaf: {:.0}x reduction (vh-bb -> full Turyn)",
                pre_filter as f64 / exact as f64);
        }
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
