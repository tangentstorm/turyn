/// Build a 16-ary MDD for boundary configs using direct construction
/// with memoization on partial autocorrelation sums.
///
/// At each level (boundary position in bouncing order), branch on all 16
/// sign columns (x,y,z,w). Track partial sums for each lag constraint.
/// Two states with the same partial sum vector have identical subtrees
/// → memoize and share.
///
/// Node encoding:
///   0x0000 = DEAD (no valid completion)
///   0xFFFF = LEAF (valid)
///   other  = index into node table

use std::collections::HashMap;

const DEAD: u32 = 0;
const LEAF: u32 = u32::MAX; // 0xFFFFFFFF — virtual leaf, never stored in nodes[]

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(7);
    let depth = 2 * k;

    eprintln!("Building 16-ary MDD for k={} (valid for all n >= {})", k, 2 * k);

    // Bouncing position order
    let mut pos_order: Vec<usize> = Vec::with_capacity(depth);
    for t in 0..k {
        pos_order.push(t);
        pos_order.push(2 * k - 1 - t);
    }
    eprintln!("Position order: {:?}", pos_order);

    let mut pos_to_level: Vec<usize> = vec![0; depth];
    for (level, &pos) in pos_order.iter().enumerate() {
        pos_to_level[pos] = level;
    }

    // Build exact-lag bit pairs.
    // For lag j: XY pairs (i, k+i+j), Z pairs same, W pairs (i, k+i+j+1) if j<k-1
    struct LagPairs {
        // Each entry: (pos_a, pos_b, weight_x, weight_y, weight_z, weight_w)
        // weight is the coefficient in the constraint sum
        pairs: Vec<(usize, usize)>,
        w_pairs: Vec<(usize, usize)>,
    }
    let mut lags: Vec<LagPairs> = Vec::new();
    for j in 0..k {
        let pairs: Vec<(usize, usize)> = (0..k - j)
            .map(|i| (i, k + i + j)).collect();
        let w_pairs: Vec<(usize, usize)> = if j < k - 1 {
            (0..k - j - 1).map(|i| (i, k + i + j + 1)).collect()
        } else { Vec::new() };
        lags.push(LagPairs { pairs, w_pairs });
    }

    // For each pair, determine at which level it completes (both positions placed).
    // Group by completion level.
    struct PairEvent {
        pos_a: usize,
        pos_b: usize,
        lag_idx: usize,
        is_xyzw: bool,  // true = contributes N_X + N_Y + 2*N_Z; false = W only (2*N_W)
    }
    let mut events_at_level: Vec<Vec<PairEvent>> = (0..depth).map(|_| Vec::new()).collect();
    // Also track which lags complete at each level
    let mut lag_check_at_level: Vec<Vec<usize>> = (0..=depth).map(|_| Vec::new()).collect();

    for (li, lag) in lags.iter().enumerate() {
        let mut lag_complete_level = 0usize;
        for &(a, b) in &lag.pairs {
            let complete = pos_to_level[a].max(pos_to_level[b]);
            events_at_level[complete].push(PairEvent {
                pos_a: a, pos_b: b, lag_idx: li, is_xyzw: true,
            });
            lag_complete_level = lag_complete_level.max(complete);
        }
        for &(a, b) in &lag.w_pairs {
            let complete = pos_to_level[a].max(pos_to_level[b]);
            events_at_level[complete].push(PairEvent {
                pos_a: a, pos_b: b, lag_idx: li, is_xyzw: false,
            });
            lag_complete_level = lag_complete_level.max(complete);
        }
        lag_check_at_level[lag_complete_level].push(li);
    }

    for d in 0..depth {
        if !lag_check_at_level[d].is_empty() {
            eprintln!("  Lags completing at level {}: {:?}", d, lag_check_at_level[d]);
        }
    }

    // MDD nodes
    let mut nodes: Vec<[u32; 16]> = Vec::new();
    nodes.push([DEAD; 16]); // node 0 = DEAD

    let mut unique: HashMap<(u8, [u32; 16]), u32> = HashMap::new();

    // State for memoization: (level, partial_sums for each lag, pending_bits)
    // partial_sums: accumulated N_X+N_Y+2*N_Z+2*N_W from completed pairs for each lag
    // pending_bits: x,y,z,w values at positions that have been placed but whose
    //               pair partner hasn't been placed yet. We need these to compute
    //               the pair contribution when the partner is placed.
    //
    // Key insight: we only need the VALUES at positions involved in future pair events.
    // Pack: 4 bits per position. Max relevant pending positions at any level is bounded.
    //
    // Simpler: just track the 4-bit sign column at each placed position.
    // State = (level, partial_sums[k], placed_signs[level positions × 4 bits])
    //
    // But placed_signs grows with level — that's the problem.
    // HOWEVER: once both positions of ALL pairs involving a position are done,
    // that position's value is no longer needed. We can drop it from the state.
    //
    // For the bouncing order, positions are consumed in pairs: (0, 2k-1), (1, 2k-2), etc.
    // The pair events complete at the second position of each pair.
    // So the "pending" positions at any level are those placed but not yet fully consumed.

    // Let's figure out which positions' values are still needed at each level.
    let mut last_use_level: Vec<usize> = vec![0; depth]; // last level where pos's value is needed
    for events in &events_at_level {
        for ev in events {
            let la = pos_to_level[ev.pos_a];
            let lb = pos_to_level[ev.pos_b];
            last_use_level[ev.pos_a] = last_use_level[ev.pos_a].max(la.max(lb));
            last_use_level[ev.pos_b] = last_use_level[ev.pos_b].max(la.max(lb));
        }
    }

    // At each level, which positions are "active" (placed and still needed)?
    let mut active_at_level: Vec<Vec<usize>> = vec![Vec::new(); depth + 1];
    for d in 0..depth {
        // Start with previous active set
        let mut active: Vec<usize> = if d > 0 {
            active_at_level[d - 1].iter()
                .filter(|&&p| last_use_level[p] >= d)
                .copied().collect()
        } else {
            Vec::new()
        };
        // Add the position placed at this level
        active.push(pos_order[d]);
        active.sort();
        active_at_level[d] = active;
    }

    let max_active = active_at_level.iter().map(|a| a.len()).max().unwrap_or(0);
    eprintln!("\nMax active positions at any level: {}", max_active);
    for d in 0..depth {
        eprintln!("  Level {:2}: active {:?} ({} positions)", d, active_at_level[d], active_at_level[d].len());
    }

    // State: (partial_sums, active_bits).
    // partial_sums: [i8; k] — bounded by ±(2*k) per lag, fits in i8.
    // active_bits: 4 bits per active position. Max active ≈ k+2 or so.
    // Pack into a u64 or u128.
    //
    // For k=7: max active ~9 positions × 4 bits = 36 bits + 7 partial sums × ~5 bits ≈ 71 bits.
    // Use a small Vec<i8> for sums + u64 for active bits, packed into a hash key.

    // Memoize on (level, sums_hash, active_bits)
    // Actually, let's use a simple struct key.

    type StateKey = (Vec<i8>, u64); // (partial_sums, active_bits packed)

    let mut memo: Vec<HashMap<StateKey, u32>> = (0..=depth).map(|_| HashMap::new()).collect();

    // Map from position → index in active set at each level
    let active_indices: Vec<HashMap<usize, usize>> = active_at_level.iter()
        .map(|active| active.iter().enumerate().map(|(i, &p)| (p, i)).collect())
        .collect();

    fn pack_active(sign_cols: &[u8]) -> u64 {
        let mut packed = 0u64;
        for (i, &sc) in sign_cols.iter().enumerate() {
            packed |= (sc as u64) << (i * 4);
        }
        packed
    }

    // Build the MDD top-down with memoization.
    let mut stats_calls: u64 = 0;
    let mut stats_hits: u64 = 0;

    // Iterative-ish recursive build using an explicit function.
    // Returns node_id.
    struct Ctx {
        pos_order: Vec<usize>,
        events_at_level: Vec<Vec<(usize, usize, usize, bool)>>, // (pos_a, pos_b, lag_idx, is_xyzw)
        lag_check_at_level: Vec<Vec<usize>>,
        active_at_level: Vec<Vec<usize>>,
        active_indices: Vec<HashMap<usize, usize>>,
        depth: usize,
    }

    let ctx = Ctx {
        pos_order: pos_order.clone(),
        events_at_level: events_at_level.iter().map(|evs|
            evs.iter().map(|e| (e.pos_a, e.pos_b, e.lag_idx, e.is_xyzw)).collect()
        ).collect(),
        lag_check_at_level,
        active_at_level,
        active_indices,
        depth,
    };

    fn build(
        level: usize,
        sums: &mut Vec<i8>,
        active_bits: &mut Vec<u8>, // sign_col for each active position at prev level
        ctx: &Ctx,
        nodes: &mut Vec<[u32; 16]>,
        unique: &mut HashMap<(u8, [u32; 16]), u32>,
        memo: &mut Vec<HashMap<StateKey, u32>>,
        stats_calls: &mut u64,
        stats_hits: &mut u64,
    ) -> u32 {
        *stats_calls += 1;
        if *stats_calls % 1_000_000 == 0 {
            eprintln!("  [{:.1}M calls, {:.1}M hits, {} nodes]",
                *stats_calls as f64 / 1e6, *stats_hits as f64 / 1e6, nodes.len());
        }

        if level == ctx.depth {
            // All levels done. Check all lag sums = 0.
            if sums.iter().all(|&s| s == 0) { LEAF } else { DEAD }
        } else {
            // Build state key from current sums and active bits
            let active = &ctx.active_at_level[level];
            // Map previous active bits to current active positions
            // (drop positions no longer active, keep the rest)
            let mut current_active_vals: Vec<u8> = Vec::with_capacity(active.len());
            if level > 0 {
                let prev_indices = &ctx.active_indices[level - 1];
                for &pos in active {
                    if pos == ctx.pos_order[level] {
                        current_active_vals.push(0); // placeholder, will be set per branch
                    } else if let Some(&pi) = prev_indices.get(&pos) {
                        current_active_vals.push(active_bits[pi]);
                    } else {
                        current_active_vals.push(0);
                    }
                }
            } else {
                current_active_vals.resize(active.len(), 0);
            }

            // Index of the newly-placed position in current active set
            let new_pos = ctx.pos_order[level];
            let new_idx = ctx.active_indices[level][&new_pos];

            let state_key = (sums.clone(), pack_active(&current_active_vals));
            if let Some(&cached) = memo[level].get(&state_key) {
                *stats_hits += 1;
                return cached;
            }

            let mut children = [DEAD; 16];
            for sign_col in 0u32..16 {
                // Symmetry breaking: position 0 must be all +1
                if new_pos == 0 && sign_col != 0b1111 { continue; }

                // Set the new position's value
                current_active_vals[new_idx] = sign_col as u8;

                // Process pair events completing at this level
                let sums_backup: Vec<i8> = sums.clone();
                let events = &ctx.events_at_level[level];
                for &(pos_a, pos_b, lag_idx, is_xyzw) in events {
                    let idx_a = ctx.active_indices[level][&pos_a];
                    let idx_b = ctx.active_indices[level][&pos_b];
                    let bits_a = current_active_vals[idx_a] as u32;
                    let bits_b = current_active_vals[idx_b] as u32;

                    if is_xyzw {
                        // X contribution: x_a * x_b
                        let xa: i32 = if (bits_a >> 0) & 1 == 1 { 1 } else { -1 };
                        let xb: i32 = if (bits_b >> 0) & 1 == 1 { 1 } else { -1 };
                        let ya: i32 = if (bits_a >> 1) & 1 == 1 { 1 } else { -1 };
                        let yb: i32 = if (bits_b >> 1) & 1 == 1 { 1 } else { -1 };
                        let za: i32 = if (bits_a >> 2) & 1 == 1 { 1 } else { -1 };
                        let zb: i32 = if (bits_b >> 2) & 1 == 1 { 1 } else { -1 };
                        // N_X + N_Y + 2*N_Z
                        sums[lag_idx] += (xa * xb + ya * yb + 2 * za * zb) as i8;
                    } else {
                        // W only: 2*N_W
                        let wa: i32 = if (bits_a >> 3) & 1 == 1 { 1 } else { -1 };
                        let wb: i32 = if (bits_b >> 3) & 1 == 1 { 1 } else { -1 };
                        sums[lag_idx] += (2 * wa * wb) as i8;
                    }
                }

                // Check if any completed lags are violated
                let mut ok = true;
                for &li in &ctx.lag_check_at_level[level] {
                    if sums[li] != 0 { ok = false; break; }
                }

                if ok {
                    children[sign_col as usize] = build(
                        level + 1, sums, &mut current_active_vals,
                        ctx, nodes, unique, memo, stats_calls, stats_hits,
                    );
                }

                // Restore sums
                sums.copy_from_slice(&sums_backup);
            }

            let result = if children.iter().all(|&c| c == DEAD) {
                DEAD
            } else {
                let first = children[0];
                if children.iter().all(|&c| c == first) {
                    first
                } else {
                    let key = (level as u8, children);
                    if let Some(&nid) = unique.get(&key) { nid }
                    else {
                        let nid = nodes.len() as u32;
                        assert!(nid < LEAF);
                        nodes.push(children);
                        unique.insert(key, nid);
                        nid
                    }
                }
            };

            memo[level].insert(state_key, result);
            result
        }
    }

    let mut sums = vec![0i8; k];
    let mut active_bits: Vec<u8> = Vec::new();
    let root = build(
        0, &mut sums, &mut active_bits,
        &ctx, &mut nodes, &mut unique, &mut memo,
        &mut stats_calls, &mut stats_hits,
    );

    // Stats
    let node_count = nodes.len();
    let trie_bytes = node_count * 16 * 4;
    let leaf_count = count_paths(root, &nodes);
    let memo_entries: usize = memo.iter().map(|m| m.len()).sum();

    eprintln!("\n=== MDD stats (k={}) ===", k);
    eprintln!("  Nodes: {}", node_count);
    eprintln!("  Memo entries: {}", memo_entries);
    eprintln!("  DFS calls: {} ({} hits)", stats_calls, stats_hits);
    eprintln!("  Valid 4-tuple boundary configs: {}", leaf_count);
    eprintln!("  MDD size: {} bytes ({:.2} MB)", trie_bytes, trie_bytes as f64 / 1_048_576.0);
    if k == 7 {
        eprintln!("  Current table size: 1923.1 MB");
        if trie_bytes > 0 {
            eprintln!("  Compression ratio: {:.0}x", 1_923.1 * 1_048_576.0 / trie_bytes as f64);
        }
    }

    // BFS depth breakdown
    eprintln!("\n  Depth breakdown:");
    let mut current_level_nodes: Vec<u32> = vec![root];
    for d in 0..depth {
        eprintln!("    depth {:2} (pos {:2}): {} unique nodes", d, pos_order[d], current_level_nodes.len());
        let mut next = std::collections::HashSet::new();
        for &nid in &current_level_nodes {
            if nid == DEAD || nid == LEAF { continue; }
            if (nid as usize) < nodes.len() {
                for &child in &nodes[nid as usize] {
                    if child != DEAD { next.insert(child); }
                }
            }
        }
        current_level_nodes = next.into_iter().collect();
    }
    eprintln!("    depth {:2} (leaf): {}", depth, current_level_nodes.len());
}

fn count_paths(root: u32, nodes: &[[u32; 16]]) -> u128 {
    let mut memo: HashMap<u32, u128> = HashMap::new();
    fn count(nid: u32, nodes: &[[u32; 16]], memo: &mut HashMap<u32, u128>) -> u128 {
        if nid == DEAD { return 0; }
        if nid == LEAF { return 1; }
        if let Some(&c) = memo.get(&nid) { return c; }
        let total: u128 = nodes[nid as usize].iter()
            .map(|&child| count(child, nodes, memo)).sum();
        memo.insert(nid, total);
        total
    }
    count(root, nodes, &mut memo)
}
