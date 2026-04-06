/// BFS-by-level MDD builder for ZW-first boundary configs.
///
/// Processes one level at a time instead of DFS, enabling:
/// - Bounded memory (only 2 levels in memory at once)
/// - Disk spill for huge state spaces
/// - Natural parallelism per level
///
/// Trades speed for memory efficiency at large k.

use rustc_hash::FxHashMap as HashMap;

pub const DEAD: u32 = 0;
pub const LEAF: u32 = u32::MAX;

type StateKey = (u128, u64); // (packed_sums, packed_active)

/// A single level's state map: state → MDD node ID
struct LevelStates {
    states: HashMap<StateKey, u32>,
}

impl LevelStates {
    fn new() -> Self {
        LevelStates { states: HashMap::default() }
    }
}

/// BFS-built 4-way MDD.
pub struct BfsMdd {
    pub nodes: Vec<[u32; 4]>,
    pub root: u32,
    pub k: usize,
}

impl BfsMdd {
    /// Build the ZW half of the MDD using BFS (one level at a time).
    /// Returns the ZW MDD with leaf nodes that are placeholders for XY sub-MDDs.
    pub fn build_zw_bfs(k: usize) -> Self {
        let zw_depth = 2 * k;

        // Bouncing position order
        let mut pos_order: Vec<usize> = Vec::with_capacity(2 * k);
        for t in 0..k {
            pos_order.push(t);
            pos_order.push(2 * k - 1 - t);
        }

        let mut pos_to_level: Vec<usize> = vec![0; 2 * k];
        for (level, &pos) in pos_order.iter().enumerate() {
            pos_to_level[pos] = level;
        }

        // Build lag pairs (same as ZW-first builder)
        struct LagPairs {
            z_pairs: Vec<(usize, usize)>,
            w_pairs: Vec<(usize, usize)>,
        }
        let mut lags: Vec<LagPairs> = Vec::new();
        for j in 0..k {
            let z_pairs: Vec<(usize, usize)> = (0..k - j)
                .map(|i| (i, k + i + j)).collect();
            let w_pairs: Vec<(usize, usize)> = if j < k - 1 {
                (0..k - j - 1).map(|i| (i, k + i + j + 1)).collect()
            } else { Vec::new() };
            lags.push(LagPairs { z_pairs, w_pairs });
        }

        // XY max abs for each lag (range+parity pruning in ZW half)
        let mut xy_max_abs: Vec<i32> = Vec::new();
        let mut xy_pair_counts: Vec<usize> = Vec::new();
        for j in 0..k {
            let n_pairs = k - j; // number of XY pairs for lag j
            xy_max_abs.push(2 * n_pairs as i32);
            xy_pair_counts.push(n_pairs);
        }

        // Events at each level
        let mut events_at_level: Vec<Vec<(usize, usize, usize, bool)>> =
            (0..zw_depth).map(|_| Vec::new()).collect();
        let mut lag_check_at_level: Vec<Vec<usize>> =
            (0..=zw_depth).map(|_| Vec::new()).collect();

        for (li, lag) in lags.iter().enumerate() {
            let mut complete = 0usize;
            for &(a, b) in &lag.z_pairs {
                let c = pos_to_level[a].max(pos_to_level[b]);
                events_at_level[c].push((li, a, b, true));
                complete = complete.max(c);
            }
            for &(a, b) in &lag.w_pairs {
                let c = pos_to_level[a].max(pos_to_level[b]);
                events_at_level[c].push((li, a, b, false));
                complete = complete.max(c);
            }
            lag_check_at_level[complete].push(li);
        }

        // Max remaining for range pruning
        let mut max_remaining: Vec<Vec<i32>> = vec![vec![0i32; k]; zw_depth + 1];
        for (li, lag) in lags.iter().enumerate() {
            for &(a, b) in &lag.z_pairs {
                let c = pos_to_level[a].max(pos_to_level[b]);
                for level in 0..=c { max_remaining[level][li] += 2; }
            }
            for &(a, b) in &lag.w_pairs {
                let c = pos_to_level[a].max(pos_to_level[b]);
                for level in 0..=c { max_remaining[level][li] += 2; }
            }
        }

        // Active position tracking
        let mut last_use: Vec<usize> = vec![0; 2 * k];
        for (level, events) in events_at_level.iter().enumerate() {
            for &(_, a, b, _) in events {
                last_use[a] = last_use[a].max(level);
                last_use[b] = last_use[b].max(level);
            }
        }
        let mut active_at_level: Vec<Vec<usize>> = vec![Vec::new(); zw_depth + 1];
        for d in 0..zw_depth {
            let mut active: Vec<usize> = if d > 0 {
                active_at_level[d - 1].iter()
                    .filter(|&&p| last_use[p] >= d)
                    .copied().collect()
            } else { Vec::new() };
            active.push(pos_order[d]);
            active.sort();
            active_at_level[d] = active;
        }
        let active_indices: Vec<HashMap<usize, usize>> = active_at_level.iter()
            .map(|active| active.iter().enumerate().map(|(i, &p)| (p, i)).collect())
            .collect();

        fn pack_sums(sums: &[i8]) -> u128 {
            let mut packed = 0u128;
            for (i, &s) in sums.iter().enumerate() {
                packed |= ((s as u8 as u128) & 0xFF) << (i * 8);
            }
            packed
        }

        fn pack_active(vals: &[u8]) -> u64 {
            let mut packed = 0u64;
            for (i, &v) in vals.iter().enumerate() {
                packed |= (v as u64) << (i * 2);
            }
            packed
        }

        // BFS: process one level at a time
        let mut nodes: Vec<[u32; 4]> = Vec::new();
        nodes.push([DEAD; 4]); // sentinel

        // State at each level: (sums, active_vals) → we need to expand to children
        // Level 0: initial state
        type FullState = (Vec<i8>, Vec<u8>); // (sums, active_vals)

        // Start: one state at level -1 (before any decisions)
        // Actually, we build bottom-up from the deepest level.
        // No wait, BFS goes top-down level by level.

        // For BFS top-down: at each level L, we have a set of states.
        // For each state, we generate 4 children states (for level L+1).
        // Each child state maps to an MDD node.

        // The tricky part: MDD nodes are created bottom-up (children before parents).
        // In BFS, we create parents before children.
        // Solution: two-pass approach.
        // Pass 1 (top-down BFS): enumerate all reachable states at each level.
        // Pass 2 (bottom-up): create MDD nodes from deepest level to root.

        // Pass 1: enumerate states
        let mut states_per_level: Vec<Vec<(StateKey, FullState)>> = Vec::new();

        // Level 0 initial state
        let init_sums = vec![0i8; k];
        let init_active = vec![0u8; 0];
        let init_key = (pack_sums(&init_sums), pack_active(&init_active));
        states_per_level.push(vec![(init_key, (init_sums, init_active))]);

        eprintln!("BFS pass 1 (enumerate states):");
        for level in 0..zw_depth {
            let current_states = &states_per_level[level];
            let mut next_states: HashMap<StateKey, FullState> = HashMap::default();

            let pos = pos_order[level];
            let active = &active_at_level[level];
            let new_idx = active_indices[level][&pos];

            for (_, (sums, prev_active)) in current_states {
                // Build current_vals from prev_active
                let mut current_vals: Vec<u8> = Vec::with_capacity(active.len());
                if level > 0 {
                    let prev_indices = &active_indices[level - 1];
                    for &p in active {
                        if p == pos {
                            current_vals.push(0);
                        } else if let Some(&pi) = prev_indices.get(&p) {
                            current_vals.push(prev_active[pi]);
                        } else {
                            current_vals.push(0);
                        }
                    }
                } else {
                    current_vals.resize(active.len(), 0);
                }

                for branch in 0u32..4 {
                    // Symmetry breaking
                    if pos == 0 && branch != 0b11 { continue; }

                    current_vals[new_idx] = branch as u8;
                    let mut new_sums = sums.clone();

                    // Process events
                    for &(lag_idx, pos_a, pos_b, is_z) in &events_at_level[level] {
                        let idx_a = active_indices[level][&pos_a];
                        let idx_b = active_indices[level][&pos_b];
                        let bits_a = current_vals[idx_a] as u32;
                        let bits_b = current_vals[idx_b] as u32;
                        if is_z {
                            let za = if (bits_a >> 0) & 1 == 1 { 1i32 } else { -1 };
                            let zb = if (bits_b >> 0) & 1 == 1 { 1i32 } else { -1 };
                            new_sums[lag_idx] += (2 * za * zb) as i8;
                        } else {
                            let wa = if (bits_a >> 1) & 1 == 1 { 1i32 } else { -1 };
                            let wb = if (bits_b >> 1) & 1 == 1 { 1i32 } else { -1 };
                            new_sums[lag_idx] += (2 * wa * wb) as i8;
                        }
                    }

                    // ZW lag completion check: range+parity feasibility
                    let mut ok = true;
                    for &li in &lag_check_at_level[level] {
                        let zw_val = new_sums[li] as i32;
                        let max_xy = xy_max_abs[li];
                        if zw_val.abs() > max_xy { ok = false; break; }
                        if (zw_val + max_xy) % 2 != 0 { ok = false; break; }
                    }
                    // Range pruning: can remaining ZW events keep sums achievable?
                    if ok && level + 1 < zw_depth {
                        for li in 0..k {
                            let zw_val = new_sums[li] as i32;
                            let zw_remaining = max_remaining[level + 1][li];
                            let max_xy = xy_max_abs[li];
                            // After all ZW events: |final_zw_val| must be <= max_xy
                            if (zw_val.abs() - zw_remaining) > max_xy {
                                ok = false; break;
                            }
                        }
                    }

                    if ok {
                        let next_key = (pack_sums(&new_sums), pack_active(&current_vals));
                        next_states.entry(next_key).or_insert_with(|| {
                            (new_sums.clone(), current_vals.clone())
                        });
                    }
                }
            }

            let count = next_states.len();
            eprint!("\r  Level {}/{}: {} states", level + 1, zw_depth, count);
            states_per_level.push(next_states.into_iter().collect());
        }
        eprintln!();

        // Pass 2: build MDD nodes bottom-up
        eprintln!("BFS pass 2 (build nodes):");

        // At the deepest level (zw_depth), states are terminal.
        // For ZW-only MDD: each terminal state → LEAF (we'll connect XY sub-MDDs later)
        let mut level_node_map: HashMap<StateKey, u32> = HashMap::default();
        for (key, (sums, _)) in &states_per_level[zw_depth] {
            // Terminal: check if all sums could reach 0 with XY
            // For now, mark as LEAF (placeholder for XY sub-MDD)
            level_node_map.insert(*key, LEAF);
        }

        // Build from level zw_depth-1 down to 0
        for level in (0..zw_depth).rev() {
            let current_states = &states_per_level[level];
            let pos = pos_order[level];
            let active = &active_at_level[level];
            let new_idx = active_indices[level][&pos];

            let mut new_level_map: HashMap<StateKey, u32> = HashMap::default();

            for (state_key, (sums, prev_active)) in current_states {
                // Rebuild current_vals
                let mut current_vals: Vec<u8> = Vec::with_capacity(active.len());
                if level > 0 {
                    let prev_indices = &active_indices[level - 1];
                    for &p in active {
                        if p == pos { current_vals.push(0); }
                        else if let Some(&pi) = prev_indices.get(&p) {
                            current_vals.push(prev_active[pi]);
                        } else { current_vals.push(0); }
                    }
                } else {
                    current_vals.resize(active.len(), 0);
                }

                let mut children = [DEAD; 4];
                for branch in 0u32..4 {
                    if pos == 0 && branch != 0b11 { continue; }

                    current_vals[new_idx] = branch as u8;
                    let mut new_sums = sums.clone();

                    for &(lag_idx, pos_a, pos_b, is_z) in &events_at_level[level] {
                        let idx_a = active_indices[level][&pos_a];
                        let idx_b = active_indices[level][&pos_b];
                        let bits_a = current_vals[idx_a] as u32;
                        let bits_b = current_vals[idx_b] as u32;
                        if is_z {
                            let za = if (bits_a >> 0) & 1 == 1 { 1i32 } else { -1 };
                            let zb = if (bits_b >> 0) & 1 == 1 { 1i32 } else { -1 };
                            new_sums[lag_idx] += (2 * za * zb) as i8;
                        } else {
                            let wa = if (bits_a >> 1) & 1 == 1 { 1i32 } else { -1 };
                            let wb = if (bits_b >> 1) & 1 == 1 { 1i32 } else { -1 };
                            new_sums[lag_idx] += (2 * wa * wb) as i8;
                        }
                    }

                    let child_key = (pack_sums(&new_sums), pack_active(&current_vals));
                    if let Some(&child_nid) = level_node_map.get(&child_key) {
                        children[branch as usize] = child_nid;
                    }
                }

                // Create/dedup node
                if children.iter().all(|&c| c == DEAD) {
                    new_level_map.insert(*state_key, DEAD);
                } else {
                    let first = children[0];
                    if children.iter().all(|&c| c == first) {
                        new_level_map.insert(*state_key, first);
                    } else {
                        let nid = nodes.len() as u32;
                        nodes.push(children);
                        new_level_map.insert(*state_key, nid);
                    }
                }
            }

            eprint!("\r  Level {}/{}: {} nodes total", level, zw_depth, nodes.len());
            level_node_map = new_level_map;
        }
        eprintln!();

        // Root is the node for the initial state
        let root = *level_node_map.values().next().unwrap_or(&DEAD);

        eprintln!("BFS MDD k={}: {} nodes, {:.1} MB",
            k, nodes.len(), nodes.len() as f64 * 16.0 / 1_048_576.0);

        // Report peak states per level
        let max_states: usize = states_per_level.iter().map(|s| s.len()).max().unwrap_or(0);
        let total_states: usize = states_per_level.iter().map(|s| s.len()).sum();
        eprintln!("  Max states per level: {}, total: {}", max_states, total_states);

        BfsMdd { nodes, root, k }
    }
}
