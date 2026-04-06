/// BFS-by-level MDD builder with disk-backed state storage (redb).
///
/// Processes one level at a time:
/// - Pass 1: enumerate reachable states top-down, store each level to redb
/// - Pass 2: build MDD nodes bottom-up, reading states from redb
///
/// Memory usage: O(max_states_per_level) instead of O(total_states).
/// Disk usage: O(total_states) via redb.

use rustc_hash::FxHashMap as HashMap;
use redb::{ReadableTable, ReadableDatabase};

pub const DEAD: u32 = 0;
pub const LEAF: u32 = u32::MAX;

/// Packed state: 24 bytes (u128 sums + u64 active).
/// Stored as [u8; 24] in redb.
fn pack_state(sums: &[i8], active: &[u8]) -> [u8; 24] {
    let mut buf = [0u8; 24];
    let s = pack_sums(sums);
    buf[0..16].copy_from_slice(&s.to_le_bytes());
    let a = pack_active(active);
    buf[16..24].copy_from_slice(&a.to_le_bytes());
    buf
}

fn unpack_sums(buf: &[u8; 24], k: usize) -> Vec<i8> {
    let packed = u128::from_le_bytes(buf[0..16].try_into().unwrap());
    (0..k).map(|i| ((packed >> (i * 8)) & 0xFF) as i8).collect()
}

fn unpack_active(buf: &[u8; 24], n: usize) -> Vec<u8> {
    let packed = u64::from_le_bytes(buf[16..24].try_into().unwrap());
    (0..n).map(|i| ((packed >> (i * 2)) & 3) as u8).collect()
}

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

/// BFS-built 4-way MDD.
pub struct BfsMdd {
    pub nodes: Vec<[u32; 4]>,
    pub root: u32,
    pub k: usize,
}

impl BfsMdd {
    /// Build the ZW half using BFS with redb disk backing.
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

        // Lag pairs
        let mut z_pairs_per_lag: Vec<Vec<(usize, usize)>> = Vec::new();
        let mut w_pairs_per_lag: Vec<Vec<(usize, usize)>> = Vec::new();
        let mut xy_max_abs: Vec<i32> = Vec::new();
        for j in 0..k {
            let zp: Vec<(usize, usize)> = (0..k-j).map(|i| (i, k+i+j)).collect();
            let wp: Vec<(usize, usize)> = if j < k-1 {
                (0..k-j-1).map(|i| (i, k+i+j+1)).collect()
            } else { Vec::new() };
            xy_max_abs.push(2 * zp.len() as i32);
            z_pairs_per_lag.push(zp);
            w_pairs_per_lag.push(wp);
        }

        // Events + lag checks at each level
        let mut events_at_level: Vec<Vec<(usize, usize, usize, bool)>> =
            (0..zw_depth).map(|_| Vec::new()).collect();
        let mut lag_check_at_level: Vec<Vec<usize>> =
            (0..=zw_depth).map(|_| Vec::new()).collect();
        for (li, (zp, wp)) in z_pairs_per_lag.iter().zip(w_pairs_per_lag.iter()).enumerate() {
            let mut complete = 0;
            for &(a, b) in zp {
                let c = pos_to_level[a].max(pos_to_level[b]);
                events_at_level[c].push((li, a, b, true));
                complete = complete.max(c);
            }
            for &(a, b) in wp {
                let c = pos_to_level[a].max(pos_to_level[b]);
                events_at_level[c].push((li, a, b, false));
                complete = complete.max(c);
            }
            lag_check_at_level[complete].push(li);
        }

        // Max remaining for range pruning
        let mut max_remaining: Vec<Vec<i32>> = vec![vec![0i32; k]; zw_depth + 1];
        for (li, (zp, wp)) in z_pairs_per_lag.iter().zip(w_pairs_per_lag.iter()).enumerate() {
            for &(a, b) in zp {
                let c = pos_to_level[a].max(pos_to_level[b]);
                for lv in 0..=c { max_remaining[lv][li] += 2; }
            }
            for &(a, b) in wp {
                let c = pos_to_level[a].max(pos_to_level[b]);
                for lv in 0..=c { max_remaining[lv][li] += 2; }
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
                active_at_level[d-1].iter().filter(|&&p| last_use[p] >= d).copied().collect()
            } else { Vec::new() };
            active.push(pos_order[d]);
            active.sort();
            active_at_level[d] = active;
        }
        let active_indices: Vec<HashMap<usize, usize>> = active_at_level.iter()
            .map(|a| a.iter().enumerate().map(|(i, &p)| (p, i)).collect()).collect();

        // Open redb database for level storage
        let db_path = format!("/tmp/mdd_bfs_k{}.redb", k);
        let _ = std::fs::remove_file(&db_path); // clean start
        let db = redb::Database::create(&db_path).expect("Failed to create redb");

        // Define table for each level: key=[u8;24] (packed state), value=[u8] (serialized FullState)
        // For simplicity, store FullState as (sums bytes, active bytes) concatenated.

        eprintln!("BFS pass 1 (enumerate states → redb):");
        let start = std::time::Instant::now();

        // We process one level at a time. Current level states are in memory,
        // then written to redb before moving to the next level.
        // We also need prev level states to compute current active_vals.

        // Level states: HashMap<[u8;24], Vec<u8>> where key=packed_state, value=serialized_full_state
        let mut prev_states: HashMap<[u8; 24], (Vec<i8>, Vec<u8>)> = HashMap::default();
        let init_key = pack_state(&vec![0i8; k], &vec![]);
        prev_states.insert(init_key, (vec![0i8; k], vec![]));

        let mut level_state_counts: Vec<usize> = Vec::new();
        level_state_counts.push(1);

        for level in 0..zw_depth {
            let pos = pos_order[level];
            let active = &active_at_level[level];
            let new_idx = active_indices[level][&pos];

            let mut next_states: HashMap<[u8; 24], (Vec<i8>, Vec<u8>)> = HashMap::default();

            for (_, (sums, prev_active)) in &prev_states {
                let mut current_vals: Vec<u8> = Vec::with_capacity(active.len());
                if level > 0 {
                    let prev_idx = &active_indices[level - 1];
                    for &p in active {
                        if p == pos { current_vals.push(0); }
                        else if let Some(&pi) = prev_idx.get(&p) {
                            current_vals.push(prev_active[pi]);
                        } else { current_vals.push(0); }
                    }
                } else {
                    current_vals.resize(active.len(), 0);
                }

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
                            let za = if bits_a & 1 == 1 { 1i32 } else { -1 };
                            let zb = if bits_b & 1 == 1 { 1i32 } else { -1 };
                            new_sums[lag_idx] += (2 * za * zb) as i8;
                        } else {
                            let wa = if (bits_a >> 1) & 1 == 1 { 1i32 } else { -1 };
                            let wb = if (bits_b >> 1) & 1 == 1 { 1i32 } else { -1 };
                            new_sums[lag_idx] += (2 * wa * wb) as i8;
                        }
                    }

                    let mut ok = true;
                    for &li in &lag_check_at_level[level] {
                        let zw_val = new_sums[li] as i32;
                        let max_xy = xy_max_abs[li];
                        if zw_val.abs() > max_xy { ok = false; break; }
                        if (zw_val + max_xy) % 2 != 0 { ok = false; break; }
                    }
                    if ok && level + 1 < zw_depth {
                        for li in 0..k {
                            let zw_val = new_sums[li] as i32;
                            let zw_rem = max_remaining[level + 1][li];
                            let max_xy = xy_max_abs[li];
                            if (zw_val.abs() - zw_rem) > max_xy { ok = false; break; }
                        }
                    }

                    if ok {
                        let next_key = pack_state(&new_sums, &current_vals);
                        next_states.entry(next_key).or_insert_with(|| {
                            (new_sums.clone(), current_vals.clone())
                        });
                    }
                }
            }

            // Write prev_states to redb (for pass 2)
            {
                let table_name = format!("level_{}", level);
                let table_def = redb::TableDefinition::<&[u8], &[u8]>::new(&table_name);
                let txn = db.begin_write().unwrap();
                {
                    let mut table = txn.open_table(table_def).unwrap();
                    for (key, (sums, active)) in &prev_states {
                        // Serialize: k bytes of sums + active.len() bytes of active
                        let mut val = Vec::with_capacity(k + active.len());
                        for &s in sums { val.push(s as u8); }
                        val.extend_from_slice(active);
                        table.insert(key.as_slice(), val.as_slice()).unwrap();
                    }
                }
                txn.commit().unwrap();
            }

            let count = next_states.len();
            eprint!("\r  Level {}/{}: {} states ({:.1?})   ",
                level + 1, zw_depth, count, start.elapsed());
            level_state_counts.push(count);

            prev_states = next_states;
        }

        // Write final level to redb too
        {
            let table_name = format!("level_{}", zw_depth);
            let table_def = redb::TableDefinition::<&[u8], &[u8]>::new(&table_name);
            let txn = db.begin_write().unwrap();
            {
                let mut table = txn.open_table(table_def).unwrap();
                for (key, (sums, active)) in &prev_states {
                    let mut val = Vec::with_capacity(k + active.len());
                    for &s in sums { val.push(s as u8); }
                    val.extend_from_slice(active);
                    table.insert(key.as_slice(), val.as_slice()).unwrap();
                }
            }
            txn.commit().unwrap();
        }

        eprintln!("\n  Pass 1 done in {:.1?}", start.elapsed());
        let max_states = level_state_counts.iter().max().copied().unwrap_or(0);
        let total_states: usize = level_state_counts.iter().sum();
        eprintln!("  Max states/level: {}, total: {}", max_states, total_states);

        // Pass 2: build MDD nodes bottom-up
        eprintln!("BFS pass 2 (build nodes from redb):");
        let pass2_start = std::time::Instant::now();

        let mut nodes: Vec<[u32; 4]> = Vec::new();
        nodes.push([DEAD; 4]); // sentinel

        // At deepest level: all surviving states → LEAF
        let mut level_node_map: HashMap<[u8; 24], u32> = HashMap::default();
        for (key, _) in &prev_states {
            level_node_map.insert(*key, LEAF);
        }

        for level in (0..zw_depth).rev() {
            let pos = pos_order[level];
            let active = &active_at_level[level];
            let new_idx = active_indices[level][&pos];

            // Read this level's states from redb
            let table_name = format!("level_{}", level);
            let table_def = redb::TableDefinition::<&[u8], &[u8]>::new(&table_name);
            let txn = db.begin_read().unwrap();
            let table = txn.open_table(table_def).unwrap();

            let mut new_level_map: HashMap<[u8; 24], u32> = HashMap::default();

            for entry in table.iter().unwrap() {
                let (key_guard, val_guard) = entry.unwrap();
                let key_bytes: [u8; 24] = key_guard.value().try_into().unwrap();
                let val_bytes = val_guard.value();

                let sums: Vec<i8> = val_bytes[..k].iter().map(|&b| b as i8).collect();
                let prev_active: Vec<u8> = val_bytes[k..].to_vec();

                let mut current_vals: Vec<u8> = Vec::with_capacity(active.len());
                if level > 0 {
                    let prev_idx = &active_indices[level - 1];
                    for &p in active {
                        if p == pos { current_vals.push(0); }
                        else if let Some(&pi) = prev_idx.get(&p) {
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
                            let za = if bits_a & 1 == 1 { 1i32 } else { -1 };
                            let zb = if bits_b & 1 == 1 { 1i32 } else { -1 };
                            new_sums[lag_idx] += (2 * za * zb) as i8;
                        } else {
                            let wa = if (bits_a >> 1) & 1 == 1 { 1i32 } else { -1 };
                            let wb = if (bits_b >> 1) & 1 == 1 { 1i32 } else { -1 };
                            new_sums[lag_idx] += (2 * wa * wb) as i8;
                        }
                    }

                    let child_key = pack_state(&new_sums, &current_vals);
                    if let Some(&child_nid) = level_node_map.get(&child_key) {
                        children[branch as usize] = child_nid;
                    }
                }

                // Create/dedup node
                let node_id = if children.iter().all(|&c| c == DEAD) {
                    DEAD
                } else {
                    let first = children[0];
                    if children.iter().all(|&c| c == first) {
                        first
                    } else {
                        let nid = nodes.len() as u32;
                        nodes.push(children);
                        nid
                    }
                };
                new_level_map.insert(key_bytes, node_id);
            }
            drop(table);
            drop(txn);

            eprint!("\r  Level {}/{}: {} nodes total ({:.1?})   ",
                level, zw_depth, nodes.len(), pass2_start.elapsed());
            level_node_map = new_level_map;
        }
        eprintln!();

        let root = *level_node_map.values().next().unwrap_or(&DEAD);

        eprintln!("BFS MDD k={}: {} ZW nodes, {:.1} MB, total {:.1?}",
            k, nodes.len(), nodes.len() as f64 * 16.0 / 1_048_576.0, start.elapsed());

        // Clean up
        drop(db);
        let _ = std::fs::remove_file(&db_path);

        BfsMdd { nodes, root, k }
    }
}
