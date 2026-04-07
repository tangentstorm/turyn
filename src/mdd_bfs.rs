/// BFS-by-level MDD builder.
///
/// Two passes:
/// - Pass 1 (top-down): enumerate distinct states per level via BFS.
///   Only 2 levels in memory at once. Completed levels written to disk files.
/// - Pass 2 (bottom-up): for each level, recompute children and build MDD nodes.
///   At ZW boundary, build XY sub-MDDs using DFS (with caching).
///
/// Memory: O(max_states_per_level * 24 bytes) for state keys.
/// Disk: O(total_states * 24 bytes) for level files.

use rustc_hash::FxHashMap as HashMap;
use rayon::prelude::*;
use crate::mdd_reorder::Mdd4;
use crate::mdd_zw_first::{
    DEAD, LEAF, StateKey,
    pack_sums, pack_active, make_zw_delta,
    compute_active_tracking,
};

fn unpack_sums(packed: u128, k: usize) -> Vec<i8> {
    (0..k).map(|i| ((packed >> (i * 8)) & 0xFF) as i8).collect()
}

fn unpack_active(packed: u64, n: usize) -> Vec<u8> {
    (0..n).map(|i| ((packed >> (i * 2)) & 3) as u8).collect()
}

/// Write state keys to a flat binary file. Each key is 24 bytes (u128 + u64).
fn write_keys(path: &str, keys: &[StateKey]) -> std::io::Result<()> {
    use std::io::Write;
    let mut f = std::io::BufWriter::new(std::fs::File::create(path)?);
    for &(sums, active) in keys {
        f.write_all(&sums.to_le_bytes())?;
        f.write_all(&active.to_le_bytes())?;
    }
    f.flush()?;
    Ok(())
}

/// Read state keys from a flat binary file.
fn read_keys(path: &str) -> std::io::Result<Vec<StateKey>> {
    use std::io::Read;
    let mut f = std::io::BufReader::new(std::fs::File::open(path)?);
    let file_len = std::fs::metadata(path)?.len() as usize;
    let n_keys = file_len / 24;
    let mut keys = Vec::with_capacity(n_keys);
    let mut buf = [0u8; 24];
    for _ in 0..n_keys {
        f.read_exact(&mut buf)?;
        let sums = u128::from_le_bytes(buf[0..16].try_into().unwrap());
        let active = u64::from_le_bytes(buf[16..24].try_into().unwrap());
        keys.push((sums, active));
    }
    Ok(keys)
}

/// Precomputed context for BFS level expansion.
struct BfsCtx {
    k: usize,
    zw_depth: usize,
    pos_order: Vec<usize>,
    /// Per-level: Vec of (lag_idx, idx_a, idx_b, delta_table)
    events_at_level: Vec<Vec<(usize, usize, usize, [i8; 16])>>,
    lag_check_at_level: Vec<Vec<usize>>,
    xy_max_abs: Vec<i32>,
    max_remaining: Vec<Vec<i32>>,
    active_at_level: Vec<Vec<usize>>,
    /// Flat array: active_indices[level][pos] = index in active set (usize::MAX if absent)
    active_indices: Vec<Vec<usize>>,
}

impl BfsCtx {
    fn new(k: usize) -> Self {
        let zw_depth = 2 * k;

        let mut pos_order: Vec<usize> = Vec::with_capacity(2 * k);
        for t in 0..k {
            pos_order.push(t);
            pos_order.push(2 * k - 1 - t);
        }
        let mut pos_to_level: Vec<usize> = vec![0; 2 * k];
        for (level, &pos) in pos_order.iter().enumerate() {
            pos_to_level[pos] = level;
        }

        let mut z_pairs_per_lag: Vec<Vec<(usize, usize)>> = Vec::new();
        let mut w_pairs_per_lag: Vec<Vec<(usize, usize)>> = Vec::new();
        let mut xy_max_abs: Vec<i32> = Vec::new();
        for j in 0..k {
            let zp: Vec<(usize, usize)> = (0..k - j).map(|i| (i, k + i + j)).collect();
            let wp: Vec<(usize, usize)> = if j < k - 1 {
                (0..k - j - 1).map(|i| (i, k + i + j + 1)).collect()
            } else {
                Vec::new()
            };
            xy_max_abs.push(2 * zp.len() as i32);
            z_pairs_per_lag.push(zp);
            w_pairs_per_lag.push(wp);
        }

        // Raw events (before index resolution)
        let mut raw_events: Vec<Vec<(usize, usize, usize, bool)>> =
            (0..zw_depth).map(|_| Vec::new()).collect();
        let mut lag_check_at_level: Vec<Vec<usize>> =
            (0..=zw_depth).map(|_| Vec::new()).collect();

        for (li, (zp, wp)) in z_pairs_per_lag.iter().zip(w_pairs_per_lag.iter()).enumerate() {
            let mut complete = 0;
            for &(a, b) in zp {
                let c = pos_to_level[a].max(pos_to_level[b]);
                raw_events[c].push((li, a, b, true));
                complete = complete.max(c);
            }
            for &(a, b) in wp {
                let c = pos_to_level[a].max(pos_to_level[b]);
                raw_events[c].push((li, a, b, false));
                complete = complete.max(c);
            }
            lag_check_at_level[complete].push(li);
        }

        let mut max_remaining: Vec<Vec<i32>> = vec![vec![0i32; k]; zw_depth + 1];
        for (li, (zp, wp)) in z_pairs_per_lag.iter().zip(w_pairs_per_lag.iter()).enumerate() {
            for &(a, b) in zp {
                let c = pos_to_level[a].max(pos_to_level[b]);
                for lv in 0..=c {
                    max_remaining[lv][li] += 2;
                }
            }
            for &(a, b) in wp {
                let c = pos_to_level[a].max(pos_to_level[b]);
                for lv in 0..=c {
                    max_remaining[lv][li] += 2;
                }
            }
        }

        let pairs: Vec<Vec<(usize, usize)>> = raw_events.iter()
            .map(|evs| evs.iter().map(|&(_, a, b, _)| (a, b)).collect()).collect();
        let (active_at_level, active_indices) =
            compute_active_tracking(zw_depth, 2 * k, &pos_order, &pairs);

        // Pre-resolve events with delta tables
        let events_at_level: Vec<Vec<(usize, usize, usize, [i8; 16])>> =
            raw_events.iter().enumerate().map(|(level, evs)| {
                evs.iter().map(|&(li, pos_a, pos_b, is_z)| {
                    let idx_a = active_indices[level][pos_a];
                    let idx_b = active_indices[level][pos_b];
                    (li, idx_a, idx_b, make_zw_delta(is_z))
                }).collect()
            }).collect();

        BfsCtx {
            k,
            zw_depth,
            pos_order,
            events_at_level,
            lag_check_at_level,
            xy_max_abs,
            max_remaining,
            active_at_level,
            active_indices,
        }
    }

    /// Reconstruct current_vals from a state key at a given level.
    fn unpack_current_vals(&self, key: StateKey, level: usize) -> Vec<u8> {
        let n_active = self.active_at_level[level].len();
        unpack_active(key.1, n_active)
    }

    /// Expand a state at `level`, calling `callback(branch, child_key)` for each valid child.
    #[inline]
    fn expand_state_cb<F: FnMut(u32, StateKey)>(&self, key: StateKey, level: usize, mut callback: F) {
        let pos = self.pos_order[level];
        let active = &self.active_at_level[level];
        let n_active = active.len();
        let new_idx = self.active_indices[level][pos];

        let mut current_vals = [0u8; 32];
        if level > 0 {
            let prev_indices = &self.active_indices[level - 1];
            // Inline unpack_active: extract 2-bit values from packed u64
            let packed_active = key.1;
            for (i, &p) in active.iter().enumerate() {
                if p != pos {
                    let pi = prev_indices[p];
                    if pi != usize::MAX {
                        current_vals[i] = ((packed_active >> (pi * 2)) & 3) as u8;
                    }
                }
            }
        }

        // Inline unpack_sums into fixed array
        let sums_packed = key.0;
        let mut base_sums = [0i8; 16];
        for i in 0..self.k {
            base_sums[i] = ((sums_packed >> (i * 8)) & 0xFF) as i8;
        }

        for branch in 0u32..4 {
            if pos == 0 && branch != 0b11 {
                continue;
            }
            current_vals[new_idx] = branch as u8;

            // Compute new sums from base using delta tables
            let mut sums = base_sums;
            for &(lag_idx, idx_a, idx_b, ref delta) in &self.events_at_level[level] {
                let bits_a = current_vals[idx_a] as usize;
                let bits_b = current_vals[idx_b] as usize;
                sums[lag_idx] += delta[bits_a * 4 + bits_b];
            }

            // Pruning checks
            let mut ok = true;
            for &li in &self.lag_check_at_level[level] {
                let zw_val = sums[li] as i32;
                let max_xy = self.xy_max_abs[li];
                if zw_val.abs() > max_xy {
                    ok = false;
                    break;
                }
                if (zw_val + max_xy) % 2 != 0 {
                    ok = false;
                    break;
                }
            }
            if ok && level + 1 < self.zw_depth {
                for li in 0..self.k {
                    let zw_val = sums[li] as i32;
                    let zw_rem = self.max_remaining[level + 1][li];
                    let max_xy = self.xy_max_abs[li];
                    if (zw_val.abs() - zw_rem) > max_xy {
                        ok = false;
                        break;
                    }
                }
            }

            if ok {
                let new_sums = pack_sums(&sums[..self.k]);
                let new_active = pack_active(&current_vals[..n_active]);
                callback(branch, (new_sums, new_active));
            }
        }
    }

    /// Expand a state at `level` to produce child states at `level + 1`.
    fn expand_state(&self, key: StateKey, level: usize) -> Vec<(u32, StateKey)> {
        let mut results = Vec::new();
        self.expand_state_cb(key, level, |branch, child_key| {
            results.push((branch, child_key));
        });
        results
    }
}

/// Write child indices to disk. Each parent has [u32; 4] child indices.
/// u32::MAX means DEAD/no child.
fn write_children(path: &str, children: &[[u32; 4]]) -> std::io::Result<()> {
    use std::io::Write;
    let mut f = std::io::BufWriter::new(std::fs::File::create(path)?);
    for ch in children {
        for &c in ch {
            f.write_all(&c.to_le_bytes())?;
        }
    }
    f.flush()?;
    Ok(())
}

fn read_children(path: &str) -> std::io::Result<Vec<[u32; 4]>> {
    use std::io::Read;
    let file_len = std::fs::metadata(path)?.len() as usize;
    let n = file_len / 16;
    let mut f = std::io::BufReader::new(std::fs::File::open(path)?);
    let mut result = Vec::with_capacity(n);
    let mut buf = [0u8; 16];
    for _ in 0..n {
        f.read_exact(&mut buf)?;
        let ch = [
            u32::from_le_bytes(buf[0..4].try_into().unwrap()),
            u32::from_le_bytes(buf[4..8].try_into().unwrap()),
            u32::from_le_bytes(buf[8..12].try_into().unwrap()),
            u32::from_le_bytes(buf[12..16].try_into().unwrap()),
        ];
        result.push(ch);
    }
    Ok(result)
}

const NO_CHILD: u32 = u32::MAX - 1; // sentinel for "no child in next level"

/// Build a complete ZW+XY MDD using BFS for the ZW half and DFS for XY sub-MDDs.
///
/// Single-pass approach: during top-down BFS, store parent→child index mappings.
/// Then bottom-up, just look up child indices (no re-expansion needed).
pub fn build_bfs_mdd(k: usize) -> Mdd4 {
    let zw_depth = 2 * k;
    let total_depth = 4 * k;
    let ctx = BfsCtx::new(k);
    let start = std::time::Instant::now();

    let tmp_dir = format!("/tmp/mdd_bfs_k{}", k);
    let _ = std::fs::create_dir_all(&tmp_dir);

    // ===== Pass 1: BFS top-down, enumerate states + store children =====
    eprintln!("BFS Pass 1: enumerating ZW states (k={}, depth={})...", k, zw_depth);

    let init_key: StateKey = (pack_sums(&vec![0i8; k]), 0u64);
    let mut current_keys: Vec<StateKey> = vec![init_key];
    let mut level_key_counts: Vec<usize> = vec![1];

    for level in 0..zw_depth {
        let n_parents = current_keys.len();
        // Estimate if we need memory-efficient mode (sorted Vec vs HashMap)
        // HashMap: ~80 bytes/entry. Sorted Vec: ~24 bytes/entry.
        // Use sorted mode when states would exceed ~50M entries
        let use_sorted = n_parents > 5_000_000;

        let (next_keys, parent_children) = if use_sorted {
            // Two-pass sorted dedup: lower peak memory for large levels.
            // Write parent keys to disk so we can free them during child collection.
            let parent_path = format!("{}/parent_keys_{}.bin", tmp_dir, level);
            write_keys(&parent_path, &current_keys).expect("write parent keys");

            // Pass 1: Chunked expansion + sort + merge to control peak memory.
            // Process parents in chunks, sort each chunk's children, then merge.
            let chunk_size = 2_000_000; // ~2M parents per chunk
            let n_chunks = (n_parents + chunk_size - 1) / chunk_size;
            let mut all_child_keys: Vec<StateKey> = Vec::new();

            for chunk_idx in 0..n_chunks {
                let start_idx = chunk_idx * chunk_size;
                let end_idx = (start_idx + chunk_size).min(n_parents);
                let chunk = &current_keys[start_idx..end_idx];

                let mut chunk_children: Vec<StateKey> = Vec::with_capacity(chunk.len() * 3);
                for &key in chunk {
                    ctx.expand_state_cb(key, level, |_branch, child_key| {
                        chunk_children.push(child_key);
                    });
                }
                chunk_children.sort_unstable();
                chunk_children.dedup();

                // Merge with accumulated results
                if all_child_keys.is_empty() {
                    all_child_keys = chunk_children;
                } else {
                    // Merge two sorted deduped arrays
                    let mut merged = Vec::with_capacity(all_child_keys.len() + chunk_children.len());
                    let mut i = 0;
                    let mut j = 0;
                    while i < all_child_keys.len() && j < chunk_children.len() {
                        match all_child_keys[i].cmp(&chunk_children[j]) {
                            std::cmp::Ordering::Less => { merged.push(all_child_keys[i]); i += 1; }
                            std::cmp::Ordering::Greater => { merged.push(chunk_children[j]); j += 1; }
                            std::cmp::Ordering::Equal => { merged.push(all_child_keys[i]); i += 1; j += 1; }
                        }
                    }
                    merged.extend_from_slice(&all_child_keys[i..]);
                    merged.extend_from_slice(&chunk_children[j..]);
                    all_child_keys = merged;
                }
            }
            drop(current_keys);
            current_keys = Vec::new();
            all_child_keys.shrink_to_fit();
            // Now all_child_keys is sorted+unique, index = position

            // Pass 2: re-read parents from disk, re-expand to get child indices
            let parent_keys = read_keys(&parent_path).expect("read parent keys");
            let _ = std::fs::remove_file(&parent_path);
            let mut parent_children: Vec<[u32; 4]> = Vec::with_capacity(parent_keys.len());
            for &key in &parent_keys {
                let mut ch = [NO_CHILD; 4];
                ctx.expand_state_cb(key, level, |branch, child_key| {
                    let idx = all_child_keys.binary_search(&child_key).unwrap() as u32;
                    ch[branch as usize] = idx;
                });
                parent_children.push(ch);
            }
            drop(parent_keys);
            (all_child_keys, parent_children)
        } else {
            // HashMap dedup: faster for small levels
            let mut next_key_to_idx: HashMap<StateKey, u32> = HashMap::default();
            let mut parent_children: Vec<[u32; 4]> = Vec::with_capacity(n_parents);

            for &key in &current_keys {
                let mut ch = [NO_CHILD; 4];
                ctx.expand_state_cb(key, level, |branch, child_key| {
                    let next_len = next_key_to_idx.len() as u32;
                    let idx = *next_key_to_idx.entry(child_key).or_insert(next_len);
                    ch[branch as usize] = idx;
                });
                parent_children.push(ch);
            }

            let mut next_keys = vec![(0u128, 0u64); next_key_to_idx.len()];
            for (&key, &idx) in &next_key_to_idx {
                next_keys[idx as usize] = key;
            }
            (next_keys, parent_children)
        };

        // Write parent children to disk (for pass 2)
        let path = format!("{}/children_{}.bin", tmp_dir, level);
        write_children(&path, &parent_children).expect("Failed to write children");

        let count = next_keys.len();
        eprint!("\r  Level {}/{}: {} → {} states ({:.1?})   ",
            level + 1, zw_depth, n_parents, count, start.elapsed());
        level_key_counts.push(count);
        current_keys = next_keys;
    }

    let max_states = level_key_counts.iter().max().copied().unwrap_or(0);
    let total_states: usize = level_key_counts.iter().sum();
    eprintln!("\n  Pass 1 done in {:.1?}: max {}, total {} states",
        start.elapsed(), max_states, total_states);

    // ===== Build XY sub-MDDs for distinct boundary zw_sums =====
    let zw_only = std::env::var("MDD_ZW_ONLY").is_ok();

    let mut nodes: Vec<[u32; 4]> = Vec::new();
    nodes.push([DEAD; 4]); // sentinel node 0
    let mut unique: HashMap<u64, u32> = HashMap::default();

    let boundary_nids: Vec<u32> = if zw_only {
        // ZW-only: all valid boundary states → LEAF
        eprintln!("ZW-only mode: {} boundary states → LEAF", current_keys.len());
        let mut nids = Vec::with_capacity(current_keys.len());
        for &(sums_packed, _) in &current_keys {
            let sums = unpack_sums(sums_packed, k);
            let mut ok = true;
            for li in 0..k {
                let zw_val = sums[li] as i32;
                let max_xy = ctx.xy_max_abs[li];
                if zw_val.abs() > max_xy { ok = false; break; }
                if (zw_val + max_xy) % 2 != 0 { ok = false; break; }
            }
            nids.push(if ok { LEAF } else { DEAD });
        }
        nids
    } else {
        eprintln!("Building XY sub-MDDs for {} boundary states...", current_keys.len());
        let xy_start = std::time::Instant::now();

        let mut xy_cache: HashMap<u128, u32> = HashMap::default();

        let distinct_sums: Vec<u128> = {
            let mut set: HashMap<u128, ()> = HashMap::default();
            for &(sums, _) in &current_keys {
                set.entry(sums).or_insert(());
            }
            set.into_keys().collect()
        };
        eprintln!("  {} distinct zw_sums from {} boundary states", distinct_sums.len(), current_keys.len());

        for (i, &sums_packed) in distinct_sums.iter().enumerate() {
            if i % 100000 == 0 && i > 0 {
                eprint!("\r  XY build {}/{} ({:.1?})   ", i, distinct_sums.len(), xy_start.elapsed());
            }
            let zw_sums = unpack_sums(sums_packed, k);
            let root = build_xy_dfs(
                &zw_sums, k, zw_depth,
                &ctx.pos_order, &ctx.active_at_level, &ctx.active_indices,
                &ctx.xy_max_abs,
                &mut nodes, &mut unique,
            );
            xy_cache.insert(sums_packed, root);
        }
        eprintln!("\r  XY builds done: {} sub-MDDs in {:.1?}, {} total nodes",
            distinct_sums.len(), xy_start.elapsed(), nodes.len());

        // Map boundary states to XY root node IDs
        let mut nids = Vec::with_capacity(current_keys.len());
        for &(sums, _) in &current_keys {
            nids.push(xy_cache[&sums]);
        }
        nids
    };

    // ===== Pass 2: bottom-up, build ZW nodes using stored children =====
    eprintln!("BFS Pass 2: building ZW nodes bottom-up...");
    let pass2_start = std::time::Instant::now();

    // child_nids[i] = node ID for state i at the "next" level
    let mut child_nids: Vec<u32> = boundary_nids;

    for level in (0..zw_depth).rev() {
        let path = format!("{}/children_{}.bin", tmp_dir, level);
        let parent_children = read_children(&path).expect("Failed to read children");
        let _ = std::fs::remove_file(&path); // cleanup as we go

        let mut node_dedup: HashMap<[u32; 4], u32> = HashMap::default();
        let mut level_nids: Vec<u32> = Vec::with_capacity(parent_children.len());

        for ch_indices in &parent_children {
            let mut children = [DEAD; 4];
            for b in 0..4 {
                let idx = ch_indices[b];
                if idx != NO_CHILD {
                    children[b] = child_nids[idx as usize];
                }
            }

            let node_id = if children.iter().all(|&c| c == DEAD) {
                DEAD
            } else {
                let first = children[0];
                if children.iter().all(|&c| c == first) {
                    first
                } else if let Some(&existing) = node_dedup.get(&children) {
                    existing
                } else {
                    let nid = nodes.len() as u32;
                    nodes.push(children);
                    node_dedup.insert(children, nid);
                    nid
                }
            };
            level_nids.push(node_id);
        }

        eprint!("\r  Level {}/{}: {} states → {} nodes total ({:.1?})   ",
            level, zw_depth, parent_children.len(), nodes.len(), pass2_start.elapsed());
        child_nids = level_nids;
    }
    eprintln!();

    let root = if child_nids.is_empty() { DEAD } else { child_nids[0] };
    eprintln!("BFS MDD k={}: {} nodes, {:.1} MB, total {:.1?}",
        k, nodes.len(), nodes.len() as f64 * 16.0 / 1_048_576.0, start.elapsed());

    // Cleanup
    let _ = std::fs::remove_dir(&tmp_dir);

    Mdd4 {
        nodes,
        root,
        k,
        depth: total_depth,
    }
}

/// Build XY sub-MDD using DFS (same logic as mdd_zw_first but standalone).
/// Returns the root node ID for the XY sub-MDD.
fn build_xy_dfs(
    zw_sums: &[i8],
    k: usize,
    xy_depth: usize,
    pos_order: &[usize],
    active_at_level: &[Vec<usize>],
    active_indices: &[Vec<usize>],
    xy_max_abs: &[i32],
    nodes: &mut Vec<[u32; 4]>,
    unique: &mut HashMap<u64, u32>,
) -> u32 {
    // Precompute XY events (same structure as ZW but for x,y pairs)
    let mut xy_events_at_level: Vec<Vec<(usize, usize, usize)>> =
        (0..xy_depth).map(|_| Vec::new()).collect();
    let mut xy_lag_check_at_level: Vec<Vec<usize>> =
        (0..=xy_depth).map(|_| Vec::new()).collect();
    let mut xy_max_remaining: Vec<Vec<i32>> = vec![vec![0i32; k]; xy_depth + 1];

    let mut pos_to_level: Vec<usize> = vec![0; 2 * k];
    for (level, &pos) in pos_order.iter().enumerate() {
        pos_to_level[pos] = level;
    }

    for j in 0..k {
        let pairs: Vec<(usize, usize)> = (0..k - j).map(|i| (i, k + i + j)).collect();
        let mut complete = 0;
        for &(a, b) in &pairs {
            let c = pos_to_level[a].max(pos_to_level[b]);
            xy_events_at_level[c].push((j, a, b));
            complete = complete.max(c);
            for lv in 0..=c {
                xy_max_remaining[lv][j] += 2;
            }
        }
        xy_lag_check_at_level[complete].push(j);
    }

    type XyStateKey = (u128, u64);
    let mut memo: Vec<HashMap<XyStateKey, u32>> = (0..=xy_depth).map(|_| HashMap::default()).collect();

    fn build_xy_rec(
        level: usize,
        sums: &mut Vec<i8>,
        active_bits: &[u8],
        zw_sums: &[i8],
        k: usize,
        xy_depth: usize,
        pos_order: &[usize],
        active_at_level: &[Vec<usize>],
        active_indices: &[Vec<usize>],
        xy_events_at_level: &[Vec<(usize, usize, usize)>],
        xy_lag_check_at_level: &[Vec<usize>],
        xy_max_remaining: &[Vec<i32>],
        nodes: &mut Vec<[u32; 4]>,
        unique: &mut HashMap<u64, u32>,
        memo: &mut Vec<HashMap<(u128, u64), u32>>,
    ) -> u32 {
        if level == xy_depth {
            for li in 0..k {
                if sums[li] != -zw_sums[li] {
                    return DEAD;
                }
            }
            return LEAF;
        }

        let active = &active_at_level[level];
        let n_active = active.len();
        let mut current_vals = [0u8; 32];
        if level > 0 {
            let prev_indices = &active_indices[level - 1];
            for (i, &pos) in active.iter().enumerate() {
                if pos != pos_order[level] {
                    let pi = prev_indices[pos];
                    if pi != usize::MAX {
                        current_vals[i] = active_bits[pi];
                    }
                }
            }
        }

        let new_pos = pos_order[level];
        let new_idx = active_indices[level][new_pos];

        let state_key = (pack_sums(sums), pack_active(&current_vals[..n_active]));
        if let Some(&cached) = memo[level].get(&state_key) {
            return cached;
        }

        let unique_level = (xy_depth + level) as u8;
        let mut children = [DEAD; 4];

        for branch in 0u32..4 {
            if new_pos == 0 && branch != 0b11 {
                continue;
            }
            current_vals[new_idx] = branch as u8;
            let sums_backup = pack_sums(sums);

            for &(lag_idx, pos_a, pos_b) in &xy_events_at_level[level] {
                let idx_a = active_indices[level][pos_a];
                let idx_b = active_indices[level][pos_b];
                let bits_a = current_vals[idx_a] as u32;
                let bits_b = current_vals[idx_b] as u32;
                let xa = if bits_a & 1 == 1 { 1i32 } else { -1 };
                let xb = if bits_b & 1 == 1 { 1i32 } else { -1 };
                let ya = if (bits_a >> 1) & 1 == 1 { 1i32 } else { -1 };
                let yb = if (bits_b >> 1) & 1 == 1 { 1i32 } else { -1 };
                sums[lag_idx] += (xa * xb + ya * yb) as i8;
            }

            let mut ok = true;
            for &li in &xy_lag_check_at_level[level] {
                if sums[li] != -zw_sums[li] {
                    ok = false;
                    break;
                }
            }
            if ok && level + 1 < xy_depth {
                for li in 0..k {
                    let gap = (sums[li] as i32) - (-(zw_sums[li] as i32));
                    let remaining = xy_max_remaining[level + 1][li];
                    if gap.abs() > remaining {
                        ok = false;
                        break;
                    }
                }
            }

            if ok {
                children[branch as usize] = build_xy_rec(
                    level + 1,
                    sums,
                    &current_vals[..n_active],
                    zw_sums,
                    k,
                    xy_depth,
                    pos_order,
                    active_at_level,
                    active_indices,
                    xy_events_at_level,
                    xy_lag_check_at_level,
                    xy_max_remaining,
                    nodes,
                    unique,
                    memo,
                );
            }

            // Restore sums
            for i in 0..sums.len() {
                sums[i] = ((sums_backup >> (i * 8)) & 0xFF) as i8;
            }
        }

        let result = if children.iter().all(|&c| c == DEAD) {
            DEAD
        } else {
            let first = children[0];
            if children.iter().all(|&c| c == first) {
                first
            } else {
                let key = {
                    use std::hash::{Hash, Hasher};
                    let mut h = rustc_hash::FxHasher::default();
                    unique_level.hash(&mut h);
                    for &c in &children {
                        c.hash(&mut h);
                    }
                    h.finish()
                };
                if let Some(&nid) = unique.get(&key) {
                    nid
                } else {
                    let nid = nodes.len() as u32;
                    nodes.push(children);
                    unique.insert(key, nid);
                    nid
                }
            }
        };

        memo[level].insert(state_key, result);
        result
    }

    let mut sums = vec![0i8; k];
    build_xy_rec(
        0, &mut sums, &[],
        zw_sums, k, xy_depth,
        pos_order, active_at_level, active_indices,
        &xy_events_at_level, &xy_lag_check_at_level, &xy_max_remaining,
        nodes, unique, &mut memo,
    )
}
