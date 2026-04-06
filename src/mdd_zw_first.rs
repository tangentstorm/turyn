/// ZW-first 4-way MDD for boundary configs.
///
/// Variable order: z,w decisions first (top 2k levels), x,y decisions last (bottom 2k levels).
/// Each level branches 4-way. Positions visited in bouncing order within each half.
///
/// Top half: branch on (z[pos], w[pos]). At lag checkpoints, prune z,w combinations
/// where 2*N_Z + 2*N_W is outside the range achievable by any (x,y).
///
/// Bottom half: branch on (x[pos], y[pos]). At lag checkpoints, check exact constraint
/// N_X(s) + N_Y(s) = -(2*N_Z(s) + 2*N_W(s)).
///
/// Each path through the top half arrives at a node that roots the sub-MDD of valid (x,y)
/// pairs for that (z,w) boundary. This gives us the (z,w) → [(x,y)] mapping for free.

use rustc_hash::FxHashMap as HashMap;

pub const DEAD: u32 = 0;
pub const LEAF: u32 = u32::MAX;

pub struct ZwFirstMdd {
    pub nodes: Vec<[u32; 4]>,
    pub root: u32,
    pub k: usize,
    /// Position order for z,w (top half): bouncing order 0, 2k-1, 1, 2k-2, ...
    pub zw_pos_order: Vec<usize>,
    /// Position order for x,y (bottom half): same bouncing order
    pub xy_pos_order: Vec<usize>,
    /// Depth where z,w half ends and x,y half begins (= 2k)
    pub zw_depth: usize,
    /// Total depth (= 4k)
    pub total_depth: usize,
}

impl ZwFirstMdd {
    pub fn build(k: usize) -> Self {
        let zw_depth = 2 * k;
        let total_depth = 4 * k;

        // Bouncing position order (same for both halves)
        let mut pos_order: Vec<usize> = Vec::with_capacity(2 * k);
        for t in 0..k {
            pos_order.push(t);
            pos_order.push(2 * k - 1 - t);
        }

        let mut pos_to_level: Vec<usize> = vec![0; 2 * k];
        for (level, &pos) in pos_order.iter().enumerate() {
            pos_to_level[pos] = level;
        }

        // Build exact-lag bit pairs
        struct LagPairs {
            xy_pairs: Vec<(usize, usize)>,
            z_pairs: Vec<(usize, usize)>,
            w_pairs: Vec<(usize, usize)>,
        }
        let mut lags: Vec<LagPairs> = Vec::new();
        for j in 0..k {
            let xy_pairs: Vec<(usize, usize)> = (0..k - j)
                .map(|i| (i, k + i + j)).collect();
            let z_pairs = xy_pairs.clone();
            let w_pairs: Vec<(usize, usize)> = if j < k - 1 {
                (0..k - j - 1).map(|i| (i, k + i + j + 1)).collect()
            } else { Vec::new() };
            lags.push(LagPairs { xy_pairs, z_pairs, w_pairs });
        }

        // For each lag, compute:
        // - ZW events: pairs completing in the z,w half (both positions placed)
        // - XY events: pairs completing in the x,y half
        // - Max achievable |N_X(s) + N_Y(s)| for range pruning in z,w half
        struct LagEvent {
            pos_a: usize,
            pos_b: usize,
            is_z: bool,  // true = Z pair (2*za*zb), false = W pair (2*wa*wb)
        }
        let mut zw_events_at_level: Vec<Vec<(usize, LagEvent)>> = // (lag_idx, event)
            (0..zw_depth).map(|_| Vec::new()).collect();
        let mut xy_events_at_level: Vec<Vec<(usize, LagEvent)>> =
            (0..zw_depth).map(|_| Vec::new()).collect();
        let mut zw_lag_check_at_level: Vec<Vec<usize>> =
            (0..=zw_depth).map(|_| Vec::new()).collect();
        let mut xy_lag_check_at_level: Vec<Vec<usize>> =
            (0..=zw_depth).map(|_| Vec::new()).collect();

        // Max |N_X + N_Y| at each lag (for range pruning)
        let mut xy_max_abs: Vec<i32> = Vec::new();

        for (li, lag) in lags.iter().enumerate() {
            // Z pairs
            let mut zw_complete = 0usize;
            for &(a, b) in &lag.z_pairs {
                let complete = pos_to_level[a].max(pos_to_level[b]);
                zw_events_at_level[complete].push((li, LagEvent { pos_a: a, pos_b: b, is_z: true }));
                zw_complete = zw_complete.max(complete);
            }
            // W pairs
            for &(a, b) in &lag.w_pairs {
                let complete = pos_to_level[a].max(pos_to_level[b]);
                zw_events_at_level[complete].push((li, LagEvent { pos_a: a, pos_b: b, is_z: false }));
                zw_complete = zw_complete.max(complete);
            }
            zw_lag_check_at_level[zw_complete].push(li);

            // XY pairs (is_z doesn't matter here — all contribute N_X + N_Y)
            let mut xy_complete = 0usize;
            for &(a, b) in &lag.xy_pairs {
                let complete = pos_to_level[a].max(pos_to_level[b]);
                xy_events_at_level[complete].push((li, LagEvent { pos_a: a, pos_b: b, is_z: true }));
                xy_complete = xy_complete.max(complete);
            }
            xy_lag_check_at_level[xy_complete].push(li);

            // Max |N_X + N_Y| for this lag
            // N_X has xy_pairs.len() terms, each ±1. Same for N_Y.
            // So N_X + N_Y ranges from -2*pairs to +2*pairs with step 2.
            xy_max_abs.push(2 * lag.xy_pairs.len() as i32);
        }

        // Max remaining contribution per lag for range pruning
        // ZW events: |2*za*zb| = 2 or |2*wa*wb| = 2
        let mut zw_max_remaining: Vec<Vec<i32>> = vec![vec![0i32; k]; zw_depth + 1];
        for (li, lag) in lags.iter().enumerate() {
            for &(a, b) in &lag.z_pairs {
                let complete = pos_to_level[a].max(pos_to_level[b]);
                for level in 0..=complete { zw_max_remaining[level][li] += 2; }
            }
            for &(a, b) in &lag.w_pairs {
                let complete = pos_to_level[a].max(pos_to_level[b]);
                for level in 0..=complete { zw_max_remaining[level][li] += 2; }
            }
        }
        // XY events: |xa*xb + ya*yb| <= 2
        let mut xy_max_remaining: Vec<Vec<i32>> = vec![vec![0i32; k]; zw_depth + 1];
        for (li, lag) in lags.iter().enumerate() {
            for &(a, b) in &lag.xy_pairs {
                let complete = pos_to_level[a].max(pos_to_level[b]);
                for level in 0..=complete { xy_max_remaining[level][li] += 2; }
            }
        }

        // Active position tracking for z,w half
        let mut zw_last_use: Vec<usize> = vec![0; 2 * k];
        for (level, events) in zw_events_at_level.iter().enumerate() {
            for (_, ev) in events {
                zw_last_use[ev.pos_a] = zw_last_use[ev.pos_a].max(level);
                zw_last_use[ev.pos_b] = zw_last_use[ev.pos_b].max(level);
            }
        }
        let mut zw_active_at_level: Vec<Vec<usize>> = vec![Vec::new(); zw_depth + 1];
        for d in 0..zw_depth {
            let mut active: Vec<usize> = if d > 0 {
                zw_active_at_level[d - 1].iter()
                    .filter(|&&p| zw_last_use[p] >= d)
                    .copied().collect()
            } else { Vec::new() };
            active.push(pos_order[d]);
            active.sort();
            zw_active_at_level[d] = active;
        }
        let zw_active_indices: Vec<HashMap<usize, usize>> = zw_active_at_level.iter()
            .map(|active| active.iter().enumerate().map(|(i, &p)| (p, i)).collect())
            .collect();

        // Active position tracking for x,y half
        let mut xy_last_use: Vec<usize> = vec![0; 2 * k];
        for (level, events) in xy_events_at_level.iter().enumerate() {
            for (_, ev) in events {
                xy_last_use[ev.pos_a] = xy_last_use[ev.pos_a].max(level);
                xy_last_use[ev.pos_b] = xy_last_use[ev.pos_b].max(level);
            }
        }
        let mut xy_active_at_level: Vec<Vec<usize>> = vec![Vec::new(); zw_depth + 1];
        for d in 0..zw_depth {
            let mut active: Vec<usize> = if d > 0 {
                xy_active_at_level[d - 1].iter()
                    .filter(|&&p| xy_last_use[p] >= d)
                    .copied().collect()
            } else { Vec::new() };
            active.push(pos_order[d]);
            active.sort();
            xy_active_at_level[d] = active;
        }
        let xy_active_indices: Vec<HashMap<usize, usize>> = xy_active_at_level.iter()
            .map(|active| active.iter().enumerate().map(|(i, &p)| (p, i)).collect())
            .collect();

        // Build context
        struct Ctx {
            pos_order: Vec<usize>,
            zw_events_at_level: Vec<Vec<(usize, usize, usize, bool)>>, // (lag_idx, pos_a, pos_b, is_z)
            xy_events_at_level: Vec<Vec<(usize, usize, usize)>>,
            zw_lag_check_at_level: Vec<Vec<usize>>,
            xy_lag_check_at_level: Vec<Vec<usize>>,
            xy_max_abs: Vec<i32>,
            zw_max_remaining: Vec<Vec<i32>>,
            xy_max_remaining: Vec<Vec<i32>>,
            zw_active_at_level: Vec<Vec<usize>>,
            zw_active_indices: Vec<HashMap<usize, usize>>,
            xy_active_at_level: Vec<Vec<usize>>,
            xy_active_indices: Vec<HashMap<usize, usize>>,
            k: usize,
            zw_depth: usize,
        }

        let ctx = Ctx {
            pos_order: pos_order.clone(),
            zw_events_at_level: zw_events_at_level.iter().map(|evs|
                evs.iter().map(|(li, ev)| (*li, ev.pos_a, ev.pos_b, ev.is_z)).collect()
            ).collect(),
            xy_events_at_level: xy_events_at_level.iter().map(|evs|
                evs.iter().map(|(li, ev)| (*li, ev.pos_a, ev.pos_b)).collect()
            ).collect(),
            zw_lag_check_at_level,
            xy_lag_check_at_level,
            xy_max_abs,
            zw_max_remaining,
            xy_max_remaining,
            zw_active_at_level,
            zw_active_indices,
            xy_active_at_level,
            xy_active_indices,
            k,
            zw_depth,
        };

        let mut nodes: Vec<[u32; 4]> = Vec::new();
        nodes.push([DEAD; 4]); // node 0 = DEAD

        fn hash_node4(level: u8, children: &[u32; 4]) -> u64 {
            use std::hash::{Hash, Hasher};
            let mut h = rustc_hash::FxHasher::default();
            level.hash(&mut h);
            for &c in children { c.hash(&mut h); }
            h.finish()
        }
        let mut unique: HashMap<u64, u32> = HashMap::default();

        type StateKey = (u128, u64);
        type XyStateKey = (u128, u64); // (packed_sums, packed_active) - cleared per zw_sums
        let mut zw_memo: Vec<HashMap<StateKey, u32>> = (0..=zw_depth).map(|_| HashMap::default()).collect();
        let mut xy_memo: Vec<HashMap<XyStateKey, u32>> = (0..=zw_depth).map(|_| HashMap::default()).collect();

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
                packed |= (v as u64) << (i * 2); // 2 bits per position (4-way)
            }
            packed
        }

        fn bnd_val(bits: u32, pos: usize) -> i32 {
            if (bits >> pos) & 1 == 1 { 1 } else { -1 }
        }

        // Build XY bottom half: given zw_sums (the target for each lag),
        // build a 4-way MDD for (x,y) that satisfies N_X(s)+N_Y(s) = -zw_sums[s].
        fn build_xy(
            level: usize,  // 0..2k within xy half
            sums: &mut Vec<i8>,  // partial N_X + N_Y at each lag
            active_bits: &mut Vec<u8>,
            zw_sums: &[i8],  // target: sums[li] must equal -zw_sums[li] at end
            ctx: &Ctx,
            nodes: &mut Vec<[u32; 4]>,
            unique: &mut HashMap<u64, u32>,
            memo: &mut Vec<HashMap<XyStateKey, u32>>,
        ) -> u32 {
            if level == ctx.zw_depth {
                // Check all lags: N_X + N_Y = -zw_sums
                for li in 0..ctx.k {
                    if sums[li] != -zw_sums[li] { return DEAD; }
                }
                return LEAF;
            }

            let active = &ctx.xy_active_at_level[level];
            let mut current_vals: Vec<u8> = Vec::with_capacity(active.len());
            if level > 0 {
                let prev_indices = &ctx.xy_active_indices[level - 1];
                for &pos in active {
                    if pos == ctx.pos_order[level] {
                        current_vals.push(0);
                    } else if let Some(&pi) = prev_indices.get(&pos) {
                        current_vals.push(active_bits[pi]);
                    } else {
                        current_vals.push(0);
                    }
                }
            } else {
                current_vals.resize(active.len(), 0);
            }

            let new_pos = ctx.pos_order[level];
            let new_idx = ctx.xy_active_indices[level][&new_pos];

            let state_key = (pack_sums(sums), pack_active(&current_vals));
            if let Some(&cached) = memo[level].get(&state_key) {
                return cached;
            }

            // Use level offset for unique table to avoid collisions with zw half
            let unique_level = (ctx.zw_depth + level) as u8;

            let mut children = [DEAD; 4];
            for branch in 0u32..4 {
                let x_val = (branch >> 0) & 1;
                let y_val = (branch >> 1) & 1;

                // Symmetry breaking: x[0]=y[0]=+1
                if new_pos == 0 && branch != 0b11 { continue; }

                current_vals[new_idx] = branch as u8;

                let sums_backup = pack_sums(sums);

                // Process XY pair events at this level
                for &(lag_idx, pos_a, pos_b) in &ctx.xy_events_at_level[level] {
                    let idx_a = ctx.xy_active_indices[level][&pos_a];
                    let idx_b = ctx.xy_active_indices[level][&pos_b];
                    let bits_a = current_vals[idx_a] as u32;
                    let bits_b = current_vals[idx_b] as u32;
                    let xa = if (bits_a >> 0) & 1 == 1 { 1i32 } else { -1 };
                    let xb = if (bits_b >> 0) & 1 == 1 { 1i32 } else { -1 };
                    let ya = if (bits_a >> 1) & 1 == 1 { 1i32 } else { -1 };
                    let yb = if (bits_b >> 1) & 1 == 1 { 1i32 } else { -1 };
                    sums[lag_idx] += (xa * xb + ya * yb) as i8;
                }

                // Check completed lags
                let mut ok = true;
                for &li in &ctx.xy_lag_check_at_level[level] {
                    if sums[li] != -zw_sums[li] { ok = false; break; }
                }
                // Range check: can remaining XY events bring sums to -zw_sums?
                if ok && level + 1 < ctx.zw_depth {
                    for li in 0..ctx.k {
                        let gap = (sums[li] as i32) - (-(zw_sums[li] as i32));
                        let remaining = ctx.xy_max_remaining[level + 1][li];
                        if gap.abs() > remaining { ok = false; break; }
                    }
                }

                if ok {
                    children[branch as usize] = build_xy(
                        level + 1, sums, &mut current_vals, zw_sums,
                        ctx, nodes, unique, memo,
                    );
                }

                // Restore sums from packed backup
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
                    let key = hash_node4(unique_level, &children);
                    if let Some(&nid) = unique.get(&key) { nid }
                    else {
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

        // Build ZW top half: branch on (z,w), at bottom connect to XY sub-MDD.
        fn build_zw(
            level: usize,  // 0..2k within zw half
            sums: &mut Vec<i8>,  // partial 2*N_Z + 2*N_W at each lag
            active_bits: &mut Vec<u8>,
            ctx: &Ctx,
            nodes: &mut Vec<[u32; 4]>,
            unique: &mut HashMap<u64, u32>,
            zw_memo: &mut Vec<HashMap<StateKey, u32>>,
            xy_memo: &mut Vec<HashMap<XyStateKey, u32>>,
            zw_memo_count: &mut usize,
            max_memo_entries: usize,
            per_level_cap: usize,
        ) -> u32 {
            if level == ctx.zw_depth {
                // ZW half done. Build XY sub-MDD for these zw_sums.
                // Clear xy_memo for each distinct zw_sums to prevent memory explosion.
                // Nodes are still shared via the `unique` table.
                for m in xy_memo.iter_mut() { m.clear(); }
                let zw_sums: Vec<i8> = sums.to_vec();
                let mut xy_sums = vec![0i8; ctx.k];
                let mut xy_active: Vec<u8> = Vec::new();
                return build_xy(
                    0, &mut xy_sums, &mut xy_active, &zw_sums,
                    ctx, nodes, unique, xy_memo,
                );
            }

            let active = &ctx.zw_active_at_level[level];
            let mut current_vals: Vec<u8> = Vec::with_capacity(active.len());
            if level > 0 {
                let prev_indices = &ctx.zw_active_indices[level - 1];
                for &pos in active {
                    if pos == ctx.pos_order[level] {
                        current_vals.push(0);
                    } else if let Some(&pi) = prev_indices.get(&pos) {
                        current_vals.push(active_bits[pi]);
                    } else {
                        current_vals.push(0);
                    }
                }
            } else {
                current_vals.resize(active.len(), 0);
            }

            let new_pos = ctx.pos_order[level];
            let new_idx = ctx.zw_active_indices[level][&new_pos];

            let state_key = (pack_sums(sums), pack_active(&current_vals));
            if let Some(&cached) = zw_memo[level].get(&state_key) {
                return cached;
            }

            let mut children = [DEAD; 4];
            for branch in 0u32..4 {
                let z_val = (branch >> 0) & 1;
                let w_val = (branch >> 1) & 1;

                // Symmetry breaking: z[0]=w[0]=+1
                if new_pos == 0 && branch != 0b11 { continue; }

                current_vals[new_idx] = branch as u8;

                let sums_backup = pack_sums(sums);

                // Process ZW pair events at this level
                for &(lag_idx, pos_a, pos_b, is_z) in &ctx.zw_events_at_level[level] {
                    let idx_a = ctx.zw_active_indices[level][&pos_a];
                    let idx_b = ctx.zw_active_indices[level][&pos_b];
                    let bits_a = current_vals[idx_a] as u32;
                    let bits_b = current_vals[idx_b] as u32;
                    if is_z {
                        let za = if (bits_a >> 0) & 1 == 1 { 1i32 } else { -1 };
                        let zb = if (bits_b >> 0) & 1 == 1 { 1i32 } else { -1 };
                        sums[lag_idx] += (2 * za * zb) as i8;
                    } else {
                        let wa = if (bits_a >> 1) & 1 == 1 { 1i32 } else { -1 };
                        let wb = if (bits_b >> 1) & 1 == 1 { 1i32 } else { -1 };
                        sums[lag_idx] += (2 * wa * wb) as i8;
                    }
                }

                // At ZW lag checkpoints: range+parity prune
                let mut ok = true;
                for &li in &ctx.zw_lag_check_at_level[level] {
                    let zw_val = sums[li] as i32;
                    // Need N_X + N_Y = -zw_val, which must be in [-max, +max] with right parity
                    let max_xy = ctx.xy_max_abs[li];
                    if zw_val.abs() > max_xy { ok = false; break; }
                    if (zw_val + max_xy) % 2 != 0 { ok = false; break; }
                }
                // Range check: can remaining ZW events keep sums achievable?
                if ok && level + 1 < ctx.zw_depth {
                    for li in 0..ctx.k {
                        let zw_val = sums[li] as i32;
                        let zw_remaining = ctx.zw_max_remaining[level + 1][li];
                        let max_xy = ctx.xy_max_abs[li];
                        // After all ZW events: zw_val + remaining_zw in [-max_zw_total, +max_zw_total]
                        // Need: |final_zw_val| <= max_xy and right parity
                        // Quick check: if |zw_val| - zw_remaining > max_xy, impossible
                        if (zw_val.abs() - zw_remaining) > max_xy { ok = false; break; }
                    }
                }

                if ok {
                    children[branch as usize] = build_zw(
                        level + 1, sums, &mut current_vals,
                        ctx, nodes, unique, zw_memo, xy_memo,
                        zw_memo_count, max_memo_entries, per_level_cap,
                    );
                    if level == 1 {
                        eprint!("\r  ZW level 1 branch {}/4, {} nodes, zw_memo={}   ",
                            branch + 1, nodes.len(), *zw_memo_count);
                    }
                }

                // Restore sums from packed backup
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
                    let key = hash_node4(level as u8, &children);
                    if let Some(&nid) = unique.get(&key) { nid }
                    else {
                        let nid = nodes.len() as u32;
                        nodes.push(children);
                        unique.insert(key, nid);
                        nid
                    }
                }
            };

            // Cap total memo entries to prevent OOM at large k.
            // When over budget, evict the level with the most entries (typically deepest).
            if *zw_memo_count >= max_memo_entries {
                let (max_lvl, _) = zw_memo.iter().enumerate()
                    .max_by_key(|(_, m)| m.len()).unwrap();
                if zw_memo[max_lvl].len() > 0 {
                    *zw_memo_count -= zw_memo[max_lvl].len();
                    zw_memo[max_lvl].clear();
                }
            }
            zw_memo[level].insert(state_key, result);
            *zw_memo_count += 1;
            result
        }

        // Budget ~7GB for memo (actual overhead is ~140 bytes/entry in FxHashMap)
        let max_memo_entries: usize = 50_000_000;
        let per_level_cap: usize = max_memo_entries / (zw_depth + 1);
        let mut zw_memo_count: usize = 0;
        let mut sums = vec![0i8; k];
        let mut active_bits: Vec<u8> = Vec::new();
        let root = build_zw(
            0, &mut sums, &mut active_bits,
            &ctx, &mut nodes, &mut unique, &mut zw_memo, &mut xy_memo,
            &mut zw_memo_count, max_memo_entries, per_level_cap,
        );

        let zw_memo_entries: usize = zw_memo.iter().map(|m| m.len()).sum();
        let xy_memo_entries: usize = xy_memo.iter().map(|m| m.len()).sum();
        eprintln!("ZW-first MDD k={}: {} nodes, {:.1} MB (zw_memo={}, xy_memo={})",
            k, nodes.len(), nodes.len() as f64 * 16.0 / 1_048_576.0,
            zw_memo_entries, xy_memo_entries);

        ZwFirstMdd {
            nodes,
            root,
            k,
            zw_pos_order: pos_order.clone(),
            xy_pos_order: pos_order,
            zw_depth,
            total_depth: total_depth,
        }
    }

    /// Walk the ZW top half, collecting (z_bits, w_bits, xy_root_node) triples.
    /// xy_root_node is the MDD node that roots the valid (x,y) sub-diagram.
    pub fn enumerate_zw<F: FnMut(u32, u32, u32)>(&self, mut callback: F) {
        self.walk_zw(self.root, 0, 0, 0, &mut callback);
    }

    fn walk_zw<F: FnMut(u32, u32, u32)>(
        &self, nid: u32, level: usize, z_acc: u32, w_acc: u32, callback: &mut F,
    ) {
        if nid == DEAD { return; }
        if level == self.zw_depth {
            // nid is the root of the XY sub-MDD for this (z,w)
            callback(z_acc, w_acc, nid);
            return;
        }

        let pos = self.zw_pos_order[level];
        for branch in 0u32..4 {
            let child = self.nodes[nid as usize][branch as usize];
            if child == DEAD { continue; }
            let z_val = (branch >> 0) & 1;
            let w_val = (branch >> 1) & 1;
            self.walk_zw(child, level + 1, z_acc | (z_val << pos), w_acc | (w_val << pos), callback);
        }
    }

    /// Walk the XY bottom half from a given root node, collecting (x_bits, y_bits).
    pub fn enumerate_xy<F: FnMut(u32, u32)>(&self, xy_root: u32, mut callback: F) {
        self.walk_xy(xy_root, 0, 0, 0, &mut callback);
    }

    fn walk_xy<F: FnMut(u32, u32)>(
        &self, nid: u32, level: usize, x_acc: u32, y_acc: u32, callback: &mut F,
    ) {
        if nid == DEAD { return; }
        if nid == LEAF {
            callback(x_acc, y_acc);
            return;
        }
        if level == self.zw_depth {
            // Shouldn't happen unless LEAF reduction skipped levels
            callback(x_acc, y_acc);
            return;
        }

        let pos = self.xy_pos_order[level];
        for branch in 0u32..4 {
            let child = self.nodes[nid as usize][branch as usize];
            if child == DEAD { continue; }
            let x_val = (branch >> 0) & 1;
            let y_val = (branch >> 1) & 1;
            if child == LEAF {
                // All remaining positions are free — enumerate
                self.walk_xy_leaf(level + 1, x_acc | (x_val << pos), y_acc | (y_val << pos), callback);
            } else {
                self.walk_xy(child, level + 1, x_acc | (x_val << pos), y_acc | (y_val << pos), callback);
            }
        }
    }

    fn walk_xy_leaf<F: FnMut(u32, u32)>(
        &self, level: usize, x_acc: u32, y_acc: u32, callback: &mut F,
    ) {
        if level == self.zw_depth {
            callback(x_acc, y_acc);
            return;
        }
        let pos = self.xy_pos_order[level];
        for branch in 0u32..4 {
            let x_val = (branch >> 0) & 1;
            let y_val = (branch >> 1) & 1;
            self.walk_xy_leaf(level + 1, x_acc | (x_val << pos), y_acc | (y_val << pos), callback);
        }
    }

    /// Count paths through XY sub-MDD from a given root.
    pub fn count_xy_paths(&self, xy_root: u32) -> u128 {
        let mut memo: HashMap<u32, u128> = HashMap::default();
        self.count_xy_rec(xy_root, 0, &mut memo)
    }

    fn count_xy_rec(&self, nid: u32, level: usize, memo: &mut HashMap<u32, u128>) -> u128 {
        if nid == DEAD { return 0; }
        if nid == LEAF {
            // All remaining levels are free: 4^remaining
            let remaining = self.zw_depth - level;
            return 4u128.pow(remaining as u32);
        }
        if let Some(&c) = memo.get(&nid) { return c; }
        let total: u128 = self.nodes[nid as usize].iter()
            .map(|&child| self.count_xy_rec(child, level + 1, memo)).sum();
        memo.insert(nid, total);
        total
    }
}
