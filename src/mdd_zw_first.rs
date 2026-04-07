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

pub type StateKey = (u128, u64);

pub fn pack_sums(sums: &[i8]) -> u128 {
    let mut packed = 0u128;
    for (i, &s) in sums.iter().enumerate() {
        packed |= ((s as u8 as u128) & 0xFF) << (i * 8);
    }
    packed
}

pub fn pack_active(vals: &[u8]) -> u64 {
    let mut packed = 0u64;
    for (i, &v) in vals.iter().enumerate() {
        packed |= (v as u64) << (i * 2);
    }
    packed
}

pub fn hash_node4(level: u8, children: &[u32; 4]) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = rustc_hash::FxHasher::default();
    level.hash(&mut h);
    for &c in children { c.hash(&mut h); }
    h.finish()
}

/// Per-level profiling counters for MDD build.
pub struct BuildStats {
    /// Per ZW level: (calls, memo_hits, pruned, xy_builds)
    pub zw_level_stats: Vec<(u64, u64, u64, u64)>,
    /// Per XY level: (calls, memo_hits, pruned)
    pub xy_level_stats: Vec<(u64, u64, u64)>,
    /// Total time in XY sub-MDD builds (nanoseconds)
    pub xy_build_ns: u64,
    /// Number of distinct zw_sums that triggered XY builds
    pub xy_build_count: u64,
    /// Number of ZW memo evictions
    pub zw_memo_evictions: u64,
}

impl BuildStats {
    fn new(k: usize) -> Self {
        let zw_depth = 2 * k;
        BuildStats {
            zw_level_stats: vec![(0, 0, 0, 0); zw_depth + 1],
            xy_level_stats: vec![(0, 0, 0); zw_depth + 1],
            xy_build_ns: 0,
            xy_build_count: 0,
            zw_memo_evictions: 0,
        }
    }

    pub fn report(&self, k: usize) {
        let zw_depth = 2 * k;
        eprintln!("\n=== MDD Build Profile (k={}) ===", k);
        eprintln!("ZW levels (depth={}):", zw_depth);
        eprintln!("  {:>5} {:>12} {:>12} {:>12} {:>10}", "Level", "Calls", "MemoHits", "Pruned", "XYBuilds");
        for (i, &(calls, hits, pruned, xy)) in self.zw_level_stats.iter().enumerate() {
            if calls > 0 {
                let hit_pct = if calls > 0 { 100.0 * hits as f64 / calls as f64 } else { 0.0 };
                eprintln!("  {:>5} {:>12} {:>12} ({:>5.1}%) {:>12} {:>10}",
                    i, calls, hits, hit_pct, pruned, xy);
            }
        }
        let total_zw_calls: u64 = self.zw_level_stats.iter().map(|s| s.0).sum();
        let total_zw_hits: u64 = self.zw_level_stats.iter().map(|s| s.1).sum();
        let total_zw_pruned: u64 = self.zw_level_stats.iter().map(|s| s.2).sum();
        eprintln!("  Total: {} calls, {} hits ({:.1}%), {} pruned",
            total_zw_calls, total_zw_hits,
            if total_zw_calls > 0 { 100.0 * total_zw_hits as f64 / total_zw_calls as f64 } else { 0.0 },
            total_zw_pruned);

        eprintln!("\nXY levels:");
        eprintln!("  {:>5} {:>12} {:>12} {:>12}", "Level", "Calls", "MemoHits", "Pruned");
        for (i, &(calls, hits, pruned)) in self.xy_level_stats.iter().enumerate() {
            if calls > 0 {
                let hit_pct = if calls > 0 { 100.0 * hits as f64 / calls as f64 } else { 0.0 };
                eprintln!("  {:>5} {:>12} {:>12} ({:>5.1}%) {:>12}",
                    i, calls, hits, hit_pct, pruned);
            }
        }
        let total_xy_calls: u64 = self.xy_level_stats.iter().map(|s| s.0).sum();
        let total_xy_hits: u64 = self.xy_level_stats.iter().map(|s| s.1).sum();
        let total_xy_pruned: u64 = self.xy_level_stats.iter().map(|s| s.2).sum();
        eprintln!("  Total: {} calls, {} hits ({:.1}%), {} pruned",
            total_xy_calls, total_xy_hits,
            if total_xy_calls > 0 { 100.0 * total_xy_hits as f64 / total_xy_calls as f64 } else { 0.0 },
            total_xy_pruned);

        eprintln!("\nXY sub-MDD builds: {} (total {:.3}s)",
            self.xy_build_count, self.xy_build_ns as f64 / 1e9);
        eprintln!("ZW memo evictions: {}", self.zw_memo_evictions);
    }
}

/// Lightweight status reporter. Checks wall time every N calls
/// and prints a one-line update every ~10 seconds.
struct StatusLine {
    call_count: u64,
    start: std::time::Instant,
    last_print: std::time::Instant,
    k: usize,
}

impl StatusLine {
    fn new(k: usize) -> Self {
        let now = std::time::Instant::now();
        StatusLine { call_count: 0, start: now, last_print: now, k }
    }

    #[inline]
    fn tick(&mut self, nodes: usize, zw_memo_count: usize, xy_cache_len: usize) {
        self.call_count += 1;
        // Check time every 500K calls (~1ns amortized cost of the branch)
        if self.call_count & 0x7_FFFF == 0 {
            let now = std::time::Instant::now();
            if now.duration_since(self.last_print).as_secs() >= 10 {
                self.last_print = now;
                eprint!("\r  [k={} {:.0?}] {} nodes, zw_memo={}, xy_cache={}   ",
                    self.k, now.duration_since(self.start), nodes, zw_memo_count, xy_cache_len);
            }
        }
    }
}

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
        let (mdd, stats) = Self::build_inner(k, None, None);
        if std::env::var("MDD_PROFILE").is_ok() {
            stats.report(k);
        }
        mdd
    }

    /// Build with profiling, returning stats.
    pub fn build_with_stats(k: usize) -> (Self, BuildStats) {
        Self::build_inner(k, None, None)
    }

    /// Build ZW-only MDD (no XY sub-MDDs). Much faster and smaller.
    /// At the ZW boundary, valid states become LEAF instead of building
    /// an XY sub-MDD. Use build_xy_for_boundary() at runtime to get XY.
    pub fn build_zw_only(k: usize) -> Self {
        let (mdd, stats) = Self::build_inner_opts(k, None, None, true);
        if std::env::var("MDD_PROFILE").is_ok() {
            stats.report(k);
        }
        mdd
    }

    /// Build with parallel branches using rayon.
    /// parallel_depth=1: 4 subtrees (level 1). parallel_depth=2: 16 subtrees (levels 1+2).
    pub fn build_parallel(k: usize) -> Self {
        // Choose depth based on available cores
        let ncores = rayon::current_num_threads();
        let parallel_depth = if ncores >= 16 { 2 } else { 1 };
        Self::build_parallel_depth(k, parallel_depth)
    }

    pub fn build_parallel_depth(k: usize, parallel_depth: usize) -> Self {
        use rayon::prelude::*;

        let start = std::time::Instant::now();

        // Generate all branch combinations for the given depth.
        // Level 0 has 1 branch (symmetry: 0b11). Levels 1..depth have 4 each.
        // Total subtrees = 4^parallel_depth
        let num_subtrees = 4u32.pow(parallel_depth as u32);
        eprintln!("  Parallel build: {} subtrees (depth {}, {} cores)...",
            num_subtrees, parallel_depth, rayon::current_num_threads());

        // Each subtree is identified by a Vec of branch choices at levels 1..parallel_depth
        let subtree_branches: Vec<Vec<u32>> = (0..num_subtrees).map(|idx| {
            (0..parallel_depth).map(|d| (idx >> (d * 2)) & 3).collect()
        }).collect();

        // Build each subtree independently in parallel
        let branch_results: Vec<(Self, Vec<u32>)> = subtree_branches.into_par_iter().map(|branches| {
            let (mdd, _stats) = Self::build_inner(k, None, Some(&branches));
            (mdd, branches)
        }).collect();

        eprintln!("  Parallel build: all subtrees done in {:.1?}, merging...", start.elapsed());

        // Merge: combine independent subtree MDDs into one.
        // Each subtree MDD has a path from root through the restricted levels.
        // We extract the actual subtree root and build shared prefix levels.

        let mut merged_nodes: Vec<[u32; 4]> = Vec::new();
        merged_nodes.push([DEAD; 4]); // node 0 = DEAD sentinel

        // Extract subtree roots and copy nodes with ID remapping.
        // Key: branch path (Vec<u32>) → remapped subtree root
        let mut subtree_map: HashMap<Vec<u32>, u32> = HashMap::default();

        for (mdd, branches) in &branch_results {
            let offset = merged_nodes.len() as u32;

            // Copy nodes (skip sentinel)
            for node in &mdd.nodes[1..] {
                let mut remapped = [DEAD; 4];
                for j in 0..4 {
                    let c = node[j];
                    remapped[j] = if c == DEAD || c == LEAF { c }
                                  else { c - 1 + offset };
                }
                merged_nodes.push(remapped);
            }

            // Navigate from root through restricted levels to find subtree root
            let mut nid = mdd.root;
            if nid != DEAD && nid != LEAF {
                // Level 0: symmetry breaking → branch 3 (0b11)
                nid = mdd.nodes[nid as usize][3];
            }
            for &b in branches {
                if nid == DEAD || nid == LEAF { break; }
                nid = mdd.nodes[nid as usize][b as usize];
            }
            // Remap the subtree root
            let remapped_root = if nid == DEAD || nid == LEAF { nid }
                                else { nid - 1 + offset };
            subtree_map.insert(branches.clone(), remapped_root);
        }

        // Build the shared prefix levels bottom-up.
        // For depth=2: build level-2 nodes (4 children each from subtrees),
        // then level-1 nodes, then level-0.
        fn build_prefix_level(
            depth: usize, max_depth: usize,
            path: &mut Vec<u32>,
            subtree_map: &HashMap<Vec<u32>, u32>,
            nodes: &mut Vec<[u32; 4]>,
        ) -> u32 {
            if depth == max_depth {
                // Leaf of prefix: look up subtree root
                return *subtree_map.get(path).unwrap_or(&DEAD);
            }
            let mut children = [DEAD; 4];
            for b in 0u32..4 {
                path.push(b);
                children[b as usize] = build_prefix_level(
                    depth + 1, max_depth, path, subtree_map, nodes,
                );
                path.pop();
            }
            // Reduce
            if children.iter().all(|&c| c == DEAD) { return DEAD; }
            let first = children[0];
            if children.iter().all(|&c| c == first) { return first; }
            let nid = nodes.len() as u32;
            nodes.push(children);
            nid
        }

        // Build level 1..parallel_depth nodes
        let mut path = Vec::new();
        let level1_root = build_prefix_level(0, parallel_depth, &mut path, &subtree_map, &mut merged_nodes);

        // Build level-0 node (symmetry: only branch 3 = 0b11)
        let mut level0_children = [DEAD; 4];
        level0_children[3] = level1_root;
        let mut root = merged_nodes.len() as u32;
        merged_nodes.push(level0_children);

        // Dedup pass: merge identical nodes across branches.
        // Bottom-up: walk nodes in reverse, hash each, and remap duplicates.
        let before_dedup = merged_nodes.len();
        {
            let mut canon: HashMap<[u32; 4], u32> = HashMap::default();
            let mut remap = vec![0u32; merged_nodes.len()];
            remap[0] = DEAD; // sentinel

            // Forward pass: identify canonical nodes
            let mut new_nodes: Vec<[u32; 4]> = Vec::with_capacity(merged_nodes.len());
            new_nodes.push([DEAD; 4]); // sentinel
            for old_id in 1..merged_nodes.len() {
                // Remap children first
                let mut ch = merged_nodes[old_id];
                for c in ch.iter_mut() {
                    if *c != DEAD && *c != LEAF {
                        *c = remap[*c as usize];
                    }
                }
                // Check for reduction (all children same)
                if ch.iter().all(|&c| c == DEAD) {
                    remap[old_id] = DEAD;
                } else {
                    let first = ch[0];
                    if ch.iter().all(|&c| c == first) {
                        remap[old_id] = first;
                    } else if let Some(&existing) = canon.get(&ch) {
                        remap[old_id] = existing;
                    } else {
                        let new_id = new_nodes.len() as u32;
                        new_nodes.push(ch);
                        canon.insert(ch, new_id);
                        remap[old_id] = new_id;
                    }
                }
            }
            // Remap root
            root = if root == DEAD || root == LEAF { root } else { remap[root as usize] };
            merged_nodes = new_nodes;
        }

        eprintln!("  Dedup: {} → {} nodes ({:.0}% reduction)",
            before_dedup, merged_nodes.len(),
            (1.0 - merged_nodes.len() as f64 / before_dedup as f64) * 100.0);

        let zw_depth = 2 * k;
        let total_depth = 4 * k;
        let mut pos_order: Vec<usize> = Vec::with_capacity(2 * k);
        for t in 0..k {
            pos_order.push(t);
            pos_order.push(2 * k - 1 - t);
        }

        eprintln!("ZW-first MDD k={} (parallel): {} nodes, {:.1} MB, {:.1?}",
            k, merged_nodes.len(), merged_nodes.len() as f64 * 16.0 / 1_048_576.0,
            start.elapsed());

        ZwFirstMdd {
            nodes: merged_nodes,
            root,
            k,
            zw_pos_order: pos_order.clone(),
            xy_pos_order: pos_order,
            zw_depth,
            total_depth,
        }
    }

    fn build_inner(k: usize, restrict_level1: Option<u32>, restrict_branches: Option<&[u32]>) -> (Self, BuildStats) {
        let zw_only = std::env::var("MDD_ZW_ONLY").is_ok();
        Self::build_inner_opts(k, restrict_level1, restrict_branches, zw_only)
    }

    fn build_inner_opts(k: usize, restrict_level1: Option<u32>, restrict_branches: Option<&[u32]>, zw_only: bool) -> (Self, BuildStats) {
        let mut stats = BuildStats::new(k);
        let zw_depth = 2 * k;
        let total_depth = 4 * k;

        // Position order (configurable via MDD_ORDER env var)
        let order_name = std::env::var("MDD_ORDER").unwrap_or_else(|_| "bounce".to_string());
        let mut pos_order: Vec<usize> = Vec::with_capacity(2 * k);
        match order_name.as_str() {
            "linear" => {
                for i in 0..2*k { pos_order.push(i); }
            }
            "reverse" => {
                for i in (0..2*k).rev() { pos_order.push(i); }
            }
            "prefix_first" => {
                for i in 0..k { pos_order.push(i); }
                for i in (k..2*k).rev() { pos_order.push(i); }
            }
            "inner_out" => {
                // Inner to outer (reverse bouncing)
                for t in (0..k).rev() {
                    pos_order.push(k - 1 - t);
                    pos_order.push(k + t);
                }
            }
            _ => {
                // Default bouncing order (outer to inner)
                for t in 0..k {
                    pos_order.push(t);
                    pos_order.push(2 * k - 1 - t);
                }
            }
        };

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
        // Flat array for position→index lookup (avoids HashMap in hot path)
        let zw_active_indices: Vec<Vec<usize>> = zw_active_at_level.iter()
            .map(|active| {
                let mut flat = vec![usize::MAX; 2 * k];
                for (i, &p) in active.iter().enumerate() { flat[p] = i; }
                flat
            }).collect();

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
        let xy_active_indices: Vec<Vec<usize>> = xy_active_at_level.iter()
            .map(|active| {
                let mut flat = vec![usize::MAX; 2 * k];
                for (i, &p) in active.iter().enumerate() { flat[p] = i; }
                flat
            }).collect();

        // Build context
        // Precomputed delta tables: delta[bits_a * 4 + bits_b] for each event
        // Z event: 2 * sign(bits_a & 1) * sign(bits_b & 1)
        // W event: 2 * sign((bits_a>>1) & 1) * sign((bits_b>>1) & 1)
        // XY event: sign(xa) * sign(xb) + sign(ya) * sign(yb)
        fn make_zw_delta(is_z: bool) -> [i8; 16] {
            let mut table = [0i8; 16];
            for a in 0u32..4 {
                for b in 0u32..4 {
                    let val = if is_z {
                        let za = if a & 1 == 1 { 1i32 } else { -1 };
                        let zb = if b & 1 == 1 { 1i32 } else { -1 };
                        2 * za * zb
                    } else {
                        let wa = if (a >> 1) & 1 == 1 { 1i32 } else { -1 };
                        let wb = if (b >> 1) & 1 == 1 { 1i32 } else { -1 };
                        2 * wa * wb
                    };
                    table[(a * 4 + b) as usize] = val as i8;
                }
            }
            table
        }
        fn make_xy_delta() -> [i8; 16] {
            let mut table = [0i8; 16];
            for a in 0u32..4 {
                for b in 0u32..4 {
                    let xa = if a & 1 == 1 { 1i32 } else { -1 };
                    let xb = if b & 1 == 1 { 1i32 } else { -1 };
                    let ya = if (a >> 1) & 1 == 1 { 1i32 } else { -1 };
                    let yb = if (b >> 1) & 1 == 1 { 1i32 } else { -1 };
                    table[(a * 4 + b) as usize] = (xa * xb + ya * yb) as i8;
                }
            }
            table
        }

        // Pre-resolve active indices into events: (lag_idx, idx_a, idx_b, delta_table)
        let zw_resolved_events: Vec<Vec<(usize, usize, usize, [i8; 16])>> =
            zw_events_at_level.iter().enumerate().map(|(level, evs)| {
                evs.iter().map(|(li, ev)| {
                    let idx_a = zw_active_indices[level][ev.pos_a];
                    let idx_b = zw_active_indices[level][ev.pos_b];
                    (*li, idx_a, idx_b, make_zw_delta(ev.is_z))
                }).collect()
            }).collect();
        let xy_resolved_events: Vec<Vec<(usize, usize, usize, [i8; 16])>> =
            xy_events_at_level.iter().enumerate().map(|(level, evs)| {
                evs.iter().map(|(li, ev)| {
                    let idx_a = xy_active_indices[level][ev.pos_a];
                    let idx_b = xy_active_indices[level][ev.pos_b];
                    (*li, idx_a, idx_b, make_xy_delta())
                }).collect()
            }).collect();

        struct Ctx {
            pos_order: Vec<usize>,
            zw_events_at_level: Vec<Vec<(usize, usize, usize, [i8; 16])>>, // (lag_idx, idx_a, idx_b, delta_table)
            xy_events_at_level: Vec<Vec<(usize, usize, usize, [i8; 16])>>,
            zw_lag_check_at_level: Vec<Vec<usize>>,
            xy_lag_check_at_level: Vec<Vec<usize>>,
            xy_max_abs: Vec<i32>,
            zw_max_remaining: Vec<Vec<i32>>,
            xy_max_remaining: Vec<Vec<i32>>,
            zw_active_at_level: Vec<Vec<usize>>,
            zw_active_indices: Vec<Vec<usize>>,  // flat array: pos → index
            xy_active_at_level: Vec<Vec<usize>>,
            xy_active_indices: Vec<Vec<usize>>,  // flat array: pos → index
            k: usize,
            zw_depth: usize,
            restrict_level1: Option<u32>,
            restrict_branches: Vec<(usize, u32)>, // (level, required_branch)
            zw_only: bool,  // If true, skip XY sub-MDD building (return LEAF at ZW boundary)
        }

        let ctx = Ctx {
            pos_order: pos_order.clone(),
            zw_events_at_level: zw_resolved_events,
            xy_events_at_level: xy_resolved_events,
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
            restrict_level1,
            restrict_branches: match restrict_branches {
                Some(branches) => branches.iter().enumerate()
                    .map(|(d, &b)| (d + 1, b)) // level 1, 2, ... (skip level 0 symmetry)
                    .collect(),
                None => Vec::new(),
            },
            zw_only,
        };

        let mut nodes: Vec<[u32; 4]> = Vec::new();
        nodes.push([DEAD; 4]); // node 0 = DEAD

        let mut unique: HashMap<u64, u32> = HashMap::default();

        let mut zw_memo: Vec<HashMap<StateKey, u32>> = (0..=zw_depth).map(|_| HashMap::default()).collect();
        let mut xy_memo: Vec<HashMap<StateKey, u32>> = (0..=zw_depth).map(|_| HashMap::default()).collect();

        // Build XY bottom half: given zw_sums (the target for each lag),
        // build a 4-way MDD for (x,y) that satisfies N_X(s)+N_Y(s) = -zw_sums[s].
        fn build_xy(
            level: usize,  // 0..2k within xy half
            sums: &mut Vec<i8>,  // partial N_X + N_Y at each lag
            active_bits: &[u8],
            zw_sums: &[i8],  // target: sums[li] must equal -zw_sums[li] at end
            ctx: &Ctx,
            nodes: &mut Vec<[u32; 4]>,
            unique: &mut HashMap<u64, u32>,
            memo: &mut Vec<HashMap<StateKey, u32>>,
            stats: &mut BuildStats,
        ) -> u32 {
            stats.xy_level_stats[level].0 += 1;
            if level == ctx.zw_depth {
                // Check all lags: N_X + N_Y = -zw_sums
                for li in 0..ctx.k {
                    if sums[li] != -zw_sums[li] { return DEAD; }
                }
                return LEAF;
            }

            let active = &ctx.xy_active_at_level[level];
            let n_active = active.len();
            let mut current_vals = [0u8; 32];
            if level > 0 {
                let prev_indices = &ctx.xy_active_indices[level - 1];
                for (i, &pos) in active.iter().enumerate() {
                    if pos != ctx.pos_order[level] {
                        let pi = prev_indices[pos];
                        if pi != usize::MAX {
                            current_vals[i] = active_bits[pi];
                        }
                    }
                }
            }

            let new_pos = ctx.pos_order[level];
            let new_idx = ctx.xy_active_indices[level][new_pos];

            let state_key = (pack_sums(sums), pack_active(&current_vals[..n_active]));
            if let Some(&cached) = memo[level].get(&state_key) {
                stats.xy_level_stats[level].1 += 1;
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

                // Process XY pair events at this level (pre-resolved indices + delta table)
                for &(lag_idx, idx_a, idx_b, ref delta) in &ctx.xy_events_at_level[level] {
                    let bits_a = current_vals[idx_a] as usize;
                    let bits_b = current_vals[idx_b] as usize;
                    sums[lag_idx] += delta[bits_a * 4 + bits_b];
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
                        level + 1, sums, &current_vals[..n_active], zw_sums,
                        ctx, nodes, unique, memo, stats,
                    );
                } else {
                    stats.xy_level_stats[level].2 += 1;
                }

                // Restore sums by subtracting deltas
                for &(lag_idx, idx_a, idx_b, ref delta) in &ctx.xy_events_at_level[level] {
                    let bits_a = current_vals[idx_a] as usize;
                    let bits_b = current_vals[idx_b] as usize;
                    sums[lag_idx] -= delta[bits_a * 4 + bits_b];
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
            active_bits: &[u8],
            ctx: &Ctx,
            nodes: &mut Vec<[u32; 4]>,
            unique: &mut HashMap<u64, u32>,
            zw_memo: &mut Vec<HashMap<StateKey, u32>>,
            xy_memo: &mut Vec<HashMap<StateKey, u32>>,
            xy_cache: &mut HashMap<u128, u32>,
            zw_memo_count: &mut usize,
            max_memo_entries: usize,
            per_level_cap: usize,
            stats: &mut BuildStats,
            status: &mut StatusLine,
        ) -> u32 {
            stats.zw_level_stats[level].0 += 1;
            status.tick(nodes.len(), *zw_memo_count, xy_cache.len());

            if level == ctx.zw_depth {
                // ZW half done.
                stats.zw_level_stats[level].3 += 1;

                if ctx.zw_only {
                    // ZW-only mode: check if any (x,y) can satisfy the constraint.
                    // Range + parity check: for each lag, |zw_val| <= max_xy and right parity.
                    for li in 0..ctx.k {
                        let zw_val = sums[li] as i32;
                        let max_xy = ctx.xy_max_abs[li];
                        if zw_val.abs() > max_xy { return DEAD; }
                        if (zw_val + max_xy) % 2 != 0 { return DEAD; }
                    }
                    return LEAF;
                }

                // Build XY sub-MDD for these zw_sums.
                // Check XY cache: same zw_sums → same XY sub-MDD root
                let sums_key = pack_sums(sums);
                if let Some(&cached_root) = xy_cache.get(&sums_key) {
                    return cached_root;
                }

                stats.xy_build_count += 1;
                let xy_start = std::time::Instant::now();
                // Clear xy_memo for each distinct zw_sums to prevent memory explosion.
                // Nodes are still shared via the `unique` table.
                for m in xy_memo.iter_mut() { m.clear(); }
                let zw_sums: Vec<i8> = sums.to_vec();
                let mut xy_sums = vec![0i8; ctx.k];
                let result = build_xy(
                    0, &mut xy_sums, &[], &zw_sums,
                    ctx, nodes, unique, xy_memo, stats,
                );
                stats.xy_build_ns += xy_start.elapsed().as_nanos() as u64;
                xy_cache.insert(sums_key, result);
                return result;
            }

            let active = &ctx.zw_active_at_level[level];
            let n_active = active.len();
            let mut current_vals = [0u8; 32];
            if level > 0 {
                let prev_indices = &ctx.zw_active_indices[level - 1];
                for (i, &pos) in active.iter().enumerate() {
                    if pos != ctx.pos_order[level] {
                        let pi = prev_indices[pos];
                        if pi != usize::MAX {
                            current_vals[i] = active_bits[pi];
                        }
                    }
                }
            }

            let new_pos = ctx.pos_order[level];
            let new_idx = ctx.zw_active_indices[level][new_pos];

            let state_key = (pack_sums(sums), pack_active(&current_vals[..n_active]));
            if let Some(&cached) = zw_memo[level].get(&state_key) {
                stats.zw_level_stats[level].1 += 1;
                return cached;
            }

            let mut children = [DEAD; 4];
            for branch in 0u32..4 {
                let z_val = (branch >> 0) & 1;
                let w_val = (branch >> 1) & 1;

                // Symmetry breaking: z[0]=w[0]=+1
                if new_pos == 0 && branch != 0b11 { continue; }

                // For parallel builds: restrict to specific branches at specified levels
                if let Some(target) = ctx.restrict_level1 {
                    if level == 1 && branch != target { continue; }
                }
                let mut skip = false;
                for &(rlevel, rbranch) in &ctx.restrict_branches {
                    if level == rlevel && branch != rbranch { skip = true; break; }
                }
                if skip { continue; }

                current_vals[new_idx] = branch as u8;

                // Process ZW pair events at this level (pre-resolved indices + delta table)
                for &(lag_idx, idx_a, idx_b, ref delta) in &ctx.zw_events_at_level[level] {
                    let bits_a = current_vals[idx_a] as usize;
                    let bits_b = current_vals[idx_b] as usize;
                    sums[lag_idx] += delta[bits_a * 4 + bits_b];
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
                        if (zw_val.abs() - zw_remaining) > max_xy { ok = false; break; }
                    }
                }

                if ok {
                    children[branch as usize] = build_zw(
                        level + 1, sums, &current_vals[..n_active],
                        ctx, nodes, unique, zw_memo, xy_memo, xy_cache,
                        zw_memo_count, max_memo_entries, per_level_cap,
                        stats, status,
                    );
                    if level == 1 {
                        eprint!("\r  ZW level 1 branch {}/4, {} nodes, zw_memo={}   ",
                            branch + 1, nodes.len(), *zw_memo_count);
                    }
                } else {
                    stats.zw_level_stats[level].2 += 1;
                }

                // Restore sums by subtracting deltas (avoids pack/unpack overhead)
                for &(lag_idx, idx_a, idx_b, ref delta) in &ctx.zw_events_at_level[level] {
                    let bits_a = current_vals[idx_a] as usize;
                    let bits_b = current_vals[idx_b] as usize;
                    sums[lag_idx] -= delta[bits_a * 4 + bits_b];
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
                stats.zw_memo_evictions += 1;
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

        // Budget memo: ~140 bytes/entry in FxHashMap.
        // When running as a parallel branch, use 1/N of the budget.
        let num_parallel = if restrict_branches.is_some() {
            4u32.pow(restrict_branches.unwrap().len() as u32) as usize
        } else if restrict_level1.is_some() { 4 } else { 1 };
        // Auto-detect: use ~50% of available RAM for memo, leave rest for nodes/etc.
        // Default ~80M entries. Override with MDD_MEMO_CAP env var.
        let auto_cap = {
            let total_bytes = std::fs::read_to_string("/proc/meminfo")
                .ok()
                .and_then(|s| {
                    s.lines()
                        .find(|l| l.starts_with("MemTotal:"))
                        .and_then(|l| l.split_whitespace().nth(1))
                        .and_then(|n| n.parse::<usize>().ok())
                        .map(|kb| kb * 1024)
                })
                .unwrap_or(16 * 1024 * 1024 * 1024); // fallback 16GB
            // Use 40% of total RAM for memo (140 bytes/entry)
            // Leave 60% for nodes, unique table, xy_cache, OS, etc.
            let memo_budget = total_bytes * 2 / 5;
            (memo_budget / 140).min(200_000_000) // cap at 200M entries
        };
        let total_memo_cap: usize = std::env::var("MDD_MEMO_CAP")
            .ok().and_then(|s| s.parse().ok())
            .unwrap_or(auto_cap);
        eprintln!("  Memo budget: {} entries ({:.1} GB) across {} parallel tasks",
            total_memo_cap, total_memo_cap as f64 * 140.0 / 1e9, num_parallel);
        let max_memo_entries: usize = total_memo_cap / num_parallel;
        let per_level_cap: usize = max_memo_entries / (zw_depth + 1);
        let mut zw_memo_count: usize = 0;
        let mut xy_cache: HashMap<u128, u32> = HashMap::default();

        let mut sums = vec![0i8; k];
        let mut status = StatusLine::new(k);
        let root = build_zw(
            0, &mut sums, &[],
            &ctx, &mut nodes, &mut unique, &mut zw_memo, &mut xy_memo, &mut xy_cache,
            &mut zw_memo_count, max_memo_entries, per_level_cap,
            &mut stats, &mut status,
        );
        eprintln!(); // newline after status line

        let zw_memo_entries: usize = zw_memo.iter().map(|m| m.len()).sum();
        let xy_memo_entries: usize = xy_memo.iter().map(|m| m.len()).sum();
        let zw_boundary_calls: u64 = stats.zw_level_stats[zw_depth].3;
        eprintln!("ZW-first MDD k={}: {} nodes, {:.1} MB (zw_memo={}, xy_memo={}, xy_cache={}/{} = {:.1}% hit)",
            k, nodes.len(), nodes.len() as f64 * 16.0 / 1_048_576.0,
            zw_memo_entries, xy_memo_entries, xy_cache.len(), zw_boundary_calls,
            if zw_boundary_calls > 0 { 100.0 * (1.0 - xy_cache.len() as f64 / zw_boundary_calls as f64) } else { 0.0 });

        // Report per-level memo sizes (only when profiling)
        if std::env::var("MDD_PROFILE").is_ok() {
            eprintln!("  ZW memo per level:");
            for (i, m) in zw_memo.iter().enumerate() {
                if m.len() > 0 {
                    eprintln!("    level {}: {} entries", i, m.len());
                }
            }
        }

        (ZwFirstMdd {
            nodes,
            root,
            k,
            zw_pos_order: pos_order.clone(),
            xy_pos_order: pos_order,
            zw_depth,
            total_depth: total_depth,
        }, stats)
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

/// Build a standalone XY sub-MDD for a given ZW boundary.
///
/// `zw_sums` are the partial autocorrelation sums from the ZW half.
/// The XY sub-MDD encodes all (x,y) boundary configurations that satisfy
/// N_X(s) + N_Y(s) = -zw_sums[s] for each lag s.
///
/// Returns (nodes, root) where nodes are 4-way children arrays.
/// This is the key API for runtime MDD extension: the main turyn program
/// can walk a prebuilt k=K MDD, extract zw_sums at each boundary, and
/// call this to build the XY constraint for that specific boundary.
pub fn build_xy_for_boundary(k: usize, zw_sums: &[i8]) -> (Vec<[u32; 4]>, u32) {
    assert_eq!(zw_sums.len(), k, "zw_sums must have k={} elements", k);

    let zw_depth = 2 * k;

    // Position order (bouncing)
    let mut pos_order: Vec<usize> = Vec::with_capacity(2 * k);
    for t in 0..k {
        pos_order.push(t);
        pos_order.push(2 * k - 1 - t);
    }
    let mut pos_to_level: Vec<usize> = vec![0; 2 * k];
    for (level, &pos) in pos_order.iter().enumerate() {
        pos_to_level[pos] = level;
    }

    // XY lag pairs
    struct LagPairs {
        xy_pairs: Vec<(usize, usize)>,
    }
    let mut lags: Vec<LagPairs> = Vec::new();
    for j in 0..k {
        let xy_pairs: Vec<(usize, usize)> = (0..k - j)
            .map(|i| (i, k + i + j)).collect();
        lags.push(LagPairs { xy_pairs });
    }

    // XY events at each level
    struct LagEvent {
        pos_a: usize,
        pos_b: usize,
    }
    let mut xy_events_at_level: Vec<Vec<(usize, LagEvent)>> =
        (0..zw_depth).map(|_| Vec::new()).collect();
    let mut xy_lag_check_at_level: Vec<Vec<usize>> =
        (0..=zw_depth).map(|_| Vec::new()).collect();

    for (li, lag) in lags.iter().enumerate() {
        let mut xy_complete = 0usize;
        for &(a, b) in &lag.xy_pairs {
            let complete = pos_to_level[a].max(pos_to_level[b]);
            xy_events_at_level[complete].push((li, LagEvent { pos_a: a, pos_b: b }));
            xy_complete = xy_complete.max(complete);
        }
        xy_lag_check_at_level[xy_complete].push(li);
    }

    // Max remaining for range pruning
    let mut xy_max_remaining: Vec<Vec<i32>> = vec![vec![0i32; k]; zw_depth + 1];
    for (li, lag) in lags.iter().enumerate() {
        for &(a, b) in &lag.xy_pairs {
            let complete = pos_to_level[a].max(pos_to_level[b]);
            for level in 0..=complete { xy_max_remaining[level][li] += 2; }
        }
    }

    // Active position tracking
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
    let xy_active_indices: Vec<Vec<usize>> = xy_active_at_level.iter()
        .map(|active| {
            let mut flat = vec![usize::MAX; 2 * k];
            for (i, &p) in active.iter().enumerate() { flat[p] = i; }
            flat
        }).collect();

    // Precompute delta table
    let mut xy_delta = [0i8; 16];
    for a in 0u32..4 {
        for b in 0u32..4 {
            let xa = if a & 1 == 1 { 1i32 } else { -1 };
            let xb = if b & 1 == 1 { 1i32 } else { -1 };
            let ya = if (a >> 1) & 1 == 1 { 1i32 } else { -1 };
            let yb = if (b >> 1) & 1 == 1 { 1i32 } else { -1 };
            xy_delta[(a * 4 + b) as usize] = (xa * xb + ya * yb) as i8;
        }
    }

    // Pre-resolve events
    let resolved_events: Vec<Vec<(usize, usize, usize, [i8; 16])>> =
        xy_events_at_level.iter().enumerate().map(|(level, evs)| {
            evs.iter().map(|(li, ev)| {
                let idx_a = xy_active_indices[level][ev.pos_a];
                let idx_b = xy_active_indices[level][ev.pos_b];
                (*li, idx_a, idx_b, xy_delta)
            }).collect()
        }).collect();

    let mut nodes: Vec<[u32; 4]> = Vec::new();
    nodes.push([DEAD; 4]); // sentinel
    let mut unique: HashMap<u64, u32> = HashMap::default();
    let mut memo: Vec<HashMap<StateKey, u32>> = (0..=zw_depth).map(|_| HashMap::default()).collect();

    struct XyCtx {
        pos_order: Vec<usize>,
        events: Vec<Vec<(usize, usize, usize, [i8; 16])>>,
        lag_check: Vec<Vec<usize>>,
        max_remaining: Vec<Vec<i32>>,
        active_at_level: Vec<Vec<usize>>,
        active_indices: Vec<Vec<usize>>,
        k: usize,
        zw_depth: usize,
    }

    let ctx = XyCtx {
        pos_order,
        events: resolved_events,
        lag_check: xy_lag_check_at_level,
        max_remaining: xy_max_remaining,
        active_at_level: xy_active_at_level,
        active_indices: xy_active_indices,
        k,
        zw_depth,
    };

    fn build(
        level: usize,
        sums: &mut [i8],
        active_bits: &[u8],
        zw_sums: &[i8],
        ctx: &XyCtx,
        nodes: &mut Vec<[u32; 4]>,
        unique: &mut HashMap<u64, u32>,
        memo: &mut Vec<HashMap<StateKey, u32>>,
    ) -> u32 {
        if level == ctx.zw_depth {
            for li in 0..ctx.k {
                if sums[li] != -zw_sums[li] { return DEAD; }
            }
            return LEAF;
        }

        let active = &ctx.active_at_level[level];
        let n_active = active.len();
        let mut current_vals = [0u8; 32];
        if level > 0 {
            let prev_indices = &ctx.active_indices[level - 1];
            for (i, &pos) in active.iter().enumerate() {
                if pos != ctx.pos_order[level] {
                    let pi = prev_indices[pos];
                    if pi != usize::MAX {
                        current_vals[i] = active_bits[pi];
                    }
                }
            }
        }

        let new_pos = ctx.pos_order[level];
        let new_idx = ctx.active_indices[level][new_pos];

        let state_key = (pack_sums(sums), pack_active(&current_vals[..n_active]));
        if let Some(&cached) = memo[level].get(&state_key) {
            return cached;
        }

        let mut children = [DEAD; 4];
        for branch in 0u32..4 {
            if new_pos == 0 && branch != 0b11 { continue; }
            current_vals[new_idx] = branch as u8;

            for &(lag_idx, idx_a, idx_b, ref delta) in &ctx.events[level] {
                let bits_a = current_vals[idx_a] as usize;
                let bits_b = current_vals[idx_b] as usize;
                sums[lag_idx] += delta[bits_a * 4 + bits_b];
            }

            let mut ok = true;
            for &li in &ctx.lag_check[level] {
                if sums[li] != -zw_sums[li] { ok = false; break; }
            }
            if ok && level + 1 < ctx.zw_depth {
                for li in 0..ctx.k {
                    let gap = (sums[li] as i32) - (-(zw_sums[li] as i32));
                    let remaining = ctx.max_remaining[level + 1][li];
                    if gap.abs() > remaining { ok = false; break; }
                }
            }

            if ok {
                children[branch as usize] = build(
                    level + 1, sums, &current_vals[..n_active], zw_sums,
                    ctx, nodes, unique, memo,
                );
            }

            // Restore sums
            for &(lag_idx, idx_a, idx_b, ref delta) in &ctx.events[level] {
                let bits_a = current_vals[idx_a] as usize;
                let bits_b = current_vals[idx_b] as usize;
                sums[lag_idx] -= delta[bits_a * 4 + bits_b];
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

        memo[level].insert(state_key, result);
        result
    }

    let mut sums = vec![0i8; k];
    let root = build(
        0, &mut sums, &[], zw_sums,
        &ctx, &mut nodes, &mut unique, &mut memo,
    );

    (nodes, root)
}

/// Build an MDD that extends a k=base_k boundary to k=target_k.
///
/// Given concrete boundary values (z_bits, w_bits, x_bits, y_bits) from a
/// base_k-sized MDD, this builds an MDD over the *extension* positions only
/// (positions base_k..target_k-1 in the "short" halves and their corresponding
/// "long" counterparts).
///
/// The lag structure: lag j pairs position i with position (k + i + j) for Z/X,
/// and position i with position (k + i + j + 1) for W/Y. When extending from
/// base_k to target_k, we get three kinds of autocorrelation terms:
///   1. Old×Old: fully determined by the base boundary bits (frozen, becomes initial sums)
///   2. Old×New: one factor is known, the other is a new variable (cross-terms)
///   3. New×New: both factors are new variables
///
/// The extension MDD branches on the new positions and tracks partial sums that
/// include contributions from cross-terms (using the known old bit values) and
/// new×new terms. At the end, all sums must be zero.
///
/// Returns a ZwFirstMdd over the extension positions.
pub fn build_extension(
    base_k: usize,
    target_k: usize,
    z_bits: u32,
    w_bits: u32,
    x_bits: u32,
    y_bits: u32,
) -> (Vec<[u32; 4]>, u32) {
    assert!(target_k > base_k, "target_k must be > base_k");
    let extra = target_k - base_k;

    // Compute initial sums from old×old pairs (these are fixed)
    let mut initial_sums = vec![0i8; target_k];
    for j in 0..target_k {
        let mut sum = 0i32;

        // Z old×old pairs: lag j, positions (i, base_k + i + j)
        // Only pairs where BOTH positions are in 0..2*base_k
        for i in 0..base_k {
            let pos_b = base_k + i + j;
            if pos_b < 2 * base_k {
                let za = if (z_bits >> i) & 1 == 1 { 1 } else { -1i32 };
                let zb = if (z_bits >> pos_b) & 1 == 1 { 1 } else { -1i32 };
                sum += 2 * za * zb;
            }
        }
        // W old×old pairs: lag j, positions (i, base_k + i + j + 1)
        if j < target_k - 1 {
            for i in 0..base_k {
                let pos_b = base_k + i + j + 1;
                if pos_b < 2 * base_k {
                    let wa = if (w_bits >> i) & 1 == 1 { 1 } else { -1i32 };
                    let wb = if (w_bits >> pos_b) & 1 == 1 { 1 } else { -1i32 };
                    sum += 2 * wa * wb;
                }
            }
        }
        // X old×old pairs
        for i in 0..base_k {
            let pos_b = base_k + i + j;
            if pos_b < 2 * base_k {
                let xa = if (x_bits >> i) & 1 == 1 { 1 } else { -1i32 };
                let xb = if (x_bits >> pos_b) & 1 == 1 { 1 } else { -1i32 };
                sum += xa * xb;
            }
        }
        // Y old×old pairs
        for i in 0..base_k {
            let pos_b = base_k + i + j;
            if pos_b < 2 * base_k {
                let ya = if (y_bits >> i) & 1 == 1 { 1 } else { -1i32 };
                let yb = if (y_bits >> pos_b) & 1 == 1 { 1 } else { -1i32 };
                sum += ya * yb;
            }
        }

        initial_sums[j] = sum as i8;
    }

    // Now build an MDD for the extension positions.
    // The extension has 2*extra positions per sequence (extra "short" + extra "long").
    // We interleave all 4 sequences: each level assigns (z,w,x,y) at a new position.
    // But to match the ZW-first structure, we do ZW first, then XY.

    let ext_depth = 2 * extra;  // positions per half-sequence

    // Position mapping: extension position p maps to actual position (base_k + p)
    // in the full sequence. The "short" half uses positions 0..extra-1,
    // the "long" half uses positions extra..2*extra-1.

    // Build position order (bouncing within extension)
    let mut pos_order: Vec<usize> = Vec::with_capacity(ext_depth);
    for t in 0..extra {
        pos_order.push(t);
        pos_order.push(2 * extra - 1 - t);
    }
    let mut pos_to_level: Vec<usize> = vec![0; ext_depth];
    for (level, &pos) in pos_order.iter().enumerate() {
        pos_to_level[pos] = level;
    }

    // Events: for each lag j, determine which pairs involve extension positions.
    // A pair (i, base_k+i+j) where i or base_k+i+j is in the extension range.
    //
    // Extension positions in the full sequence:
    //   Short half: base_k..base_k+extra-1  (ext pos 0..extra-1)
    //   Long half:  base_k+extra..2*target_k-1  (ext pos extra..2*extra-1)
    //
    // Actually: the full sequence has 2*target_k positions. Positions 0..target_k-1
    // are "short", positions target_k..2*target_k-1 are "long".
    // Old positions: 0..base_k-1 (short) and target_k..target_k+base_k-1 (long)
    // New positions: base_k..target_k-1 (short) and target_k+base_k..2*target_k-1 (long)
    //
    // In the extension MDD, we number new positions 0..2*extra-1:
    //   0..extra-1 = actual positions base_k..target_k-1 (new short)
    //   extra..2*extra-1 = actual positions target_k+base_k..2*target_k-1 (new long)

    // For each lag j, collect events involving at least one new position.
    // Each event: which ext positions are involved, and if one is old, what's the known value.
    struct ExtEvent {
        lag: usize,
        // If both positions are new: ext_a and ext_b are extension positions
        // If one is old: ext_new is the extension position, old_sign is the known ±1 value
        kind: ExtEventKind,
    }
    enum ExtEventKind {
        // Both positions are new extension positions
        NewNew { ext_a: usize, ext_b: usize, is_z: bool },
        // One position is old (known sign), one is new
        OldNew { ext_new: usize, old_sign_z: i8, old_sign_w: i8, old_sign_x: i8, old_sign_y: i8 },
    }

    let mut events_at_level: Vec<Vec<ExtEvent>> = (0..ext_depth).map(|_| Vec::new()).collect();
    let mut lag_check_at_level: Vec<Vec<usize>> = (0..=ext_depth).map(|_| Vec::new()).collect();
    let mut max_remaining: Vec<Vec<i32>> = vec![vec![0i32; target_k]; ext_depth + 1];

    for j in 0..target_k {
        let mut max_complete_level: Option<usize> = None;

        // Z/X pairs: (i, target_k + i + j) for i in 0..target_k-j
        for i in 0..target_k.saturating_sub(j) {
            let actual_a = i;
            let actual_b = target_k + i + j;
            if actual_b >= 2 * target_k { continue; }

            let a_is_new = actual_a >= base_k && actual_a < target_k;
            let b_is_new = actual_b >= target_k + base_k;

            if !a_is_new && !b_is_new {
                continue; // old×old: already in initial_sums
            }

            let ext_a = if a_is_new { Some(actual_a - base_k) } else { None };
            let ext_b = if b_is_new { Some(extra + (actual_b - target_k - base_k)) } else { None };

            // Determine when this event completes (both positions assigned)
            let complete_level = match (ext_a, ext_b) {
                (Some(ea), Some(eb)) => pos_to_level[ea].max(pos_to_level[eb]),
                (Some(ea), None) => pos_to_level[ea],
                (None, Some(eb)) => pos_to_level[eb],
                (None, None) => unreachable!(),
            };

            let event = match (ext_a, ext_b) {
                (Some(ea), Some(eb)) => ExtEvent {
                    lag: j,
                    kind: ExtEventKind::NewNew { ext_a: ea, ext_b: eb, is_z: true },
                },
                (Some(en), None) => {
                    // b is old position
                    let zb = if (z_bits >> actual_b) & 1 == 1 { 1i8 } else { -1 };
                    let xb = if (x_bits >> actual_b) & 1 == 1 { 1i8 } else { -1 };
                    ExtEvent {
                        lag: j,
                        kind: ExtEventKind::OldNew { ext_new: en, old_sign_z: zb, old_sign_w: 0, old_sign_x: xb, old_sign_y: 0 },
                    }
                },
                (None, Some(en)) => {
                    // a is old position
                    let za = if (z_bits >> actual_a) & 1 == 1 { 1i8 } else { -1 };
                    let xa = if (x_bits >> actual_a) & 1 == 1 { 1i8 } else { -1 };
                    ExtEvent {
                        lag: j,
                        kind: ExtEventKind::OldNew { ext_new: en, old_sign_z: za, old_sign_w: 0, old_sign_x: xa, old_sign_y: 0 },
                    }
                },
                _ => unreachable!(),
            };

            // Track max contribution for pruning
            for lv in 0..=complete_level {
                max_remaining[lv][j] += 4; // max |delta| per event (2 for Z + 2 for X)
            }

            events_at_level[complete_level].push(event);
            max_complete_level = Some(max_complete_level.map_or(complete_level, |c: usize| c.max(complete_level)));
        }

        // W/Y pairs: (i, target_k + i + j + 1) for i in 0..target_k-j-1
        if j < target_k - 1 {
            for i in 0..target_k - j - 1 {
                let actual_a = i;
                let actual_b = target_k + i + j + 1;
                if actual_b >= 2 * target_k { continue; }

                let a_is_new = actual_a >= base_k && actual_a < target_k;
                let b_is_new = actual_b >= target_k + base_k;

                if !a_is_new && !b_is_new {
                    continue; // old×old
                }

                let ext_a = if a_is_new { Some(actual_a - base_k) } else { None };
                let ext_b = if b_is_new { Some(extra + (actual_b - target_k - base_k)) } else { None };

                let complete_level = match (ext_a, ext_b) {
                    (Some(ea), Some(eb)) => pos_to_level[ea].max(pos_to_level[eb]),
                    (Some(ea), None) => pos_to_level[ea],
                    (None, Some(eb)) => pos_to_level[eb],
                    (None, None) => unreachable!(),
                };

                let event = match (ext_a, ext_b) {
                    (Some(ea), Some(eb)) => ExtEvent {
                        lag: j,
                        kind: ExtEventKind::NewNew { ext_a: ea, ext_b: eb, is_z: false },
                    },
                    (Some(en), None) => {
                        let wb = if (w_bits >> actual_b) & 1 == 1 { 1i8 } else { -1 };
                        let yb = if (y_bits >> actual_b) & 1 == 1 { 1i8 } else { -1 };
                        ExtEvent {
                            lag: j,
                            kind: ExtEventKind::OldNew { ext_new: en, old_sign_z: 0, old_sign_w: wb, old_sign_x: 0, old_sign_y: yb },
                        }
                    },
                    (None, Some(en)) => {
                        let wa = if (w_bits >> actual_a) & 1 == 1 { 1i8 } else { -1 };
                        let ya = if (y_bits >> actual_a) & 1 == 1 { 1i8 } else { -1 };
                        ExtEvent {
                            lag: j,
                            kind: ExtEventKind::OldNew { ext_new: en, old_sign_z: 0, old_sign_w: wa, old_sign_x: 0, old_sign_y: ya },
                        }
                    },
                    _ => unreachable!(),
                };

                for lv in 0..=complete_level {
                    max_remaining[lv][j] += 4;
                }

                events_at_level[complete_level].push(event);
                max_complete_level = Some(max_complete_level.map_or(complete_level, |c: usize| c.max(complete_level)));
            }
        }

        if let Some(cl) = max_complete_level {
            lag_check_at_level[cl].push(j);
        }
    }

    // Build XY events separately (for the second half of the extension).
    // XY pairs: (i, target_k+i+j) for X and Y, using new positions.
    let mut xy_events_at_level: Vec<Vec<ExtEvent>> = (0..ext_depth).map(|_| Vec::new()).collect();
    let mut xy_lag_check_at_level: Vec<Vec<usize>> = (0..=ext_depth).map(|_| Vec::new()).collect();
    let mut xy_max_remaining: Vec<Vec<i32>> = vec![vec![0i32; target_k]; ext_depth + 1];

    for j in 0..target_k {
        let mut max_complete_level: Option<usize> = None;

        // X/Y pairs: (i, target_k + i + j)
        for i in 0..target_k.saturating_sub(j) {
            let actual_a = i;
            let actual_b = target_k + i + j;
            if actual_b >= 2 * target_k { continue; }

            let a_is_new = actual_a >= base_k && actual_a < target_k;
            let b_is_new = actual_b >= target_k + base_k;

            if !a_is_new && !b_is_new { continue; }

            let ext_a = if a_is_new { Some(actual_a - base_k) } else { None };
            let ext_b = if b_is_new { Some(extra + (actual_b - target_k - base_k)) } else { None };

            let complete_level = match (ext_a, ext_b) {
                (Some(ea), Some(eb)) => pos_to_level[ea].max(pos_to_level[eb]),
                (Some(ea), None) => pos_to_level[ea],
                (None, Some(eb)) => pos_to_level[eb],
                (None, None) => unreachable!(),
            };

            let event = match (ext_a, ext_b) {
                (Some(ea), Some(eb)) => ExtEvent {
                    lag: j,
                    kind: ExtEventKind::NewNew { ext_a: ea, ext_b: eb, is_z: true }, // is_z used as "is_x" here
                },
                (Some(en), None) => {
                    let xb = if (x_bits >> actual_b) & 1 == 1 { 1i8 } else { -1 };
                    let yb = if (y_bits >> actual_b) & 1 == 1 { 1i8 } else { -1 };
                    ExtEvent { lag: j, kind: ExtEventKind::OldNew {
                        ext_new: en, old_sign_z: xb, old_sign_w: yb, old_sign_x: 0, old_sign_y: 0,
                    }}
                },
                (None, Some(en)) => {
                    let xa = if (x_bits >> actual_a) & 1 == 1 { 1i8 } else { -1 };
                    let ya = if (y_bits >> actual_a) & 1 == 1 { 1i8 } else { -1 };
                    ExtEvent { lag: j, kind: ExtEventKind::OldNew {
                        ext_new: en, old_sign_z: xa, old_sign_w: ya, old_sign_x: 0, old_sign_y: 0,
                    }}
                },
                _ => unreachable!(),
            };

            for lv in 0..=complete_level { xy_max_remaining[lv][j] += 2; }
            xy_events_at_level[complete_level].push(event);
            max_complete_level = Some(max_complete_level.map_or(complete_level, |c: usize| c.max(complete_level)));
        }

        if let Some(cl) = max_complete_level {
            xy_lag_check_at_level[cl].push(j);
        }
    }

    // Compute total XY max achievable for range pruning at ZW boundary
    let xy_max_abs: Vec<i32> = (0..target_k).map(|j| xy_max_remaining[0][j]).collect();

    // Active position tracking (same for both ZW and XY halves — same positions)
    let mut last_use: Vec<usize> = vec![0; ext_depth];
    for (level, evs) in events_at_level.iter().chain(xy_events_at_level.iter()).enumerate() {
        let l = level % ext_depth; // events_at_level and xy_events_at_level use same position indices
        for ev in evs {
            match &ev.kind {
                ExtEventKind::NewNew { ext_a, ext_b, .. } => {
                    last_use[*ext_a] = last_use[*ext_a].max(l);
                    last_use[*ext_b] = last_use[*ext_b].max(l);
                }
                ExtEventKind::OldNew { ext_new, .. } => {
                    last_use[*ext_new] = last_use[*ext_new].max(l);
                }
            }
        }
    }
    let mut active_at_level: Vec<Vec<usize>> = vec![Vec::new(); ext_depth + 1];
    for d in 0..ext_depth {
        let mut active: Vec<usize> = if d > 0 {
            active_at_level[d - 1].iter().filter(|&&p| last_use[p] >= d).copied().collect()
        } else { Vec::new() };
        active.push(pos_order[d]);
        active.sort();
        active_at_level[d] = active;
    }
    let active_indices: Vec<Vec<usize>> = active_at_level.iter()
        .map(|active| {
            let mut flat = vec![usize::MAX; ext_depth];
            for (i, &p) in active.iter().enumerate() { flat[p] = i; }
            flat
        }).collect();

    // Resolve ZW events into delta tables
    fn make_zw_delta(is_z: bool) -> [i8; 16] {
        let mut t = [0i8; 16];
        for a in 0u32..4 { for b in 0u32..4 {
            t[(a*4+b) as usize] = if is_z {
                let za = if a&1==1 {1i32} else {-1}; let zb = if b&1==1 {1} else {-1}; (2*za*zb) as i8
            } else {
                let wa = if (a>>1)&1==1 {1i32} else {-1}; let wb = if (b>>1)&1==1 {1} else {-1}; (2*wa*wb) as i8
            };
        }} t
    }
    fn make_xy_delta() -> [i8; 16] {
        let mut t = [0i8; 16];
        for a in 0u32..4 { for b in 0u32..4 {
            let xa = if a&1==1 {1i32} else {-1}; let xb = if b&1==1 {1} else {-1};
            let ya = if (a>>1)&1==1 {1i32} else {-1}; let yb = if (b>>1)&1==1 {1} else {-1};
            t[(a*4+b) as usize] = (xa*xb + ya*yb) as i8;
        }} t
    }

    let zw_resolved: Vec<Vec<(usize, usize, usize, [i8; 16])>> = events_at_level.iter().enumerate().map(|(level, evs)| {
        evs.iter().map(|ev| {
            match &ev.kind {
                ExtEventKind::NewNew { ext_a, ext_b, is_z } => {
                    (ev.lag, active_indices[level][*ext_a], active_indices[level][*ext_b], make_zw_delta(*is_z))
                }
                ExtEventKind::OldNew { ext_new, old_sign_z, old_sign_w, .. } => {
                    let idx = active_indices[level][*ext_new];
                    let mut delta = [0i8; 16];
                    for a in 0u32..4 { for b in 0u32..4 {
                        let nz = if a&1==1 {1i32} else {-1};
                        let nw = if (a>>1)&1==1 {1i32} else {-1};
                        delta[(a*4+b) as usize] = (2*(*old_sign_z as i32)*nz + 2*(*old_sign_w as i32)*nw) as i8;
                    }}
                    (ev.lag, idx, idx, delta)
                }
            }
        }).collect()
    }).collect();

    let xy_resolved: Vec<Vec<(usize, usize, usize, [i8; 16])>> = xy_events_at_level.iter().enumerate().map(|(level, evs)| {
        evs.iter().map(|ev| {
            match &ev.kind {
                ExtEventKind::NewNew { ext_a, ext_b, .. } => {
                    (ev.lag, active_indices[level][*ext_a], active_indices[level][*ext_b], make_xy_delta())
                }
                ExtEventKind::OldNew { ext_new, old_sign_z: old_x, old_sign_w: old_y, .. } => {
                    // old_sign_z/w are repurposed as old_x/old_y for XY events
                    let idx = active_indices[level][*ext_new];
                    let mut delta = [0i8; 16];
                    for a in 0u32..4 { for b in 0u32..4 {
                        let nx = if a&1==1 {1i32} else {-1};
                        let ny = if (a>>1)&1==1 {1i32} else {-1};
                        delta[(a*4+b) as usize] = ((*old_x as i32)*nx + (*old_y as i32)*ny) as i8;
                    }}
                    (ev.lag, idx, idx, delta)
                }
            }
        }).collect()
    }).collect();

    // DFS builder: ZW half (levels 0..ext_depth) then XY half (levels ext_depth..2*ext_depth)
    let mut nodes: Vec<[u32; 4]> = Vec::new();
    nodes.push([DEAD; 4]);
    let mut unique: HashMap<u64, u32> = HashMap::default();
    let mut zw_memo: Vec<HashMap<StateKey, u32>> = (0..=ext_depth).map(|_| HashMap::default()).collect();
    let mut xy_memo: Vec<HashMap<StateKey, u32>> = (0..=ext_depth).map(|_| HashMap::default()).collect();

    // XY half DFS
    fn build_xy_ext(
        level: usize, sums: &mut [i8], active_bits: &[u8], target_k: usize,
        ext_depth: usize, pos_order: &[usize],
        active_at_level: &[Vec<usize>], active_indices: &[Vec<usize>],
        events: &[Vec<(usize, usize, usize, [i8; 16])>],
        lag_check: &[Vec<usize>], max_remaining: &[Vec<i32>],
        nodes: &mut Vec<[u32; 4]>, unique: &mut HashMap<u64, u32>,
        memo: &mut Vec<HashMap<StateKey, u32>>,
    ) -> u32 {
        if level == ext_depth {
            for li in 0..target_k { if sums[li] != 0 { return DEAD; } }
            return LEAF;
        }
        let active = &active_at_level[level];
        let n_active = active.len();
        let mut cv = [0u8; 32];
        if level > 0 {
            let pi = &active_indices[level - 1];
            for (i, &pos) in active.iter().enumerate() {
                if pos != pos_order[level] { let p = pi[pos]; if p != usize::MAX { cv[i] = active_bits[p]; } }
            }
        }
        let new_idx = active_indices[level][pos_order[level]];
        let sk = (pack_sums(sums), pack_active(&cv[..n_active]));
        if let Some(&c) = memo[level].get(&sk) { return c; }

        let mut children = [DEAD; 4];
        for branch in 0u32..4 {
            // No symmetry breaking in extension — base already handles it
            cv[new_idx] = branch as u8;
            for &(li, ia, ib, ref d) in &events[level] {
                sums[li] += d[cv[ia] as usize * 4 + cv[ib] as usize];
            }
            let mut ok = true;
            for &li in &lag_check[level] { if sums[li] != 0 { ok = false; break; } }
            if ok && level + 1 < ext_depth {
                for li in 0..target_k {
                    if (sums[li] as i32).abs() > max_remaining[level+1][li] { ok = false; break; }
                }
            }
            if ok {
                children[branch as usize] = build_xy_ext(
                    level+1, sums, &cv[..n_active], target_k, ext_depth, pos_order,
                    active_at_level, active_indices, events, lag_check, max_remaining,
                    nodes, unique, memo,
                );
            }
            for &(li, ia, ib, ref d) in &events[level] {
                sums[li] -= d[cv[ia] as usize * 4 + cv[ib] as usize];
            }
        }
        let result = if children.iter().all(|&c| c == DEAD) { DEAD }
        else {
            let first = children[0];
            if children.iter().all(|&c| c == first) { first }
            else {
                let key = hash_node4((ext_depth + level) as u8, &children);
                if let Some(&nid) = unique.get(&key) { nid }
                else { let nid = nodes.len() as u32; nodes.push(children); unique.insert(key, nid); nid }
            }
        };
        memo[level].insert(sk, result);
        result
    }

    // ZW half DFS
    fn build_zw_ext(
        level: usize, sums: &mut [i8], active_bits: &[u8], target_k: usize,
        ext_depth: usize, pos_order: &[usize], xy_max_abs: &[i32],
        active_at_level: &[Vec<usize>], active_indices: &[Vec<usize>],
        zw_events: &[Vec<(usize, usize, usize, [i8; 16])>],
        zw_lag_check: &[Vec<usize>], zw_max_remaining: &[Vec<i32>],
        xy_events: &[Vec<(usize, usize, usize, [i8; 16])>],
        xy_lag_check: &[Vec<usize>], xy_max_remaining_arr: &[Vec<i32>],
        nodes: &mut Vec<[u32; 4]>, unique: &mut HashMap<u64, u32>,
        zw_memo: &mut Vec<HashMap<StateKey, u32>>,
        xy_memo: &mut Vec<HashMap<StateKey, u32>>,
    ) -> u32 {
        if level == ext_depth {
            // ZW done. Check XY feasibility, then build XY half.
            for li in 0..target_k {
                let zw_val = sums[li] as i32;
                if zw_val.abs() > xy_max_abs[li] { return DEAD; }
                if (zw_val + xy_max_abs[li]) % 2 != 0 { return DEAD; }
            }
            // Build XY sub-MDD. Target: sums[li] must reach 0 after XY events.
            for m in xy_memo.iter_mut() { m.clear(); }
            return build_xy_ext(
                0, sums, &[], target_k, ext_depth, pos_order,
                active_at_level, active_indices, xy_events, xy_lag_check, xy_max_remaining_arr,
                nodes, unique, xy_memo,
            );
        }
        let active = &active_at_level[level];
        let n_active = active.len();
        let mut cv = [0u8; 32];
        if level > 0 {
            let pi = &active_indices[level - 1];
            for (i, &pos) in active.iter().enumerate() {
                if pos != pos_order[level] { let p = pi[pos]; if p != usize::MAX { cv[i] = active_bits[p]; } }
            }
        }
        let new_idx = active_indices[level][pos_order[level]];
        let sk = (pack_sums(sums), pack_active(&cv[..n_active]));
        if let Some(&c) = zw_memo[level].get(&sk) { return c; }

        let mut children = [DEAD; 4];
        for branch in 0u32..4 {
            // No symmetry breaking in extension — base already handles it
            cv[new_idx] = branch as u8;
            for &(li, ia, ib, ref d) in &zw_events[level] {
                sums[li] += d[cv[ia] as usize * 4 + cv[ib] as usize];
            }
            let mut ok = true;
            for &li in &zw_lag_check[level] {
                let v = sums[li] as i32;
                if v.abs() > xy_max_abs[li] { ok = false; break; }
            }
            if ok && level + 1 < ext_depth {
                for li in 0..target_k {
                    let v = sums[li] as i32;
                    let rem = zw_max_remaining[level+1][li];
                    if (v.abs() - rem) > xy_max_abs[li] { ok = false; break; }
                }
            }
            if ok {
                children[branch as usize] = build_zw_ext(
                    level+1, sums, &cv[..n_active], target_k, ext_depth, pos_order, xy_max_abs,
                    active_at_level, active_indices, zw_events, zw_lag_check, zw_max_remaining,
                    xy_events, xy_lag_check, xy_max_remaining_arr,
                    nodes, unique, zw_memo, xy_memo,
                );
            }
            for &(li, ia, ib, ref d) in &zw_events[level] {
                sums[li] -= d[cv[ia] as usize * 4 + cv[ib] as usize];
            }
        }
        let result = if children.iter().all(|&c| c == DEAD) { DEAD }
        else {
            let first = children[0];
            if children.iter().all(|&c| c == first) { first }
            else {
                let key = hash_node4(level as u8, &children);
                if let Some(&nid) = unique.get(&key) { nid }
                else { let nid = nodes.len() as u32; nodes.push(children); unique.insert(key, nid); nid }
            }
        };
        zw_memo[level].insert(sk, result);
        result
    }

    let mut sums = initial_sums;
    let root = build_zw_ext(
        0, &mut sums, &[], target_k, ext_depth, &pos_order, &xy_max_abs,
        &active_at_level, &active_indices,
        &zw_resolved, &lag_check_at_level, &max_remaining,
        &xy_resolved, &xy_lag_check_at_level, &xy_max_remaining,
        &mut nodes, &mut unique, &mut zw_memo, &mut xy_memo,
    );

    eprintln!("build_extension: base_k={}, target_k={}, extra={}, {} nodes, root={}",
        base_k, target_k, extra, nodes.len(),
        if root == DEAD { "DEAD".to_string() } else if root == LEAF { "LEAF".to_string() } else { root.to_string() });

    (nodes, root)
}
