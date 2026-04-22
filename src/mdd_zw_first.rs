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

/// Memo key used by `build_zw_dfs` and `build_xy_dfs`.  Extends `StateKey`
/// with a `u8` of per-rule "has this BDKR canonical rule already fired?"
/// bits so that two subtrees with identical `(sums, active_bits)` but
/// different firing histories aren't incorrectly memoized to the same node.
///
/// Bit layout depends on which half we're in (see BDKR_RULE_* constants):
///   ZW build: bit 0 = rule (iv) fired on Z, bit 1 = rule (v) fired on W
///   XY build: bit 0 = rule (ii) fired on X, bit 1 = rule (iii) fired on Y
pub type BuildMemoKey = (u128, u64, u8);

/// BDKR rule-fired state bit positions (XY half).
pub const BDKR_RULE_II_FIRED: u8 = 1 << 0;
pub const BDKR_RULE_III_FIRED: u8 = 1 << 1;
/// BDKR rule-fired state bit positions (ZW half).
pub const BDKR_RULE_IV_FIRED: u8 = 1 << 0;
pub const BDKR_RULE_V_FIRED: u8 = 1 << 1;
/// Captures the `W[m-1]` tail bit (bit 2) and a "tail known" flag (bit 3).
/// Rule (v)'s alternation predicate `W[j]*W[m-1-j] != W[m-1]` needs `W[m-1]`,
/// which sits at MDD position `2k-1` — placed at level 1 in bouncing order
/// but drops out of `active_bits` at the final level.  We snapshot its bit
/// into `zw_rule_state` the moment it's placed so later levels can read it.
pub const BDKR_W_TAIL_BIT: u8 = 1 << 2;
pub const BDKR_W_TAIL_KNOWN: u8 = 1 << 3;

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

/// Compute active position tracking for a sequence of levels.
/// `position_pairs[level]` gives the (pos_a, pos_b) pairs that complete at that level.
/// Returns (active_at_level, active_indices) where active_indices is a flat Vec<usize>
/// with active_indices[level][pos] = index in active set (usize::MAX if absent).
pub fn compute_active_tracking(
    depth: usize,
    n_positions: usize,
    pos_order: &[usize],
    position_pairs: &[Vec<(usize, usize)>],
) -> (Vec<Vec<usize>>, Vec<Vec<usize>>) {
    let mut last_use: Vec<usize> = vec![0; n_positions];
    for (level, pairs) in position_pairs.iter().enumerate() {
        for &(a, b) in pairs {
            last_use[a] = last_use[a].max(level);
            last_use[b] = last_use[b].max(level);
        }
    }
    let mut active_at_level: Vec<Vec<usize>> = vec![Vec::new(); depth + 1];
    for d in 0..depth {
        let mut active: Vec<usize> = if d > 0 {
            active_at_level[d - 1].iter()
                .filter(|&&p| last_use[p] >= d)
                .copied().collect()
        } else { Vec::new() };
        active.push(pos_order[d]);
        active.sort();
        active_at_level[d] = active;
    }
    let active_indices: Vec<Vec<usize>> = active_at_level.iter()
        .map(|active| {
            let mut flat = vec![usize::MAX; n_positions];
            for (i, &p) in active.iter().enumerate() { flat[p] = i; }
            flat
        }).collect();
    (active_at_level, active_indices)
}

/// Delta table for Z or W events: delta[bits_a * 4 + bits_b].
/// Z (is_z=true): 2 * sign(bit0_a) * sign(bit0_b)
/// W (is_z=false): 2 * sign(bit1_a) * sign(bit1_b)
pub fn make_zw_delta(is_z: bool) -> [i8; 16] {
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

/// Reduce a 4-way node: return DEAD if all dead, collapse if all same,
/// otherwise dedup via hash-based unique table.
#[inline]
pub fn reduce_node(
    level: u8,
    children: [u32; 4],
    nodes: &mut Vec<[u32; 4]>,
    unique: &mut HashMap<u64, u32>,
) -> u32 {
    if children.iter().all(|&c| c == DEAD) {
        return DEAD;
    }
    let first = children[0];
    if children.iter().all(|&c| c == first) {
        return first;
    }
    let key = hash_node4(level, &children);
    if let Some(&nid) = unique.get(&key) {
        nid
    } else {
        let nid = nodes.len() as u32;
        nodes.push(children);
        unique.insert(key, nid);
        nid
    }
}

/// Delta table for XY events: xa*xb + ya*yb.
pub fn make_xy_delta() -> [i8; 16] {
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
#[allow(dead_code)]
struct StatusLine {
    call_count: u64,
    start: std::time::Instant,
    last_print: std::time::Instant,
    k: usize,
}

#[allow(dead_code)]
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
        let stats = BuildStats::new(k);
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
        let zw_pairs: Vec<Vec<(usize, usize)>> = zw_events_at_level.iter()
            .map(|evs| evs.iter().map(|(_, ev)| (ev.pos_a, ev.pos_b)).collect()).collect();
        let (zw_active_at_level, zw_active_indices) =
            compute_active_tracking(zw_depth, 2 * k, &pos_order, &zw_pairs);

        let xy_pairs: Vec<Vec<(usize, usize)>> = xy_events_at_level.iter()
            .map(|evs| evs.iter().map(|(_, ev)| (ev.pos_a, ev.pos_b)).collect()).collect();
        let (xy_active_at_level, xy_active_indices) =
            compute_active_tracking(zw_depth, 2 * k, &pos_order, &xy_pairs);

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

        let mut all_restrict: Vec<(usize, u32)> = match restrict_branches {
            Some(branches) => branches.iter().enumerate()
                .map(|(d, &b)| (d + 1, b))
                .collect(),
            None => Vec::new(),
        };
        if let Some(target) = restrict_level1 {
            all_restrict.push((1, target));
        }

        // Enable BDKR canonical rule enforcement only when pos_order is the
        // bouncing layout (required for ascending-j incremental scanning).
        // Users can force-disable via MDD_DISABLE_CANON=1 for A/B comparisons.
        let canonical_rules = is_bouncing_order(&pos_order, k)
            && std::env::var("MDD_DISABLE_CANON").is_err();
        let close_pair_at_level = compute_close_pair_at_level(&pos_order, k);
        let w_tail_pos = 2 * k - 1;

        let zw_ctx = ZwBuildCtx {
            pos_order: pos_order.clone(),
            events: zw_resolved_events,
            lag_check: zw_lag_check_at_level,
            max_remaining: zw_max_remaining,
            active_at_level: zw_active_at_level,
            active_indices: zw_active_indices,
            xy_max_abs,
            k,
            depth: zw_depth,
            symmetry_break: true,
            restrict_branches: all_restrict,
            zw_only,
            canonical_rules,
            close_pair_at_level: close_pair_at_level.clone(),
            w_tail_pos,
            target_pair_offset: 0,
            pin_z_tail: std::env::var("MDD_PIN_Z_TAIL").is_ok(),
        };
        let xy_ctx = XyBuildCtx {
            pos_order: pos_order.clone(),
            events: xy_resolved_events,
            lag_check: xy_lag_check_at_level,
            max_remaining: xy_max_remaining,
            active_at_level: xy_active_at_level,
            active_indices: xy_active_indices,
            k,
            depth: zw_depth,
            symmetry_break: true,
            canonical_rules,
            close_pair_at_level,
            target_pair_offset: 0,
            initial_xy_rule_state: 0,
        };

        let mut nodes: Vec<[u32; 4]> = Vec::new();
        nodes.push([DEAD; 4]); // node 0 = DEAD

        let mut unique: HashMap<u64, u32> = HashMap::default();

        let mut zw_memo: Vec<HashMap<BuildMemoKey, u32>> = (0..=zw_depth).map(|_| HashMap::default()).collect();
        let mut xy_memo: Vec<HashMap<BuildMemoKey, u32>> = (0..=zw_depth).map(|_| HashMap::default()).collect();

        // (build_zw is now the module-level build_zw_dfs)

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
        let _per_level_cap: usize = max_memo_entries / (zw_depth + 1);
        let mut zw_memo_count: usize = 0;
        let mut xy_cache: HashMap<u128, u32> = HashMap::default();

        let mut sums = vec![0i8; k];
        let root = build_zw_dfs(
            0, &mut sums, &[], 0,
            &zw_ctx, &xy_ctx,
            &mut nodes, &mut unique, &mut zw_memo, &mut xy_memo, &mut xy_cache,
            max_memo_entries, &mut zw_memo_count,
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
/// Context for ZW half DFS builder.
pub struct ZwBuildCtx {
    pub pos_order: Vec<usize>,
    pub events: Vec<Vec<(usize, usize, usize, [i8; 16])>>,
    pub lag_check: Vec<Vec<usize>>,
    pub max_remaining: Vec<Vec<i32>>,
    pub active_at_level: Vec<Vec<usize>>,
    pub active_indices: Vec<Vec<usize>>,
    pub xy_max_abs: Vec<i32>,
    pub k: usize,
    pub depth: usize,
    pub symmetry_break: bool,
    pub restrict_branches: Vec<(usize, u32)>,
    pub zw_only: bool,
    /// Enforce BDKR canonical rules (iv) and (v) during DFS.  Only safe when
    /// `pos_order` is the "bouncing" layout (pair `j` closes at level `2j+1`)
    /// so that palindromic pairs close in ascending `j` order.  Toggle off to
    /// get the old (non-canonical) MDD — e.g., in `build_extension` where the
    /// initial rule-fired state comes from the base boundary bits.
    pub canonical_rules: bool,
    /// For each level `l`, `Some(j)` if palindromic pair `(j, 2k-1-j)` closes
    /// at level `l`; `None` otherwise.  Precomputed from `pos_order`.
    pub close_pair_at_level: Vec<Option<usize>>,
    /// MDD position holding the tail `W[m-1]` used by rule (v).  Placed at
    /// level 1 in bouncing order (MDD position `2k-1`); tracked here so the
    /// DFS can read its bit from `active_bits` at any later level.  Set to
    /// `usize::MAX` if the tail lies outside this MDD (e.g., in `build_extension`
    /// the tail is in the old base bits and seeded into the initial rule_state).
    pub w_tail_pos: usize,
    /// Offset added to the MDD palindromic pair index `j` to get the target
    /// palindromic pair index (`j_target = target_pair_offset + j`).  Zero for
    /// the main build; equal to `base_k` in `build_extension` where the
    /// extension MDD starts at target pair `base_k`.
    pub target_pair_offset: usize,
    /// Experimental: pin `z[n-1] = -1` at MDD position `2k-1` (Z-bit = 0).
    /// Consequence of rule (i) `z[0]=x[0]=y[0]=x[n-1]=y[n-1]=+1` plus the
    /// lag-(n-1) vanishing identity (W contributes zero at lag n-1 since
    /// `len(W) = n-1`): `2·z[n-1] + x[0]·x[n-1] + y[0]·y[n-1] = 0` ⇒
    /// `z[n-1] = -1`.  Enabled via `MDD_PIN_Z_TAIL=1`; off in
    /// `build_extension` (no new Z tail there).
    pub pin_z_tail: bool,
}

/// DFS builder for ZW half. At the boundary, delegates to build_xy_dfs.
/// Returns the root node ID.
///
/// `zw_rule_state` carries the BDKR rule (iv)/(v) "has fired at an earlier
/// palindromic pair?" bits (`BDKR_RULE_IV_FIRED`, `BDKR_RULE_V_FIRED`).
/// When `ctx.canonical_rules` is true, each odd level that closes a
/// palindromic pair evaluates the rule on the closing pair's bits and
/// either prunes the branch (rule violated) or marks the rule as fired.
/// The initial call should pass `0` (no rules fired yet) — except when
/// continuing from a walked base boundary (see `build_extension`).
pub fn build_zw_dfs(
    level: usize,
    sums: &mut [i8],
    active_bits: &[u8],
    zw_rule_state: u8,
    ctx: &ZwBuildCtx,
    xy_ctx: &XyBuildCtx,
    nodes: &mut Vec<[u32; 4]>,
    unique: &mut HashMap<u64, u32>,
    zw_memo: &mut Vec<HashMap<BuildMemoKey, u32>>,
    xy_memo: &mut Vec<HashMap<BuildMemoKey, u32>>,
    xy_cache: &mut HashMap<u128, u32>,
    max_memo_entries: usize,
    zw_memo_count: &mut usize,
) -> u32 {
    if level == ctx.depth {
        // ZW done. Check XY feasibility.
        for li in 0..ctx.k {
            let zw_val = sums[li] as i32;
            if zw_val.abs() > ctx.xy_max_abs[li] { return DEAD; }
            if (zw_val + ctx.xy_max_abs[li]) % 2 != 0 { return DEAD; }
        }
        if ctx.zw_only { return LEAF; }

        // Check XY cache: same zw_sums → same XY sub-MDD root.  The XY
        // sub-MDD is independent of ZW rule state, so we only key by sums.
        let sums_key = pack_sums(sums);
        if let Some(&cached) = xy_cache.get(&sums_key) { return cached; }

        for m in xy_memo.iter_mut() { m.clear(); }
        let target: Vec<i8> = sums.iter().map(|&s| -s).collect();
        let mut xy_sums = vec![0i8; ctx.k];
        let result = build_xy_dfs(
            0, &mut xy_sums, &[], &target, xy_ctx.initial_xy_rule_state,
            xy_ctx, nodes, unique, xy_memo,
        );
        xy_cache.insert(sums_key, result);
        return result;
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

    let state_key: BuildMemoKey = (
        pack_sums(sums),
        pack_active(&current_vals[..n_active]),
        zw_rule_state,
    );
    if let Some(&cached) = zw_memo[level].get(&state_key) {
        return cached;
    }

    // Does a palindromic pair close at this level?  If so, the closing
    // pair index is `close_j` and its mirror position is `2k-1-close_j`.
    let close_j: Option<usize> = if ctx.canonical_rules {
        ctx.close_pair_at_level[level]
    } else { None };

    let mut children = [DEAD; 4];
    for branch in 0u32..4 {
        if ctx.symmetry_break && new_pos == 0 && branch != 0b11 { continue; }
        // Rule (i) consequence: z[n-1] = -1.  MDD position 2k-1 holds z[n-1],
        // and Z-bit = branch & 1 with bit=1 ⇒ z=+1.  Skip Z-bit=1 branches
        // there so only z[n-1]=-1 survives.  Gated on symmetry_break (the XY
        // half's x[n-1]=y[n-1]=+1 pin, which the derivation relies on, is
        // also gated on symmetry_break).
        if ctx.pin_z_tail && ctx.symmetry_break
            && new_pos == 2 * ctx.k - 1
            && (branch & 0b01) != 0 { continue; }
        if !ctx.restrict_branches.is_empty() {
            let mut skip = false;
            for &(rlevel, rbranch) in &ctx.restrict_branches {
                if level == rlevel && branch != rbranch { skip = true; break; }
            }
            if skip { continue; }
        }

        current_vals[new_idx] = branch as u8;

        // Evaluate BDKR rules (iv)/(v) if a palindromic pair closes here.
        // Z-bit is bit 0, W-bit is bit 1 of each 2-bit branch slot.
        let mut new_rule_state = zw_rule_state;

        // Snapshot the W[m-1] tail bit once its MDD position is placed.
        // `close_pair_at_level` guarantees `new_pos == ctx.w_tail_pos` exactly
        // once in the build (the level where pos `2k-1` enters active_bits).
        if ctx.canonical_rules
            && new_rule_state & BDKR_W_TAIL_KNOWN == 0
            && new_pos == ctx.w_tail_pos
        {
            let w_bit = ((branch >> 1) & 1) as u8;
            new_rule_state |= BDKR_W_TAIL_KNOWN;
            if w_bit == 1 { new_rule_state |= BDKR_W_TAIL_BIT; }
        }

        if let Some(j) = close_j {
            let mirror = ctx.depth - 1 - j;
            let target_j = ctx.target_pair_offset + j;
            let idx_j = ctx.active_indices[level][j];
            let idx_m = ctx.active_indices[level][mirror];
            // Both must be active at this level (they are, since the
            // closing event is owned by this level in bouncing order).
            if idx_j != usize::MAX && idx_m != usize::MAX {
                let zj = (current_vals[idx_j]      ) & 1;
                let zm = (current_vals[idx_m]      ) & 1;
                let wj = (current_vals[idx_j] >> 1) & 1;
                let wm = (current_vals[idx_m] >> 1) & 1;

                // Rule (iv) on Z: least j with Z[j] == Z[n-1-j] ⇒ Z[j]=+1.
                if zw_rule_state & BDKR_RULE_IV_FIRED == 0 && zj == zm {
                    // Pair is palindromic (both equal).  Rule fires here.
                    if zj != 1 {
                        // Z[j] = -1 violates: skip this branch entirely.
                        continue;
                    }
                    new_rule_state |= BDKR_RULE_IV_FIRED;
                }

                // Rule (v) on W: least j (>=1) with W[j]*W[n-1-j] != W[n-1]
                //   ⇒ W[j]=+1.  target_j=0 can't fire (W[0]=+1 via rule (i)).
                // The tail W[n-1] bit is carried in new_rule_state's
                // BDKR_W_TAIL_BIT once known.
                if target_j >= 1
                    && zw_rule_state & BDKR_RULE_V_FIRED == 0
                    && new_rule_state & BDKR_W_TAIL_KNOWN != 0
                {
                    let w_tail = if new_rule_state & BDKR_W_TAIL_BIT != 0 { 1u8 } else { 0 };
                    // (wj XNOR wm) = 1 iff wj == wm iff product = +1.
                    //   prod != tail ⇒ rule fires; require wj = +1 else prune.
                    let prod_bit = (wj == wm) as u8;
                    if prod_bit != w_tail {
                        if wj != 1 { continue; }
                        new_rule_state |= BDKR_RULE_V_FIRED;
                    }
                }
            }
        }

        for &(lag_idx, idx_a, idx_b, ref delta) in &ctx.events[level] {
            let bits_a = current_vals[idx_a] as usize;
            let bits_b = current_vals[idx_b] as usize;
            sums[lag_idx] += delta[bits_a * 4 + bits_b];
        }

        let mut ok = true;
        for &li in &ctx.lag_check[level] {
            let zw_val = sums[li] as i32;
            if zw_val.abs() > ctx.xy_max_abs[li] { ok = false; break; }
            if (zw_val + ctx.xy_max_abs[li]) % 2 != 0 { ok = false; break; }
        }
        if ok && level + 1 < ctx.depth {
            for li in 0..ctx.k {
                let zw_val = sums[li] as i32;
                let zw_remaining = ctx.max_remaining[level + 1][li];
                if (zw_val.abs() - zw_remaining) > ctx.xy_max_abs[li] { ok = false; break; }
            }
        }

        if ok {
            children[branch as usize] = build_zw_dfs(
                level + 1, sums, &current_vals[..n_active], new_rule_state,
                ctx, xy_ctx,
                nodes, unique, zw_memo, xy_memo, xy_cache,
                max_memo_entries, zw_memo_count,
            );
        }

        for &(lag_idx, idx_a, idx_b, ref delta) in &ctx.events[level] {
            let bits_a = current_vals[idx_a] as usize;
            let bits_b = current_vals[idx_b] as usize;
            sums[lag_idx] -= delta[bits_a * 4 + bits_b];
        }
    }

    let result = reduce_node(level as u8, children, nodes, unique);

    // Memo eviction when over budget
    if max_memo_entries > 0 && *zw_memo_count >= max_memo_entries {
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

/// Context for XY sub-MDD DFS builder.
pub struct XyBuildCtx {
    pub pos_order: Vec<usize>,
    pub events: Vec<Vec<(usize, usize, usize, [i8; 16])>>,
    pub lag_check: Vec<Vec<usize>>,
    pub max_remaining: Vec<Vec<i32>>,
    pub active_at_level: Vec<Vec<usize>>,
    pub active_indices: Vec<Vec<usize>>,
    pub k: usize,
    pub depth: usize,
    pub symmetry_break: bool,
    /// Enforce BDKR canonical rules (ii), (iii), (vi) during DFS.  See
    /// `ZwBuildCtx::canonical_rules` for constraints (bouncing order only).
    pub canonical_rules: bool,
    /// See `ZwBuildCtx::close_pair_at_level`.
    pub close_pair_at_level: Vec<Option<usize>>,
    /// See `ZwBuildCtx::target_pair_offset`.
    pub target_pair_offset: usize,
    /// Initial `xy_rule_state` passed to `build_xy_dfs` when ZW reaches the
    /// boundary.  Zero for the main build (no rules fired yet); in
    /// `build_extension` seeded from the base bits so rules already fired in
    /// the base aren't re-checked.
    pub initial_xy_rule_state: u8,
}

/// Returns true iff `pos_order` is the default bouncing layout — pair `j`
/// occupies levels `(2j, 2j+1)` so palindromic pairs close in ascending `j`.
/// The DFS's incremental "first-violation" rule application relies on this.
pub fn is_bouncing_order(pos_order: &[usize], k: usize) -> bool {
    if pos_order.len() != 2 * k { return false; }
    for j in 0..k {
        if pos_order[2 * j] != j || pos_order[2 * j + 1] != 2 * k - 1 - j {
            return false;
        }
    }
    true
}

/// Precompute `close_pair_at_level[l]` = `Some(j)` if palindromic pair
/// `(j, 2k-1-j)` closes (both positions placed) at level `l`.
pub fn compute_close_pair_at_level(pos_order: &[usize], k: usize) -> Vec<Option<usize>> {
    let depth = pos_order.len();
    let mut pos_to_level: Vec<usize> = vec![0; 2 * k];
    for (level, &pos) in pos_order.iter().enumerate() {
        pos_to_level[pos] = level;
    }
    let mut close: Vec<Option<usize>> = vec![None; depth];
    for j in 0..k {
        let l1 = pos_to_level[j];
        let l2 = pos_to_level[2 * k - 1 - j];
        let close_level = l1.max(l2);
        if close_level < depth {
            close[close_level] = Some(j);
        }
    }
    close
}

/// DFS builder for XY sub-MDD. Builds the 4-way MDD for (x,y) assignments
/// that make sums reach target_sums at each lag.
///
/// `xy_rule_state` carries the BDKR rule (ii)/(iii) "has fired?" bits
/// (`BDKR_RULE_II_FIRED`, `BDKR_RULE_III_FIRED`).  Rule (vi) is a one-shot
/// tie-break evaluated at the level that closes pair `(1, 2k-2)` — no state
/// bit needed.  The initial call should pass `0`.
pub fn build_xy_dfs(
    level: usize,
    sums: &mut [i8],
    active_bits: &[u8],
    target_sums: &[i8],
    xy_rule_state: u8,
    ctx: &XyBuildCtx,
    nodes: &mut Vec<[u32; 4]>,
    unique: &mut HashMap<u64, u32>,
    memo: &mut Vec<HashMap<BuildMemoKey, u32>>,
) -> u32 {
    if level == ctx.depth {
        for li in 0..ctx.k {
            if sums[li] != target_sums[li] { return DEAD; }
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

    let state_key: BuildMemoKey = (
        pack_sums(sums),
        pack_active(&current_vals[..n_active]),
        xy_rule_state,
    );
    if let Some(&cached) = memo[level].get(&state_key) {
        return cached;
    }

    let close_j: Option<usize> = if ctx.canonical_rules {
        ctx.close_pair_at_level[level]
    } else { None };

    let mut children = [DEAD; 4];
    for branch in 0u32..4 {
        // BDKR 2012 rule (i): pin x[0]=y[0]=+1 (sub-MDD position 0) AND
        // x[n-1]=y[n-1]=+1 (sub-MDD position 2k-1 — the last suffix slot,
        // mapped to actual sequence position n-1 for any n>=2k).  Both
        // bits of branch 0b11 are set, meaning x_bit=y_bit=+1 there.
        if ctx.symmetry_break && new_pos == 0 && branch != 0b11 { continue; }
        if ctx.symmetry_break && new_pos == 2 * ctx.k - 1 && branch != 0b11 { continue; }
        current_vals[new_idx] = branch as u8;

        let mut new_rule_state = xy_rule_state;
        if let Some(j) = close_j {
            let mirror = ctx.depth - 1 - j;
            let target_j = ctx.target_pair_offset + j;
            let idx_j = ctx.active_indices[level][j];
            let idx_m = ctx.active_indices[level][mirror];
            if idx_j != usize::MAX && idx_m != usize::MAX {
                let xj = (current_vals[idx_j]      ) & 1;
                let xm = (current_vals[idx_m]      ) & 1;
                let yj = (current_vals[idx_j] >> 1) & 1;
                let ym = (current_vals[idx_m] >> 1) & 1;

                // Rule (ii) on X: least j with X[j] != X[n-1-j] ⇒ X[j]=+1.
                if xy_rule_state & BDKR_RULE_II_FIRED == 0 && xj != xm {
                    if xj != 1 { continue; }
                    new_rule_state |= BDKR_RULE_II_FIRED;
                }
                // Rule (iii) on Y.
                if xy_rule_state & BDKR_RULE_III_FIRED == 0 && yj != ym {
                    if yj != 1 { continue; }
                    new_rule_state |= BDKR_RULE_III_FIRED;
                }

                // Rule (vi) — conditional A vs B tie-break at (X[1], Y[1])
                // and (X[n-2], Y[n-2]).  Fully determined at the level
                // closing target pair j=1 since both positions are placed by
                // then.  In the main build target_j == j; in build_extension
                // rule (vi) is evaluated from the base bits up-front, so it
                // only triggers here when base_k <= 1 (target_j == 1 can
                // correspond to ext pair j=0 when base_k==1).
                if target_j == 1 {
                    let x_head = xj;  // X[1]
                    let y_head = yj;  // Y[1]
                    let x_tail = xm;  // X[n-2]
                    let y_tail = ym;  // Y[n-2]
                    if x_head != y_head {
                        if x_head != 1 { continue; }
                    } else {
                        if x_tail != 1 || y_tail != 0 { continue; }
                    }
                }
            }
        }

        for &(lag_idx, idx_a, idx_b, ref delta) in &ctx.events[level] {
            let bits_a = current_vals[idx_a] as usize;
            let bits_b = current_vals[idx_b] as usize;
            sums[lag_idx] += delta[bits_a * 4 + bits_b];
        }

        let mut ok = true;
        for &li in &ctx.lag_check[level] {
            if sums[li] != target_sums[li] { ok = false; break; }
        }
        if ok && level + 1 < ctx.depth {
            for li in 0..ctx.k {
                let gap = (sums[li] as i32) - (target_sums[li] as i32);
                let remaining = ctx.max_remaining[level + 1][li];
                if gap.abs() > remaining { ok = false; break; }
            }
        }

        if ok {
            children[branch as usize] = build_xy_dfs(
                level + 1, sums, &current_vals[..n_active], target_sums, new_rule_state,
                ctx, nodes, unique, memo,
            );
        }

        for &(lag_idx, idx_a, idx_b, ref delta) in &ctx.events[level] {
            let bits_a = current_vals[idx_a] as usize;
            let bits_b = current_vals[idx_b] as usize;
            sums[lag_idx] -= delta[bits_a * 4 + bits_b];
        }
    }

    let result = reduce_node(level as u8, children, nodes, unique);
    memo[level].insert(state_key, result);
    result
}

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

    let xy_pairs_for_active: Vec<Vec<(usize, usize)>> = xy_events_at_level.iter()
        .map(|evs| evs.iter().map(|(_, ev)| (ev.pos_a, ev.pos_b)).collect()).collect();
    let (xy_active_at_level, xy_active_indices) =
        compute_active_tracking(zw_depth, 2 * k, &pos_order, &xy_pairs_for_active);

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
    let mut memo: Vec<HashMap<BuildMemoKey, u32>> = (0..=zw_depth).map(|_| HashMap::default()).collect();

    let canonical_rules = is_bouncing_order(&pos_order, k)
        && std::env::var("MDD_DISABLE_CANON").is_err();
    let close_pair_at_level = compute_close_pair_at_level(&pos_order, k);

    let ctx = XyBuildCtx {
        pos_order,
        events: resolved_events,
        lag_check: xy_lag_check_at_level,
        max_remaining: xy_max_remaining,
        active_at_level: xy_active_at_level,
        active_indices: xy_active_indices,
        k,
        depth: zw_depth,
        symmetry_break: true,
        canonical_rules,
        close_pair_at_level,
        target_pair_offset: 0,
        initial_xy_rule_state: 0,
    };

    let target: Vec<i8> = zw_sums.iter().map(|&s| -s).collect();
    let mut sums = vec![0i8; k];
    let root = build_xy_dfs(
        0, &mut sums, &[], &target, 0,
        &ctx, &mut nodes, &mut unique, &mut memo,
    );

    (nodes, root)
}

/// Compute the BDKR canonical-rule-fired state implied by a concrete base
/// boundary.  Scans palindromic pairs `j = 0..base_k` in ascending `j`:
///
/// * Rules (ii)/(iii)/(iv)/(v) record their "first violation" (fired) bit if
///   the scan finds a firing pair whose value satisfies the rule; if the scan
///   finds a violation (e.g., rule (ii) fires with X[j]=-1), we return `None`
///   because the base boundary itself is already non-canonical.
/// * Rule (vi) is a one-shot tie-break at target pair `j=1`; when `base_k >= 2`
///   both positions are in the base and we validate here, returning `None` on
///   violation.
/// * The tail `W[n-1]` bit is seeded into `BDKR_W_TAIL_BIT`/`BDKR_W_TAIL_KNOWN`.
///
/// Returns `Some((zw_rule_state, xy_rule_state))` or `None` if the base is
/// already non-canonical.
pub fn compute_extension_initial_rule_state(
    base_k: usize,
    z_bits: u32,
    w_bits: u32,
    x_bits: u32,
    y_bits: u32,
) -> Option<(u8, u8)> {
    let bit = |bits: u32, i: usize| -> u8 { ((bits >> i) & 1) as u8 };
    let mut zw = 0u8;
    let mut xy = 0u8;

    // Seed W tail = W[n-1] from base long bit 2*base_k-1.
    if base_k >= 1 {
        zw |= BDKR_W_TAIL_KNOWN;
        if bit(w_bits, 2 * base_k - 1) == 1 { zw |= BDKR_W_TAIL_BIT; }
    }
    let w_tail = (zw & BDKR_W_TAIL_BIT) != 0;

    for j in 0..base_k {
        let mirror = 2 * base_k - 1 - j;
        let xh = bit(x_bits, j);
        let xt = bit(x_bits, mirror);
        let yh = bit(y_bits, j);
        let yt = bit(y_bits, mirror);
        let zh = bit(z_bits, j);
        let zt = bit(z_bits, mirror);
        let wh = bit(w_bits, j);
        let wt = bit(w_bits, mirror);

        // Rule (ii) on X: least j with X[j] != X[n-1-j] ⇒ X[j]=+1.
        if xy & BDKR_RULE_II_FIRED == 0 && xh != xt {
            if xh != 1 { return None; }
            xy |= BDKR_RULE_II_FIRED;
        }
        // Rule (iii) on Y.
        if xy & BDKR_RULE_III_FIRED == 0 && yh != yt {
            if yh != 1 { return None; }
            xy |= BDKR_RULE_III_FIRED;
        }
        // Rule (iv) on Z: least j with Z[j] == Z[n-1-j] ⇒ Z[j]=+1.
        if zw & BDKR_RULE_IV_FIRED == 0 && zh == zt {
            if zh != 1 { return None; }
            zw |= BDKR_RULE_IV_FIRED;
        }
        // Rule (v) on W (target_j >= 1).  j=0 trivially satisfied.
        if j >= 1 && zw & BDKR_RULE_V_FIRED == 0 {
            let prod = (wh == wt) as u8;
            let tail = if w_tail { 1u8 } else { 0 };
            if prod != tail {
                if wh != 1 { return None; }
                zw |= BDKR_RULE_V_FIRED;
            }
        }
        // Rule (vi) at target j == 1 (one-shot).
        if j == 1 {
            if xh != yh {
                if xh != 1 { return None; }
            } else {
                if xt != 1 || yt != 0 { return None; }
            }
        }
    }

    Some((zw, xy))
}

/// Build an MDD that extends a k=base_k boundary to k=target_k.
///
/// Given concrete boundary values (z_bits, w_bits, x_bits, y_bits) from a
/// base_k-sized MDD, this builds an MDD over the *extension* positions only
/// (positions base_k..target_k-1 in the "short" halves and their corresponding
/// "long" counterparts).
///
/// The lag structure: lag j pairs position i with position (k + i + j) for Z/X/Y,
/// and position i with position (k + i + j + 1) for W alone. When extending from
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
///
/// See also `has_extension` for a quick yes/no check that avoids full enumeration.
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

    // Compute initial sums from old×old pairs (these are fixed).
    //
    // Target encoding: short=0..target_k-1, long=target_k..2*target_k-1.
    // Old positions: short 0..base_k-1, long target_k+extra..2*target_k-1.
    // New positions: short base_k..target_k-1, long target_k..target_k+extra-1.
    //
    // For target lag j, Z/X/Y pairs are (i, target_k+i+j). Old×old requires
    // i < base_k AND i+j >= extra (so the long position is old, not new).
    // Base-encoding bit for old long target pos target_k+i+j: base_k + (i+j - extra).
    //
    // For W pairs at (i, target_k+i+j+1): old×old requires i < base_k AND i+j+1 >= extra.
    let mut initial_sums = vec![0i8; target_k];
    for j in 0..target_k {
        let mut sum = 0i32;

        // Z/X/Y old×old pairs: (i, target_k+i+j) where i < base_k AND i+j >= extra
        for i in 0..base_k {
            if i + j < extra { continue; } // long position is new
            if i + j >= target_k { continue; } // out of range
            let bit_b = base_k + (i + j - extra);
            let za = if (z_bits >> i) & 1 == 1 { 1 } else { -1i32 };
            let zb = if (z_bits >> bit_b) & 1 == 1 { 1 } else { -1i32 };
            sum += 2 * za * zb;
            let xa = if (x_bits >> i) & 1 == 1 { 1 } else { -1i32 };
            let xb = if (x_bits >> bit_b) & 1 == 1 { 1 } else { -1i32 };
            sum += xa * xb;
            let ya = if (y_bits >> i) & 1 == 1 { 1 } else { -1i32 };
            let yb = if (y_bits >> bit_b) & 1 == 1 { 1 } else { -1i32 };
            sum += ya * yb;
        }
        // W old×old pairs: (i, target_k+i+j+1) where i < base_k AND i+j+1 >= extra
        if j < target_k - 1 {
            for i in 0..base_k {
                if i + j + 1 < extra { continue; }
                if i + j + 1 >= target_k { continue; }
                let bit_b = base_k + (i + j + 1 - extra);
                let wa = if (w_bits >> i) & 1 == 1 { 1 } else { -1i32 };
                let wb = if (w_bits >> bit_b) & 1 == 1 { 1 } else { -1i32 };
                sum += 2 * wa * wb;
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

    // Position classification for events.
    //
    // Target encoding: short=0..target_k-1, long=target_k..2*target_k-1.
    // Old short: 0..base_k-1.  New short: base_k..target_k-1.
    // New long: target_k..target_k+extra-1.  Old long: target_k+extra..2*target_k-1.
    //
    // Extension numbering: ext 0..extra-1 = new short, ext extra..2*extra-1 = new long.

    // Classify target position: Some(ext_idx) if new, None if old.
    let classify = |pos: usize| -> Option<usize> {
        if pos < base_k { None }
        else if pos < target_k { Some(pos - base_k) }
        else if pos < target_k + extra { Some(extra + (pos - target_k)) }
        else { None }
    };
    // Convert old target position to base-encoding bit index.
    let to_base_bit = |pos: usize| -> usize {
        if pos < base_k { pos } else { base_k + (pos - target_k - extra) }
    };

    struct ExtEvent {
        lag: usize,
        // If both positions are new: ext_a and ext_b are extension positions
        // If one is old: ext_new is the extension position, old_sign is the known ±1 value
        kind: ExtEventKind,
    }
    #[allow(dead_code)]
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

        // Z pairs: (i, target_k + i + j) for i in 0..target_k-j
        for i in 0..target_k.saturating_sub(j) {
            let pos_a = i;
            let pos_b = target_k + i + j;
            if pos_b >= 2 * target_k { continue; }

            let ext_a = classify(pos_a);
            let ext_b = classify(pos_b);
            if ext_a.is_none() && ext_b.is_none() { continue; }

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
                    let bb = to_base_bit(pos_b);
                    let zb = if (z_bits >> bb) & 1 == 1 { 1i8 } else { -1 };
                    ExtEvent {
                        lag: j,
                        kind: ExtEventKind::OldNew { ext_new: en, old_sign_z: zb, old_sign_w: 0, old_sign_x: 0, old_sign_y: 0 },
                    }
                },
                (None, Some(en)) => {
                    let ba = to_base_bit(pos_a);
                    let za = if (z_bits >> ba) & 1 == 1 { 1i8 } else { -1 };
                    ExtEvent {
                        lag: j,
                        kind: ExtEventKind::OldNew { ext_new: en, old_sign_z: za, old_sign_w: 0, old_sign_x: 0, old_sign_y: 0 },
                    }
                },
                _ => unreachable!(),
            };

            for lv in 0..=complete_level {
                max_remaining[lv][j] += 2; // max |2*za*zb| = 2
            }

            events_at_level[complete_level].push(event);
            max_complete_level = Some(max_complete_level.map_or(complete_level, |c: usize| c.max(complete_level)));
        }

        // W-only pairs: (i, target_k + i + j + 1) for i in 0..target_k-j-1
        if j < target_k - 1 {
            for i in 0..target_k - j - 1 {
                let pos_a = i;
                let pos_b = target_k + i + j + 1;
                if pos_b >= 2 * target_k { continue; }

                let ext_a = classify(pos_a);
                let ext_b = classify(pos_b);
                if ext_a.is_none() && ext_b.is_none() { continue; }

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
                        let bb = to_base_bit(pos_b);
                        let wb = if (w_bits >> bb) & 1 == 1 { 1i8 } else { -1 };
                        ExtEvent {
                            lag: j,
                            kind: ExtEventKind::OldNew { ext_new: en, old_sign_z: 0, old_sign_w: wb, old_sign_x: 0, old_sign_y: 0 },
                        }
                    },
                    (None, Some(en)) => {
                        let ba = to_base_bit(pos_a);
                        let wa = if (w_bits >> ba) & 1 == 1 { 1i8 } else { -1 };
                        ExtEvent {
                            lag: j,
                            kind: ExtEventKind::OldNew { ext_new: en, old_sign_z: 0, old_sign_w: wa, old_sign_x: 0, old_sign_y: 0 },
                        }
                    },
                    _ => unreachable!(),
                };

                for lv in 0..=complete_level {
                    max_remaining[lv][j] += 2; // max |2*wa*wb| = 2
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
    // XY pairs: (i, target_k+i+j) for X and Y (same positions as Z).
    let mut xy_events_at_level: Vec<Vec<ExtEvent>> = (0..ext_depth).map(|_| Vec::new()).collect();
    let mut xy_lag_check_at_level: Vec<Vec<usize>> = (0..=ext_depth).map(|_| Vec::new()).collect();
    let mut xy_max_remaining: Vec<Vec<i32>> = vec![vec![0i32; target_k]; ext_depth + 1];

    for j in 0..target_k {
        let mut max_complete_level: Option<usize> = None;

        // X/Y pairs: (i, target_k + i + j) — same positions as Z
        for i in 0..target_k.saturating_sub(j) {
            let pos_a = i;
            let pos_b = target_k + i + j;
            if pos_b >= 2 * target_k { continue; }

            let ext_a = classify(pos_a);
            let ext_b = classify(pos_b);
            if ext_a.is_none() && ext_b.is_none() { continue; }

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
                    let bb = to_base_bit(pos_b);
                    let xb = if (x_bits >> bb) & 1 == 1 { 1i8 } else { -1 };
                    let yb = if (y_bits >> bb) & 1 == 1 { 1i8 } else { -1 };
                    ExtEvent { lag: j, kind: ExtEventKind::OldNew {
                        ext_new: en, old_sign_z: xb, old_sign_w: yb, old_sign_x: 0, old_sign_y: 0,
                    }}
                },
                (None, Some(en)) => {
                    let ba = to_base_bit(pos_a);
                    let xa = if (x_bits >> ba) & 1 == 1 { 1i8 } else { -1 };
                    let ya = if (y_bits >> ba) & 1 == 1 { 1i8 } else { -1 };
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

    // Extract position pairs from events for active tracking
    fn ext_event_pairs(evs: &[ExtEvent]) -> Vec<(usize, usize)> {
        evs.iter().map(|ev| match &ev.kind {
            ExtEventKind::NewNew { ext_a, ext_b, .. } => (*ext_a, *ext_b),
            ExtEventKind::OldNew { ext_new, .. } => (*ext_new, *ext_new),
        }).collect()
    }
    // Combine ZW and XY event pairs (both use same position space)
    let combined_pairs: Vec<Vec<(usize, usize)>> = (0..ext_depth).map(|l| {
        let mut pairs = ext_event_pairs(&events_at_level[l]);
        pairs.extend(ext_event_pairs(&xy_events_at_level[l]));
        pairs
    }).collect();
    let (active_at_level, active_indices) =
        compute_active_tracking(ext_depth, ext_depth, &pos_order, &combined_pairs);

    // Resolve ZW events into delta tables
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
    let mut zw_memo: Vec<HashMap<BuildMemoKey, u32>> = (0..=ext_depth).map(|_| HashMap::default()).collect();
    let mut xy_memo: Vec<HashMap<BuildMemoKey, u32>> = (0..=ext_depth).map(|_| HashMap::default()).collect();

    // Seed initial BDKR rule-fired state from the base boundary bits.  If the
    // base itself violates any rule (e.g., X[j]!=X[n-1-j] with X[j]=-1 at the
    // first such j) then no canonical extension is possible → return DEAD.
    let (init_zw_state, init_xy_state) = match compute_extension_initial_rule_state(
        base_k, z_bits, w_bits, x_bits, y_bits,
    ) {
        Some(s) => s,
        None => {
            return (nodes, DEAD);
        }
    };

    let canonical_rules = is_bouncing_order(&pos_order, extra)
        && std::env::var("MDD_DISABLE_CANON").is_err();
    let close_pair_at_level = compute_close_pair_at_level(&pos_order, extra);

    let ext_zw_ctx = ZwBuildCtx {
        pos_order: pos_order.clone(),
        events: zw_resolved,
        lag_check: lag_check_at_level,
        max_remaining,
        active_at_level: active_at_level.clone(),
        active_indices: active_indices.clone(),
        xy_max_abs,
        k: target_k,
        depth: ext_depth,
        symmetry_break: false,
        restrict_branches: Vec::new(),
        zw_only: false,
        canonical_rules,
        close_pair_at_level: close_pair_at_level.clone(),
        // The W tail W[n-1] lies in the base (old long bit 2*base_k-1),
        // pre-seeded into `init_zw_state`.  Use usize::MAX so no extension
        // position ever matches and the DFS never re-snapshots.
        w_tail_pos: usize::MAX,
        target_pair_offset: base_k,
        // Z tail pin is applied only in the base build; extension inherits
        // the pinned value via the base's bits.
        pin_z_tail: false,
    };
    let ext_xy_ctx = XyBuildCtx {
        pos_order,
        events: xy_resolved,
        lag_check: xy_lag_check_at_level,
        max_remaining: xy_max_remaining,
        active_at_level,
        active_indices,
        k: target_k,
        depth: ext_depth,
        symmetry_break: false,
        canonical_rules,
        close_pair_at_level,
        target_pair_offset: base_k,
        initial_xy_rule_state: init_xy_state,
    };
    let mut sums = initial_sums;
    let mut zw_memo_count = 0usize;
    let mut xy_cache: HashMap<u128, u32> = HashMap::default();
    let root = build_zw_dfs(
        0, &mut sums, &[], init_zw_state,
        &ext_zw_ctx, &ext_xy_ctx,
        &mut nodes, &mut unique, &mut zw_memo, &mut xy_memo, &mut xy_cache,
        0, &mut zw_memo_count,
    );

    if std::env::var("MDD_PROFILE").is_ok() {
        eprintln!("build_extension: base_k={}, target_k={}, extra={}, {} nodes, root={}",
            base_k, target_k, extra, nodes.len(),
            if root == DEAD { "DEAD".to_string() } else if root == LEAF { "LEAF".to_string() } else { root.to_string() });
    }

    (nodes, root)
}

/// Check if ANY valid extension exists for a base boundary (quick yes/no).
/// Builds the full extension MDD but only checks if the root is live.
pub fn has_extension(
    base_k: usize,
    target_k: usize,
    z_bits: u32,
    w_bits: u32,
    x_bits: u32,
    y_bits: u32,
) -> bool {
    let (_, root) = build_extension(base_k, target_k, z_bits, w_bits, x_bits, y_bits);
    root != DEAD
}

/// Fast extension feasibility check for mdd_extend=1.
/// Brute-forces all 256 assignments for the 8 new boundary positions
/// (z/w/x/y × front/back) and checks if the extended boundary's partial
/// autocorrelation sums are achievable by the remaining middle positions.
/// ~1000x faster than has_extension() (no MDD/HashMap allocation).
pub fn has_extension_fast(
    base_k: usize,
    n: usize,
    z_bits: u32,
    w_bits: u32,
    x_bits: u32,
    y_bits: u32,
) -> bool {
    let m = n - 1;
    let tk = base_k + 1; // target_k

    // New positions: seq[base_k] (front) and seq[len-base_k-1] (back)
    let z_new = [base_k, n - base_k - 1];
    let w_new = [base_k, m - base_k - 1];
    // x,y new positions same as z

    // Helper: is position in the EXTENDED boundary (first tk or last tk)?
    let is_z_bnd = |p: usize| p < tk || p >= n - tk;
    let is_w_bnd = |p: usize| p < tk || p >= m - tk;

    // Helper: get old boundary value from bits
    let zv = |p: usize| -> i32 {
        if p < base_k { if (z_bits >> p) & 1 == 1 { 1 } else { -1 } }
        else { let b = base_k + (p - (n - base_k)); if (z_bits >> b) & 1 == 1 { 1 } else { -1 } }
    };
    let wv = |p: usize| -> i32 {
        if p < base_k { if (w_bits >> p) & 1 == 1 { 1 } else { -1 } }
        else { let b = base_k + (p - (m - base_k)); if (w_bits >> b) & 1 == 1 { 1 } else { -1 } }
    };
    let xv = |p: usize| -> i32 {
        if p < base_k { if (x_bits >> p) & 1 == 1 { 1 } else { -1 } }
        else { let b = base_k + (p - (n - base_k)); if (x_bits >> b) & 1 == 1 { 1 } else { -1 } }
    };
    let yv = |p: usize| -> i32 {
        if p < base_k { if (y_bits >> p) & 1 == 1 { 1 } else { -1 } }
        else { let b = base_k + (p - (n - base_k)); if (y_bits >> b) & 1 == 1 { 1 } else { -1 } }
    };

    // Identify which lags have boundary-boundary pairs (only these need checking)
    let mut check_lags: Vec<usize> = Vec::new();
    for j in 1..n {
        let has_z = (0..n.saturating_sub(j)).any(|i| is_z_bnd(i) && is_z_bnd(i + j));
        let has_w = (0..m.saturating_sub(j)).any(|i| is_w_bnd(i) && is_w_bnd(i + j));
        if has_z || has_w { check_lags.push(j); }
    }

    // Pre-compute old×old sums and max_middle for each check lag
    let is_old_z = |p: usize| p < base_k || p >= n - base_k;
    let is_old_w = |p: usize| p < base_k || p >= m - base_k;
    let _is_new_z = |p: usize| p == z_new[0] || p == z_new[1];
    let _is_new_w = |p: usize| p == w_new[0] || p == w_new[1];

    struct LagInfo {
        old_old_sum: i32,
        max_mid: i32,
        // Linear coefficients: [zf, zb, wf, wb, xf, xb, yf, yb]
        linear: [i32; 8],
        // Bilinear: (var_a, var_b, weight) pairs
        bilinear: Vec<(usize, usize, i32)>,
    }

    let mut lag_infos: Vec<LagInfo> = Vec::with_capacity(check_lags.len());

    for &j in &check_lags {
        let mut old_old_sum = 0i32;
        let mut linear = [0i32; 8];
        let mut bilinear: Vec<(usize, usize, i32)> = Vec::new();

        // Z pairs: (i, i+j), weight 2
        for i in 0..n.saturating_sub(j) {
            let a = i;
            let b = i + j;
            if !is_z_bnd(a) || !is_z_bnd(b) { continue; }
            let a_old = is_old_z(a);
            let b_old = is_old_z(b);
            let a_new_idx = if a == z_new[0] { Some(0usize) } else if a == z_new[1] { Some(1) } else { None };
            let b_new_idx = if b == z_new[0] { Some(0usize) } else if b == z_new[1] { Some(1) } else { None };

            if a_old && b_old {
                old_old_sum += 2 * zv(a) * zv(b);
            } else if let (Some(ai), None) = (a_new_idx, b_new_idx) {
                // new × old: contribution = 2 * new_val * old_val
                linear[ai] += 2 * zv(b);
            } else if let (None, Some(bi)) = (a_new_idx, b_new_idx) {
                // old × new
                linear[bi] += 2 * zv(a);
            } else if let (Some(ai), Some(bi)) = (a_new_idx, b_new_idx) {
                // new × new
                bilinear.push((ai, bi, 2));
            }
        }

        // W pairs: (i, i+j), weight 2
        for i in 0..m.saturating_sub(j) {
            let a = i;
            let b = i + j;
            if !is_w_bnd(a) || !is_w_bnd(b) { continue; }
            let a_old = is_old_w(a);
            let b_old = is_old_w(b);
            let a_new_idx = if a == w_new[0] { Some(2usize) } else if a == w_new[1] { Some(3) } else { None };
            let b_new_idx = if b == w_new[0] { Some(2usize) } else if b == w_new[1] { Some(3) } else { None };

            if a_old && b_old {
                old_old_sum += 2 * wv(a) * wv(b);
            } else if let (Some(ai), None) = (a_new_idx, b_new_idx) {
                linear[ai] += 2 * wv(b);
            } else if let (None, Some(bi)) = (a_new_idx, b_new_idx) {
                linear[bi] += 2 * wv(a);
            } else if let (Some(ai), Some(bi)) = (a_new_idx, b_new_idx) {
                bilinear.push((ai, bi, 2));
            }
        }

        // X pairs: (i, i+j), weight 1, same positions as Z
        for i in 0..n.saturating_sub(j) {
            let a = i;
            let b = i + j;
            if !is_z_bnd(a) || !is_z_bnd(b) { continue; }
            let a_old = is_old_z(a);
            let b_old = is_old_z(b);
            let a_new_idx = if a == z_new[0] { Some(4usize) } else if a == z_new[1] { Some(5) } else { None };
            let b_new_idx = if b == z_new[0] { Some(4usize) } else if b == z_new[1] { Some(5) } else { None };

            if a_old && b_old {
                old_old_sum += xv(a) * xv(b);
            } else if let (Some(ai), None) = (a_new_idx, b_new_idx) {
                linear[ai] += xv(b);
            } else if let (None, Some(bi)) = (a_new_idx, b_new_idx) {
                linear[bi] += xv(a);
            } else if let (Some(ai), Some(bi)) = (a_new_idx, b_new_idx) {
                bilinear.push((ai, bi, 1));
            }
        }

        // Y pairs: (i, i+j), weight 1, same positions as Z
        for i in 0..n.saturating_sub(j) {
            let a = i;
            let b = i + j;
            if !is_z_bnd(a) || !is_z_bnd(b) { continue; }
            let a_old = is_old_z(a);
            let b_old = is_old_z(b);
            let a_new_idx = if a == z_new[0] { Some(6usize) } else if a == z_new[1] { Some(7) } else { None };
            let b_new_idx = if b == z_new[0] { Some(6usize) } else if b == z_new[1] { Some(7) } else { None };

            if a_old && b_old {
                old_old_sum += yv(a) * yv(b);
            } else if let (Some(ai), None) = (a_new_idx, b_new_idx) {
                linear[ai] += yv(b);
            } else if let (None, Some(bi)) = (a_new_idx, b_new_idx) {
                linear[bi] += yv(a);
            } else if let (Some(ai), Some(bi)) = (a_new_idx, b_new_idx) {
                bilinear.push((ai, bi, 1));
            }
        }

        // Max middle correction
        let z_total = n.saturating_sub(j) as i32;
        let z_bnd: i32 = (0..n.saturating_sub(j)).filter(|&i| is_z_bnd(i) && is_z_bnd(i + j)).count() as i32;
        let w_total = m.saturating_sub(j) as i32;
        let w_bnd: i32 = (0..m.saturating_sub(j)).filter(|&i| is_w_bnd(i) && is_w_bnd(i + j)).count() as i32;
        let max_mid = 2 * (z_total - z_bnd) + 2 * (w_total - w_bnd)
                    + (z_total - z_bnd) + (z_total - z_bnd); // X + Y same as Z

        lag_infos.push(LagInfo { old_old_sum, max_mid, linear, bilinear });
    }

    // Evaluate all 256 combos
    let vals_for = |combo: u32| -> [i32; 8] {
        [
            if combo & 1 != 0 { 1 } else { -1 },   // zf
            if combo & 2 != 0 { 1 } else { -1 },   // zb
            if combo & 4 != 0 { 1 } else { -1 },   // wf
            if combo & 8 != 0 { 1 } else { -1 },   // wb
            if combo & 16 != 0 { 1 } else { -1 },  // xf
            if combo & 32 != 0 { 1 } else { -1 },  // xb
            if combo & 64 != 0 { 1 } else { -1 },  // yf
            if combo & 128 != 0 { 1 } else { -1 },  // yb
        ]
    };

    'combo: for combo in 0u32..256 {
        let v = vals_for(combo);
        for info in &lag_infos {
            let mut s = info.old_old_sum;
            for i in 0..8 { s += info.linear[i] * v[i]; }
            for &(a, b, w) in &info.bilinear { s += w * v[a] * v[b]; }
            if s.abs() > info.max_mid || (s + info.max_mid) % 2 != 0 {
                continue 'combo;
            }
        }
        return true;
    }
    false
}

/// ZW-only extension check for use at stage 0 (Boundary handler).
/// Only needs z_bits/w_bits — treats all XY positions as free variables.
/// Checks if the ZW boundary can extend to k+1 with any XY assignment.
/// Very fast: only 16 ZW combos (vs 256 for full check).
pub fn has_zw_extension_fast(
    base_k: usize,
    n: usize,
    z_bits: u32,
    w_bits: u32,
) -> bool {
    let m = n - 1;
    let tk = base_k + 1;

    let z_new = [base_k, n - base_k - 1];
    let w_new = [base_k, m - base_k - 1];

    let is_z_bnd = |p: usize| p < tk || p >= n - tk;
    let is_w_bnd = |p: usize| p < tk || p >= m - tk;

    let zv = |p: usize| -> i32 {
        if p < base_k { if (z_bits >> p) & 1 == 1 { 1 } else { -1 } }
        else { let b = base_k + (p - (n - base_k)); if (z_bits >> b) & 1 == 1 { 1 } else { -1 } }
    };
    let wv = |p: usize| -> i32 {
        if p < base_k { if (w_bits >> p) & 1 == 1 { 1 } else { -1 } }
        else { let b = base_k + (p - (m - base_k)); if (w_bits >> b) & 1 == 1 { 1 } else { -1 } }
    };

    let _is_old_z = |p: usize| p < base_k || p >= n - base_k;
    let _is_old_w = |p: usize| p < base_k || p >= m - base_k;

    // Identify check lags (where ZW boundary pairs exist)
    let mut check_lags: Vec<usize> = Vec::new();
    for j in 1..n {
        let has_z = (0..n.saturating_sub(j)).any(|i| is_z_bnd(i) && is_z_bnd(i + j));
        let has_w = (0..m.saturating_sub(j)).any(|i| is_w_bnd(i) && is_w_bnd(i + j));
        if has_z || has_w { check_lags.push(j); }
    }

    struct ZwLagInfo {
        zw_old_old_sum: i32,
        max_correction: i32,
        // Linear coefficients for 4 ZW vars: [zf, zb, wf, wb]
        linear: [i32; 4],
        bilinear: Vec<(usize, usize, i32)>,
    }

    let mut lag_infos: Vec<ZwLagInfo> = Vec::with_capacity(check_lags.len());

    for &j in &check_lags {
        let mut zw_old_old_sum = 0i32;
        let mut linear = [0i32; 4];
        let mut bilinear: Vec<(usize, usize, i32)> = Vec::new();

        // Z boundary pairs: weight 2
        for i in 0..n.saturating_sub(j) {
            let (a, b) = (i, i + j);
            if !is_z_bnd(a) || !is_z_bnd(b) { continue; }
            let a_new = if a == z_new[0] { Some(0usize) } else if a == z_new[1] { Some(1) } else { None };
            let b_new = if b == z_new[0] { Some(0usize) } else if b == z_new[1] { Some(1) } else { None };

            if a_new.is_none() && b_new.is_none() {
                zw_old_old_sum += 2 * zv(a) * zv(b);
            } else if let (Some(ai), None) = (a_new, b_new) {
                linear[ai] += 2 * zv(b);
            } else if let (None, Some(bi)) = (a_new, b_new) {
                linear[bi] += 2 * zv(a);
            } else if let (Some(ai), Some(bi)) = (a_new, b_new) {
                bilinear.push((ai, bi, 2));
            }
        }

        // W boundary pairs: weight 2
        for i in 0..m.saturating_sub(j) {
            let (a, b) = (i, i + j);
            if !is_w_bnd(a) || !is_w_bnd(b) { continue; }
            let a_new = if a == w_new[0] { Some(2usize) } else if a == w_new[1] { Some(3) } else { None };
            let b_new = if b == w_new[0] { Some(2usize) } else if b == w_new[1] { Some(3) } else { None };

            if a_new.is_none() && b_new.is_none() {
                zw_old_old_sum += 2 * wv(a) * wv(b);
            } else if let (Some(ai), None) = (a_new, b_new) {
                linear[ai] += 2 * wv(b);
            } else if let (None, Some(bi)) = (a_new, b_new) {
                linear[bi] += 2 * wv(a);
            } else if let (Some(ai), Some(bi)) = (a_new, b_new) {
                bilinear.push((ai, bi, 2));
            }
        }

        // Max correction: ZW middle pairs + ALL X/Y pairs (free since no X/Y boundary)
        let z_total = n.saturating_sub(j) as i32;
        let z_bnd: i32 = (0..n.saturating_sub(j)).filter(|&i| is_z_bnd(i) && is_z_bnd(i + j)).count() as i32;
        let w_total = m.saturating_sub(j) as i32;
        let w_bnd: i32 = (0..m.saturating_sub(j)).filter(|&i| is_w_bnd(i) && is_w_bnd(i + j)).count() as i32;
        // ZW middle pairs + ALL XY pairs (X and Y boundary positions are free)
        let max_correction = 2 * (z_total - z_bnd) + 2 * (w_total - w_bnd) + 2 * z_total;

        lag_infos.push(ZwLagInfo { zw_old_old_sum, max_correction, linear, bilinear });
    }

    // Only 16 ZW combos (4 vars: zf, zb, wf, wb)
    'combo: for combo in 0u32..16 {
        let v: [i32; 4] = [
            if combo & 1 != 0 { 1 } else { -1 },
            if combo & 2 != 0 { 1 } else { -1 },
            if combo & 4 != 0 { 1 } else { -1 },
            if combo & 8 != 0 { 1 } else { -1 },
        ];
        for info in &lag_infos {
            let mut s = info.zw_old_old_sum;
            for i in 0..4 { s += info.linear[i] * v[i]; }
            for &(a, b, w) in &info.bilinear { s += w * v[a] * v[b]; }
            if s.abs() > info.max_correction || (s + info.max_correction) % 2 != 0 {
                continue 'combo;
            }
        }
        return true;
    }
    false
}
