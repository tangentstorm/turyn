/// 16-ary MDD (Multi-valued Decision Diagram) for Turyn boundary configs.
///
/// Represents all valid (x,y,z,w) boundary 4-tuples as a DAG.
/// Built using memoized DFS on partial autocorrelation sums.
/// Positions visited in bouncing order: 0, 2k-1, 1, 2k-2, ...
///
/// Node encoding:
///   0          = DEAD (no valid completion)
///   u32::MAX   = LEAF (valid terminal)
///   other      = index into nodes[]

use std::collections::HashMap;

pub const DEAD: u32 = 0;
pub const LEAF: u32 = u32::MAX;

pub struct BoundaryMdd {
    pub nodes: Vec<[u32; 16]>,
    pub root: u32,
    pub k: usize,
    pub pos_order: Vec<usize>,
}

impl BoundaryMdd {
    /// Build MDD for boundary width k. Valid for all n >= 2k.
    pub fn build(k: usize) -> Self {
        let depth = 2 * k;

        // Bouncing position order
        let mut pos_order: Vec<usize> = Vec::with_capacity(depth);
        for t in 0..k {
            pos_order.push(t);
            pos_order.push(2 * k - 1 - t);
        }

        let mut pos_to_level: Vec<usize> = vec![0; depth];
        for (level, &pos) in pos_order.iter().enumerate() {
            pos_to_level[pos] = level;
        }

        // Build exact-lag bit pairs
        struct LagInfo {
            pairs: Vec<(usize, usize)>,    // XY/Z pairs
            w_pairs: Vec<(usize, usize)>,  // W pairs
        }
        let mut lags: Vec<LagInfo> = Vec::new();
        for j in 0..k {
            let pairs: Vec<(usize, usize)> = (0..k - j)
                .map(|i| (i, k + i + j)).collect();
            let w_pairs: Vec<(usize, usize)> = if j < k - 1 {
                (0..k - j - 1).map(|i| (i, k + i + j + 1)).collect()
            } else { Vec::new() };
            lags.push(LagInfo { pairs, w_pairs });
        }

        // Events: (pos_a, pos_b, lag_idx, is_xyzw)
        // is_xyzw=true: contributes N_X + N_Y + 2*N_Z
        // is_xyzw=false: contributes 2*N_W only
        let mut events_at_level: Vec<Vec<(usize, usize, usize, bool)>> =
            (0..depth).map(|_| Vec::new()).collect();
        let mut lag_check_at_level: Vec<Vec<usize>> =
            (0..=depth).map(|_| Vec::new()).collect();

        for (li, lag) in lags.iter().enumerate() {
            let mut lag_complete = 0usize;
            for &(a, b) in &lag.pairs {
                let complete = pos_to_level[a].max(pos_to_level[b]);
                events_at_level[complete].push((a, b, li, true));
                lag_complete = lag_complete.max(complete);
            }
            for &(a, b) in &lag.w_pairs {
                let complete = pos_to_level[a].max(pos_to_level[b]);
                events_at_level[complete].push((a, b, li, false));
                lag_complete = lag_complete.max(complete);
            }
            lag_check_at_level[lag_complete].push(li);
        }

        // Compute which positions' values are still needed at each level
        let mut last_use_level: Vec<usize> = vec![0; depth];
        for events in &events_at_level {
            for &(pa, pb, _, _) in events {
                let la = pos_to_level[pa];
                let lb = pos_to_level[pb];
                let complete = la.max(lb);
                last_use_level[pa] = last_use_level[pa].max(complete);
                last_use_level[pb] = last_use_level[pb].max(complete);
            }
        }

        let mut active_at_level: Vec<Vec<usize>> = vec![Vec::new(); depth + 1];
        for d in 0..depth {
            let mut active: Vec<usize> = if d > 0 {
                active_at_level[d - 1].iter()
                    .filter(|&&p| last_use_level[p] >= d)
                    .copied().collect()
            } else { Vec::new() };
            active.push(pos_order[d]);
            active.sort();
            active_at_level[d] = active;
        }

        let active_indices: Vec<HashMap<usize, usize>> = active_at_level.iter()
            .map(|active| active.iter().enumerate().map(|(i, &p)| (p, i)).collect())
            .collect();

        // Build context
        struct Ctx {
            pos_order: Vec<usize>,
            events_at_level: Vec<Vec<(usize, usize, usize, bool)>>,
            lag_check_at_level: Vec<Vec<usize>>,
            active_at_level: Vec<Vec<usize>>,
            active_indices: Vec<HashMap<usize, usize>>,
            depth: usize,
        }

        let ctx = Ctx {
            pos_order: pos_order.clone(),
            events_at_level,
            lag_check_at_level,
            active_at_level,
            active_indices,
            depth,
        };

        let mut nodes: Vec<[u32; 16]> = Vec::new();
        nodes.push([DEAD; 16]); // node 0 = DEAD

        let mut unique: HashMap<(u8, [u32; 16]), u32> = HashMap::new();

        type StateKey = (Vec<i8>, u64);
        let mut memo: Vec<HashMap<StateKey, u32>> = (0..=depth).map(|_| HashMap::new()).collect();

        fn pack_active(sign_cols: &[u8]) -> u64 {
            let mut packed = 0u64;
            for (i, &sc) in sign_cols.iter().enumerate() {
                packed |= (sc as u64) << (i * 4);
            }
            packed
        }

        fn build_rec(
            level: usize,
            sums: &mut Vec<i8>,
            active_bits: &mut Vec<u8>,
            ctx: &Ctx,
            nodes: &mut Vec<[u32; 16]>,
            unique: &mut HashMap<(u8, [u32; 16]), u32>,
            memo: &mut Vec<HashMap<StateKey, u32>>,
        ) -> u32 {
            if level == ctx.depth {
                return if sums.iter().all(|&s| s == 0) { LEAF } else { DEAD };
            }

            let active = &ctx.active_at_level[level];
            let mut current_active_vals: Vec<u8> = Vec::with_capacity(active.len());
            if level > 0 {
                let prev_indices = &ctx.active_indices[level - 1];
                for &pos in active {
                    if pos == ctx.pos_order[level] {
                        current_active_vals.push(0);
                    } else if let Some(&pi) = prev_indices.get(&pos) {
                        current_active_vals.push(active_bits[pi]);
                    } else {
                        current_active_vals.push(0);
                    }
                }
            } else {
                current_active_vals.resize(active.len(), 0);
            }

            let new_pos = ctx.pos_order[level];
            let new_idx = ctx.active_indices[level][&new_pos];

            let state_key = (sums.clone(), pack_active(&current_active_vals));
            if let Some(&cached) = memo[level].get(&state_key) {
                return cached;
            }

            let mut children = [DEAD; 16];
            for sign_col in 0u32..16 {
                if new_pos == 0 && sign_col != 0b1111 { continue; }

                current_active_vals[new_idx] = sign_col as u8;

                let sums_backup: Vec<i8> = sums.clone();
                for &(pos_a, pos_b, lag_idx, is_xyzw) in &ctx.events_at_level[level] {
                    let idx_a = ctx.active_indices[level][&pos_a];
                    let idx_b = ctx.active_indices[level][&pos_b];
                    let bits_a = current_active_vals[idx_a] as u32;
                    let bits_b = current_active_vals[idx_b] as u32;

                    if is_xyzw {
                        let xa: i32 = if (bits_a >> 0) & 1 == 1 { 1 } else { -1 };
                        let xb: i32 = if (bits_b >> 0) & 1 == 1 { 1 } else { -1 };
                        let ya: i32 = if (bits_a >> 1) & 1 == 1 { 1 } else { -1 };
                        let yb: i32 = if (bits_b >> 1) & 1 == 1 { 1 } else { -1 };
                        let za: i32 = if (bits_a >> 2) & 1 == 1 { 1 } else { -1 };
                        let zb: i32 = if (bits_b >> 2) & 1 == 1 { 1 } else { -1 };
                        sums[lag_idx] += (xa * xb + ya * yb + 2 * za * zb) as i8;
                    } else {
                        let wa: i32 = if (bits_a >> 3) & 1 == 1 { 1 } else { -1 };
                        let wb: i32 = if (bits_b >> 3) & 1 == 1 { 1 } else { -1 };
                        sums[lag_idx] += (2 * wa * wb) as i8;
                    }
                }

                let mut ok = true;
                for &li in &ctx.lag_check_at_level[level] {
                    if sums[li] != 0 { ok = false; break; }
                }

                if ok {
                    children[sign_col as usize] = build_rec(
                        level + 1, sums, &mut current_active_vals,
                        ctx, nodes, unique, memo,
                    );
                }

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
        let mut active_bits: Vec<u8> = Vec::new();
        let root = build_rec(
            0, &mut sums, &mut active_bits,
            &ctx, &mut nodes, &mut unique, &mut memo,
        );

        eprintln!("MDD k={}: {} nodes, {:.1} MB",
            k, nodes.len(), nodes.len() as f64 * 64.0 / 1_048_576.0);

        BoundaryMdd { nodes, root, k, pos_order }
    }

    /// Walk the MDD with z,w bits fixed, collecting valid (x_bits, y_bits) pairs.
    /// The z,w bits are packed as: bits 0..k-1 = prefix, bits k..2k-1 = suffix.
    pub fn query_xy(&self, z_bits: u32, w_bits: u32, out: &mut Vec<(u32, u32)>) {
        out.clear();
        self.walk_xy(self.root, 0, z_bits, w_bits, 0, 0, out);
    }

    fn walk_xy(&self, nid: u32, level: usize, z_bits: u32, w_bits: u32,
               x_acc: u32, y_acc: u32, out: &mut Vec<(u32, u32)>) {
        if nid == DEAD { return; }
        if level == 2 * self.k {
            if nid == LEAF {
                out.push((x_acc, y_acc));
            }
            return;
        }

        let pos = self.pos_order[level];
        let z_val = (z_bits >> pos) & 1;
        let w_val = (w_bits >> pos) & 1;

        // z=bit2, w=bit3 in sign_col encoding
        let zw_bits = (z_val << 2) | (w_val << 3);

        // Try all 4 (x,y) combinations with these fixed z,w
        for xy in 0u32..4 {
            let sign_col = xy | zw_bits;
            let child = self.nodes[nid as usize][sign_col as usize];
            if child == DEAD { continue; }

            let x_val = (xy >> 0) & 1;
            let y_val = (xy >> 1) & 1;
            let new_x = x_acc | (x_val << pos);
            let new_y = y_acc | (y_val << pos);

            self.walk_xy(child, level + 1, z_bits, w_bits, new_x, new_y, out);
        }
    }

    #[allow(dead_code)]
    /// Build a 4-way ZW projection: for each 16-way node, OR together the
    /// (x,y) children for each (z,w) branch. The result is a 4-way MDD where
    /// every path is a valid (z,w) boundary (has at least one valid x,y).
    pub fn project_zw(&self) -> ZwProjection {
        let mut nodes_4: Vec<[u32; 4]> = Vec::new();
        nodes_4.push([DEAD; 4]); // node 0 = DEAD

        let mut unique_4: HashMap<(u8, [u32; 4]), u32> = HashMap::new();
        let mut memo: HashMap<u32, u32> = HashMap::new();

        let root = Self::project_node(
            self.root, 0, &self.nodes, self.k,
            &mut nodes_4, &mut unique_4, &mut memo,
        );

        eprintln!("ZW projection: {} nodes (4-way)", nodes_4.len());
        ZwProjection { nodes: nodes_4, root, k: self.k, pos_order: self.pos_order.clone() }
    }

    fn project_node(
        nid: u32, level: u8,
        nodes_16: &[[u32; 16]],
        k: usize,
        nodes_4: &mut Vec<[u32; 4]>,
        unique_4: &mut HashMap<(u8, [u32; 4]), u32>,
        memo: &mut HashMap<u32, u32>,
    ) -> u32 {
        if nid == DEAD { return DEAD; }
        if nid == LEAF { return LEAF; }
        if let Some(&cached) = memo.get(&nid) { return cached; }

        let mut children_4 = [DEAD; 4];
        for zw in 0u32..4 {
            let z_val = (zw >> 0) & 1;
            let w_val = (zw >> 1) & 1;
            let zw_bits = (z_val << 2) | (w_val << 3);

            // OR over all (x,y) branches: collect unique projected children
            // and merge them. For now, use a simple approach: if any (x,y)
            // leads to LEAF, the projected child is LEAF. Otherwise, recurse
            // into each unique child and pick the first non-DEAD result.
            // (This loses some paths but is correct for existence queries.)
            //
            // Actually, we need the full union. But for enumerate_zw we only
            // need existence (is this (z,w) branch viable?), not the count.
            // So: projected[zw] = LEAF if any path exists, DEAD otherwise.
            // But we want to WALK the projection, so we need structure.
            //
            // Simple correct approach: if all 4 (x,y) children project to the
            // same node, use that. Otherwise, we'd need an Apply(OR). For now,
            // just check existence: projected[zw] = project(first non-DEAD child).
            // This may miss some (z,w) paths that are only valid through specific (x,y).

            // Collect all unique non-DEAD children for this zw
            let mut child_16s: Vec<u32> = Vec::new();
            for xy in 0u32..4 {
                let sign_col = xy | zw_bits;
                let child = nodes_16[nid as usize][sign_col as usize];
                if child != DEAD && !child_16s.contains(&child) {
                    child_16s.push(child);
                }
            }

            if child_16s.is_empty() {
                children_4[zw as usize] = DEAD;
            } else if child_16s.len() == 1 {
                // All live (x,y) lead to the same subtree — project it
                children_4[zw as usize] = Self::project_node(
                    child_16s[0], level + 1, nodes_16, k,
                    nodes_4, unique_4, memo,
                );
            } else {
                // Multiple distinct subtrees. Project each and OR them together.
                // For a correct projection, we need Apply(OR) on the projected children.
                // Simple version: project each, then merge.
                let mut merged = DEAD;
                for &c16 in &child_16s {
                    let projected = Self::project_node(
                        c16, level + 1, nodes_16, k,
                        nodes_4, unique_4, memo,
                    );
                    merged = or_4way(merged, projected, level + 1, nodes_4, unique_4);
                }
                children_4[zw as usize] = merged;
            }
        }

        // Reduce
        if children_4.iter().all(|&c| c == DEAD) {
            memo.insert(nid, DEAD);
            return DEAD;
        }
        let first = children_4[0];
        if children_4.iter().all(|&c| c == first) {
            memo.insert(nid, first);
            return first;
        }

        let key = (level, children_4);
        let result = if let Some(&existing) = unique_4.get(&key) {
            existing
        } else {
            let id = nodes_4.len() as u32;
            nodes_4.push(children_4);
            unique_4.insert(key, id);
            id
        };
        memo.insert(nid, result);
        result
    }
}

#[allow(dead_code)]
/// OR two 4-way MDD nodes: result has a branch if either input has it.
fn or_4way(
    a: u32, b: u32, level: u8,
    nodes: &mut Vec<[u32; 4]>,
    unique: &mut HashMap<(u8, [u32; 4]), u32>,
) -> u32 {
    if a == DEAD { return b; }
    if b == DEAD { return a; }
    if a == LEAF || b == LEAF { return LEAF; }
    if a == b { return a; }

    let a_ch = nodes[a as usize];
    let b_ch = nodes[b as usize];
    let mut children = [DEAD; 4];
    for i in 0..4 {
        children[i] = or_4way(a_ch[i], b_ch[i], level + 1, nodes, unique);
    }

    if children.iter().all(|&c| c == DEAD) { return DEAD; }
    let first = children[0];
    if children.iter().all(|&c| c == first) { return first; }

    let key = (level, children);
    if let Some(&existing) = unique.get(&key) { return existing; }
    let id = nodes.len() as u32;
    nodes.push(children);
    unique.insert(key, id);
    id
}

/// 4-way ZW projection MDD. Each path is a valid (z,w) boundary.
#[allow(dead_code)]
pub struct ZwProjection {
    pub nodes: Vec<[u32; 4]>,
    pub root: u32,
    pub k: usize,
    pub pos_order: Vec<usize>,
}

#[allow(dead_code)]
impl ZwProjection {
    /// Enumerate all valid (z_bits, w_bits) boundary pairs.
    pub fn enumerate<F: FnMut(u32, u32)>(&self, mut callback: F) {
        self.walk(self.root, 0, 0, 0, &mut callback);
    }

    fn walk<F: FnMut(u32, u32)>(
        &self, nid: u32, level: usize, z_acc: u32, w_acc: u32, callback: &mut F,
    ) {
        if nid == DEAD { return; }
        if level == 2 * self.k {
            if nid == LEAF { callback(z_acc, w_acc); }
            return;
        }

        let pos = self.pos_order[level];
        for zw in 0u32..4 {
            let child = self.nodes[nid as usize][zw as usize];
            if child == DEAD { continue; }
            let z_val = (zw >> 0) & 1;
            let w_val = (zw >> 1) & 1;
            if child == LEAF {
                // All deeper positions are don't-care for ZW — enumerate remaining
                self.walk_leaf(level + 1, z_acc | (z_val << pos), w_acc | (w_val << pos), callback);
            } else {
                self.walk(child, level + 1, z_acc | (z_val << pos), w_acc | (w_val << pos), callback);
            }
        }
    }

    /// When we hit a LEAF in the projection, all remaining positions are free.
    /// Enumerate all 4^remaining (z,w) completions.
    fn walk_leaf<F: FnMut(u32, u32)>(
        &self, level: usize, z_acc: u32, w_acc: u32, callback: &mut F,
    ) {
        if level == 2 * self.k {
            callback(z_acc, w_acc);
            return;
        }
        let pos = self.pos_order[level];
        for zw in 0u32..4 {
            let z_val = (zw >> 0) & 1;
            let w_val = (zw >> 1) & 1;
            self.walk_leaf(level + 1, z_acc | (z_val << pos), w_acc | (w_val << pos), callback);
        }
    }

    /// Count total valid (z,w) pairs.
    pub fn count_paths(&self) -> u128 {
        let mut memo: HashMap<u32, u128> = HashMap::new();
        fn count(nid: u32, nodes: &[[u32; 4]], memo: &mut HashMap<u32, u128>) -> u128 {
            if nid == DEAD { return 0; }
            if nid == LEAF { return 1; }
            if let Some(&c) = memo.get(&nid) { return c; }
            let total: u128 = nodes[nid as usize].iter()
                .map(|&child| count(child, nodes, memo)).sum();
            memo.insert(nid, total);
            total
        }
        count(self.root, &self.nodes, &mut memo)
    }
}

impl BoundaryMdd {
    /// Enumerate all valid (z,w,x,y) boundary 4-tuples.
    /// More efficient than enumerate_zw + query_xy because it walks once.
    /// Walk the MDD collecting all unique (z_bits, w_bits) that have any valid (x,y).
    /// At each level, try all 4 (z,w) choices. For each, check if any (x,y) child
    /// is non-DEAD. If so, collect unique child nodes and recurse.
    /// Dedup at leaf via HashSet.
    pub fn walk_zw_unique(
        &self, nid: u32, level: usize, z_acc: u32, w_acc: u32,
        out: &mut std::collections::HashSet<(u32, u32)>,
    ) {
        if nid == DEAD { return; }
        if level == 2 * self.k {
            if nid == LEAF {
                out.insert((z_acc, w_acc));
            }
            return;
        }

        let pos = self.pos_order[level];
        for zw in 0u32..4 {
            let z_val = (zw >> 0) & 1;
            let w_val = (zw >> 1) & 1;
            let zw_sign = (z_val << 2) | (w_val << 3);

            // Collect unique non-DEAD child nodes across all (x,y) branches
            let mut child_set: Vec<u32> = Vec::with_capacity(4);
            for xy in 0u32..4 {
                let sign_col = xy | zw_sign;
                let child = self.nodes[nid as usize][sign_col as usize];
                if child != DEAD && !child_set.contains(&child) {
                    child_set.push(child);
                }
            }
            if child_set.is_empty() { continue; }

            let new_z = z_acc | (z_val << pos);
            let new_w = w_acc | (w_val << pos);

            for &child in &child_set {
                self.walk_zw_unique(child, level + 1, new_z, new_w, out);
            }
        }
    }

    #[allow(dead_code)]
    pub fn enumerate_all<F: FnMut(u32, u32, u32, u32)>(&self, mut callback: F) {
        self.walk_all(self.root, 0, 0, 0, 0, 0, &mut callback);
    }

    fn walk_all<F: FnMut(u32, u32, u32, u32)>(
        &self, nid: u32, level: usize,
        x_acc: u32, y_acc: u32, z_acc: u32, w_acc: u32,
        callback: &mut F,
    ) {
        if nid == DEAD { return; }
        if level == 2 * self.k {
            if nid == LEAF {
                callback(x_acc, y_acc, z_acc, w_acc);
            }
            return;
        }

        let pos = self.pos_order[level];
        for sign_col in 0u32..16 {
            let child = self.nodes[nid as usize][sign_col as usize];
            if child == DEAD { continue; }

            let x_val = (sign_col >> 0) & 1;
            let y_val = (sign_col >> 1) & 1;
            let z_val = (sign_col >> 2) & 1;
            let w_val = (sign_col >> 3) & 1;

            self.walk_all(
                child, level + 1,
                x_acc | (x_val << pos),
                y_acc | (y_val << pos),
                z_acc | (z_val << pos),
                w_acc | (w_val << pos),
                callback,
            );
        }
    }
}
