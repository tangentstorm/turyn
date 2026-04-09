/// Reorder a 16-way interleaved MDD into a 4-way ZW-first MDD.
///
/// Step 1: Split each 16-way node into two 4-way levels (zw, then xy).
/// Step 2: Adjacent-swap xy levels down past zw levels to group them.
///
/// Result: depth 4k, first 2k levels branch on (z,w), last 2k on (x,y).
/// Each ZW path arrives at a node that roots the XY sub-MDD.

use rustc_hash::FxHashMap as HashMap;
use std::io::Write;

pub const DEAD: u32 = 0;
pub const LEAF: u32 = u32::MAX;

pub struct Mdd4 {
    pub nodes: Vec<[u32; 4]>,
    pub root: u32,
    pub k: usize,
    pub depth: usize, // total levels = 4k
}

impl Mdd4 {
    /// Count the number of live (non-DEAD) paths through the full MDD.
    /// Uses memoization. Returns f64 because path counts can exceed 2^64.
    pub fn count_live_paths(&self) -> f64 {
        let mut cache: std::collections::HashMap<u32, f64> = std::collections::HashMap::new();
        self.count_paths_from(self.root, 0, &mut cache)
    }

    fn count_paths_from(&self, nid: u32, level: usize, cache: &mut std::collections::HashMap<u32, f64>) -> f64 {
        if nid == DEAD { return 0.0; }
        if nid == LEAF {
            let remaining = self.depth.saturating_sub(level);
            return 4.0f64.powi(remaining as i32);
        }
        if level >= self.depth { return 1.0; }
        if let Some(&c) = cache.get(&nid) { return c; }
        let mut count = 0.0f64;
        for b in 0..4 {
            count += self.count_paths_from(self.nodes[nid as usize][b], level + 1, cache);
        }
        cache.insert(nid, count);
        count
    }
    /// Save to binary file. Format: magic "MDD4", k (u32), root (u32), node_count (u32), node data.
    pub fn save(&self, path: &str) -> std::io::Result<()> {
        let mut f = std::io::BufWriter::new(std::fs::File::create(path)?);
        f.write_all(b"MDD4")?;
        f.write_all(&(self.k as u32).to_le_bytes())?;
        f.write_all(&self.root.to_le_bytes())?;
        f.write_all(&(self.nodes.len() as u32).to_le_bytes())?;
        let bytes = unsafe {
            std::slice::from_raw_parts(
                self.nodes.as_ptr() as *const u8,
                self.nodes.len() * 16,
            )
        };
        f.write_all(bytes)?;
        f.flush()?;
        Ok(())
    }

    /// Load from binary file.
    pub fn load(path: &str) -> Option<Self> {
        let data = std::fs::read(path).ok()?;
        if data.len() < 16 { return None; }
        if &data[0..4] != b"MDD4" { return None; }
        let k = u32::from_le_bytes(data[4..8].try_into().ok()?) as usize;
        let root = u32::from_le_bytes(data[8..12].try_into().ok()?);
        let node_count = u32::from_le_bytes(data[12..16].try_into().ok()?) as usize;
        let expected = 16 + node_count * 16;
        if data.len() < expected { return None; }
        let mut nodes = vec![[0u32; 4]; node_count];
        unsafe {
            std::ptr::copy_nonoverlapping(
                data[16..].as_ptr(),
                nodes.as_mut_ptr() as *mut u8,
                node_count * 16,
            );
        }
        Some(Mdd4 { nodes, root, k, depth: 4 * k })
    }
}

impl Mdd4 {
    fn make_node(
        nodes: &mut Vec<[u32; 4]>,
        unique: &mut HashMap<(u16, [u32; 4]), u32>,
        level: u16,
        children: [u32; 4],
    ) -> u32 {
        if children.iter().all(|&c| c == DEAD) { return DEAD; }
        let first = children[0];
        if children.iter().all(|&c| c == first) { return first; }
        let key = (level, children);
        if let Some(&nid) = unique.get(&key) { return nid; }
        let nid = nodes.len() as u32;
        nodes.push(children);
        unique.insert(key, nid);
        nid
    }
}

/// Split a 16-way MDD into a 4-way MDD with double the depth.
/// At each original level, create two 4-way levels:
///   - First: branch on (z,w) = bits 2-3 of sign_col
///   - Second: branch on (x,y) = bits 0-1 of sign_col
pub fn split_16_to_4(
    nodes_16: &[[u32; 16]],
    root_16: u32,
    depth_16: usize,
) -> Mdd4 {
    let depth_4 = depth_16 * 2;
    let mut nodes_4: Vec<[u32; 4]> = Vec::new();
    nodes_4.push([DEAD; 4]); // node 0 = DEAD
    let mut unique: HashMap<(u16, [u32; 4]), u32> = HashMap::default();
    let mut memo: HashMap<u32, u32> = HashMap::default();

    fn convert(
        nid_16: u32,
        level_16: usize,
        depth_16: usize,
        nodes_16: &[[u32; 16]],
        nodes_4: &mut Vec<[u32; 4]>,
        unique: &mut HashMap<(u16, [u32; 4]), u32>,
        memo: &mut HashMap<u32, u32>,
    ) -> u32 {
        if nid_16 == DEAD { return DEAD; }
        if nid_16 == LEAF { return LEAF; }
        if let Some(&cached) = memo.get(&nid_16) { return cached; }

        let level_4_zw = (level_16 * 2) as u16;
        let level_4_xy = level_4_zw + 1;
        let ch16 = &nodes_16[nid_16 as usize];

        // For each (z,w) branch, create an (x,y) sub-node
        let mut zw_children = [DEAD; 4];
        for zw in 0u32..4 {
            let zw_bits = zw << 2; // z=bit2, w=bit3
            let mut xy_children = [DEAD; 4];
            for xy in 0u32..4 {
                let sign_col = xy | zw_bits;
                let child_16 = ch16[sign_col as usize];
                xy_children[xy as usize] = convert(
                    child_16, level_16 + 1, depth_16,
                    nodes_16, nodes_4, unique, memo,
                );
            }
            zw_children[zw as usize] = Mdd4::make_node(nodes_4, unique, level_4_xy, xy_children);
        }
        let result = Mdd4::make_node(nodes_4, unique, level_4_zw, zw_children);
        memo.insert(nid_16, result);
        result
    }

    let root = convert(root_16, 0, depth_16, nodes_16, &mut nodes_4, &mut unique, &mut memo);
    Mdd4 { nodes: nodes_4, root, k: depth_16 / 2, depth: depth_4 }
}

/// Swap two adjacent levels in a 4-way MDD (in-place).
/// Only touches nodes at `level` (mutated) and creates new nodes at `level+1`.
/// Nodes above level keep the same IDs; nodes below level+2 are unchanged.
fn swap_adjacent_inplace(mdd: &mut Mdd4, level: u16) {
    // Walk from root to collect all node IDs reachable at `level`.
    let mut at_level: Vec<u32> = Vec::new();
    {
        let mut visited = vec![false; mdd.nodes.len()];
        fn collect(
            nid: u32, current: u16, target: u16,
            nodes: &[[u32; 4]], visited: &mut [bool],
            result: &mut Vec<u32>,
        ) {
            if nid == DEAD || nid == LEAF { return; }
            let idx = nid as usize;
            if visited[idx] { return; }
            visited[idx] = true;
            if current == target {
                result.push(nid);
                return;
            }
            for &ch in &nodes[idx] {
                collect(ch, current + 1, target, nodes, visited, result);
            }
        }
        collect(mdd.root, 0, level, &mdd.nodes, &mut visited, &mut at_level);
    }

    // For each node at `level`, transpose grandchildren and create new inner nodes.
    //
    // Before: node branches on var_L, children branch on var_{L+1}
    //   node[i] = C_i, C_i[j] = D[i][j] (grandchild at level L+2)
    //
    // After:  node branches on var_{L+1}, children branch on var_L
    //   node[j] = new_inner_j, new_inner_j[i] = D[i][j]
    let mut inner_unique: HashMap<[u32; 4], u32> = HashMap::default();

    for &nid in &at_level {
        let ch = mdd.nodes[nid as usize];

        // Read grandchildren D[i][j]
        let mut d = [[DEAD; 4]; 4];
        for i in 0..4 {
            d[i] = if ch[i] == DEAD { [DEAD; 4] }
                   else if ch[i] == LEAF { [LEAF; 4] }
                   else { mdd.nodes[ch[i] as usize] };
        }

        // Transpose: new_ch[j] has children [D[0][j], D[1][j], D[2][j], D[3][j]]
        let mut new_ch = [DEAD; 4];
        for j in 0..4 {
            let inner = [d[0][j], d[1][j], d[2][j], d[3][j]];
            if inner.iter().all(|&c| c == DEAD) {
                new_ch[j] = DEAD;
            } else {
                let first = inner[0];
                if inner.iter().all(|&c| c == first) {
                    new_ch[j] = first;
                } else if let Some(&existing) = inner_unique.get(&inner) {
                    new_ch[j] = existing;
                } else {
                    let new_nid = mdd.nodes.len() as u32;
                    mdd.nodes.push(inner);
                    inner_unique.insert(inner, new_nid);
                    new_ch[j] = new_nid;
                }
            }
        }

        // Mutate level-L node in place
        mdd.nodes[nid as usize] = new_ch;
    }
    // Note: old level-(L+1) nodes that are no longer referenced become garbage.
    // This is acceptable — they waste space but don't affect correctness.
}

/// Reorder a 16-way interleaved MDD so z,w decisions come first.
/// Returns a 4-way MDD with depth 4k: first 2k levels = (z,w), last 2k = (x,y).
pub fn reorder_zw_first(
    nodes_16: &[[u32; 16]],
    root_16: u32,
    k: usize,
) -> Mdd4 {
    let depth_16 = 2 * k;
    eprintln!("Splitting 16-way → 4-way ({} → {} levels)...", depth_16, depth_16 * 2);
    let mut mdd4 = split_16_to_4(nodes_16, root_16, depth_16);
    eprintln!("  Split: {} nodes", mdd4.nodes.len());

    // Current order: zw0, xy0, zw1, xy1, zw2, xy2, ...
    // Target order:  zw0, zw1, zw2, ..., xy0, xy1, xy2, ...
    // Strategy: bubble each xy level rightward past subsequent zw levels.
    // xy0 is at position 1, needs to move to position 2k.
    // xy1 is at position 3, needs to move to position 2k+1.
    // etc.

    let mut swaps_done = 0;

    // For each xy level (originally at positions 1, 3, 5, ..., 2k-1),
    // bubble it rightward past all subsequent zw levels.
    // After processing xy_i, the order is:
    //   zw0, zw1, ..., zw_i, xy0, ..., xy_i, zw_{i+1}, xy_{i+1}, ...
    // Wait, this is tricky. Let me think step by step.
    //
    // Start: zw0 xy0 zw1 xy1 zw2 xy2 ... zw_{k-1} xy_{k-1}
    //
    // Bubble xy0 right past zw1: swap positions 1,2
    //   zw0 zw1 xy0 xy1 zw2 xy2 ...
    // Bubble xy0 right past xy1: swap positions 2,3 — but xy0 and xy1 are same type!
    // Actually we only need to move xy past zw, not past other xy.
    //
    // Better: move each xy level to the end, one at a time.
    // Start: zw0 xy0 zw1 xy1 zw2 xy2
    //   Move xy0: swap(1,2) → zw0 zw1 xy0 xy1 zw2 xy2
    //             swap(2,3) → zw0 zw1 xy1 xy0 zw2 xy2
    //             swap(3,4) → zw0 zw1 xy1 zw2 xy0 xy2
    //             swap(4,5) → zw0 zw1 xy1 zw2 xy2 xy0
    //   Now xy0 is at the end. But the intermediate swaps moved xy1 left.
    //
    // Hmm, this is a sorting problem. Simpler: just do bubble sort.
    // Label each level: Z (zw) or X (xy).
    // Current: Z X Z X Z X ...
    // Target:  Z Z Z ... X X X ...
    // Bubble sort: scan left to right, swap adjacent X Z → Z X.

    let total_levels = mdd4.depth; // = 4k
    // After split, order is: zw_pos0, xy_pos0, zw_pos1, xy_pos1, ...
    // Each pair of levels covers one boundary position.
    let mut labels: Vec<bool> = Vec::with_capacity(total_levels);
    for _ in 0..depth_16 {
        labels.push(true);  // zw level
        labels.push(false); // xy level
    }

    // Count total swaps needed for progress reporting
    let total_swaps_needed: usize = {
        let mut tmp = labels.clone();
        let mut count = 0;
        loop {
            let mut any = false;
            for i in 0..tmp.len() - 1 {
                if !tmp[i] && tmp[i + 1] { tmp.swap(i, i + 1); count += 1; any = true; }
            }
            if !any { break; }
        }
        count
    };

    let mut pass = 0;
    let reorder_start = std::time::Instant::now();
    let gc_threshold = 10_000_000; // GC when nodes exceed 10M
    loop {
        let mut swapped = false;
        for i in 0..total_levels - 1 {
            if !labels[i] && labels[i + 1] {
                // xy before zw — swap them
                swap_adjacent_inplace(&mut mdd4, i as u16);
                labels.swap(i, i + 1);
                swaps_done += 1;
                swapped = true;
                if total_swaps_needed >= 10 {
                    eprint!("\r  Reorder: swap {}/{}, {} nodes, {:.1?}   ",
                        swaps_done, total_swaps_needed, mdd4.nodes.len(), reorder_start.elapsed());
                }
            }
        }
        pass += 1;
        // Periodic GC to keep memory bounded during reorder
        if mdd4.nodes.len() > gc_threshold {
            let before = mdd4.nodes.len();
            gc_mdd(&mut mdd4);
            eprintln!("\r  Reorder pass {}: {} swaps, GC {} → {} nodes, {:.1?}",
                pass, swaps_done, before, mdd4.nodes.len(), reorder_start.elapsed());
        } else {
            eprintln!("\r  Reorder pass {}: {} swaps total, {} nodes, {:.1?}",
                pass, swaps_done, mdd4.nodes.len(), reorder_start.elapsed());
        }
        if !swapped { break; }
    }

    eprintln!("  Reorder complete: {} swaps, {} nodes (before final GC)", swaps_done, mdd4.nodes.len());

    // Final garbage-collect
    gc_mdd(&mut mdd4);
    eprintln!("  After GC: {} nodes", mdd4.nodes.len());

    mdd4
}

/// Remove unreachable nodes and compact the node array.
fn gc_mdd(mdd: &mut Mdd4) {
    let n = mdd.nodes.len();
    let mut reachable = vec![false; n];
    // Mark reachable nodes via DFS from root
    fn mark(nid: u32, nodes: &[[u32; 4]], reachable: &mut [bool]) {
        if nid == DEAD || nid == LEAF { return; }
        let idx = nid as usize;
        if reachable[idx] { return; }
        reachable[idx] = true;
        for &ch in &nodes[idx] {
            mark(ch, nodes, reachable);
        }
    }
    mark(mdd.root, &mdd.nodes, &mut reachable);
    reachable[0] = true; // DEAD sentinel

    // Build compacted array with new IDs
    let mut old_to_new = vec![0u32; n];
    let mut new_nodes: Vec<[u32; 4]> = Vec::new();
    for (old_id, &is_reachable) in reachable.iter().enumerate() {
        if is_reachable {
            old_to_new[old_id] = new_nodes.len() as u32;
            new_nodes.push(mdd.nodes[old_id]);
        }
    }
    // Remap children
    for node in &mut new_nodes {
        for ch in node.iter_mut() {
            if *ch != DEAD && *ch != LEAF {
                *ch = old_to_new[*ch as usize];
            }
        }
    }
    mdd.root = if mdd.root == DEAD || mdd.root == LEAF { mdd.root }
               else { old_to_new[mdd.root as usize] };
    mdd.nodes = new_nodes;
}
