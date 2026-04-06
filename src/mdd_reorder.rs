/// Reorder a 16-way interleaved MDD into a 4-way ZW-first MDD.
///
/// Step 1: Split each 16-way node into two 4-way levels (zw, then xy).
/// Step 2: Adjacent-swap xy levels down past zw levels to group them.
///
/// Result: depth 4k, first 2k levels branch on (z,w), last 2k on (x,y).
/// Each ZW path arrives at a node that roots the XY sub-MDD.

use std::collections::HashMap;

pub const DEAD: u32 = 0;
pub const LEAF: u32 = u32::MAX;

pub struct Mdd4 {
    pub nodes: Vec<[u32; 4]>,
    pub root: u32,
    pub depth: usize, // total levels
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
    let mut unique: HashMap<(u16, [u32; 4]), u32> = HashMap::new();
    let mut memo: HashMap<u32, u32> = HashMap::new();

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
    Mdd4 { nodes: nodes_4, root, depth: depth_4 }
}

/// Swap two adjacent levels in a 4-way MDD.
/// Level `level` and `level+1` exchange positions.
/// Returns the new root (if swapping level 0, root changes).
pub fn swap_adjacent(mdd: &mut Mdd4, unique: &mut HashMap<(u16, [u32; 4]), u32>, level: u16) {
    // Collect all nodes at `level` that need swapping
    // For each node at `level`: its children are at `level+1`.
    // After swap: node at `level` branches on what was `level+1`'s variable,
    // and each child branches on what was `level`'s variable.
    //
    // For node N at level L with children C[0..3]:
    //   Each C[i] at level L+1 has children D[i][0..3] at level L+2.
    //
    // After swap, new node N' at level L:
    //   N'[j] = new node at level L+1
    //   N'[j][i] = D[i][j]  (the old grandchild reached by going i then j)
    //
    // So: new_children_at_L[j] = make_node(L+1, [D[0][j], D[1][j], D[2][j], D[3][j]])
    //     new_N = make_node(L, new_children_at_L)

    // We need to find all nodes reachable at `level` and rebuild them.
    // But we don't track which nodes are at which level.
    // Instead, rebuild the full MDD from root, transforming nodes at `level`.

    let old_nodes = mdd.nodes.clone();
    let mut new_nodes: Vec<[u32; 4]> = Vec::new();
    new_nodes.push([DEAD; 4]); // DEAD sentinel
    let mut new_unique: HashMap<(u16, [u32; 4]), u32> = HashMap::new();
    let mut memo: HashMap<u32, u32> = HashMap::new();

    fn rebuild(
        nid: u32,
        current_level: u16,
        swap_level: u16,
        old_nodes: &[[u32; 4]],
        new_nodes: &mut Vec<[u32; 4]>,
        new_unique: &mut HashMap<(u16, [u32; 4]), u32>,
        memo: &mut HashMap<u32, u32>,
    ) -> u32 {
        if nid == DEAD { return DEAD; }
        if nid == LEAF { return LEAF; }
        if let Some(&cached) = memo.get(&nid) { return cached; }

        if current_level == swap_level {
            // This node is at the swap level. Restructure.
            let ch = old_nodes[nid as usize]; // children at swap_level+1

            // Grandchildren: D[i][j] where i indexes ch (old level variable),
            // j indexes ch[i]'s children (old level+1 variable)
            let mut d = [[DEAD; 4]; 4];
            for i in 0..4 {
                if ch[i] == DEAD {
                    d[i] = [DEAD; 4];
                } else if ch[i] == LEAF {
                    d[i] = [LEAF; 4];
                } else {
                    d[i] = old_nodes[ch[i] as usize];
                }
            }

            // New structure: branch on old level+1 variable first, then old level variable
            let mut new_ch = [DEAD; 4]; // new children (branching on old level+1 var)
            for j in 0..4 {
                let mut inner = [DEAD; 4]; // branching on old level var
                for i in 0..4 {
                    inner[i] = rebuild(
                        d[i][j], current_level + 2, swap_level,
                        old_nodes, new_nodes, new_unique, memo,
                    );
                }
                new_ch[j] = Mdd4::make_node(new_nodes, new_unique, swap_level + 1, inner);
            }
            let result = Mdd4::make_node(new_nodes, new_unique, swap_level, new_ch);
            memo.insert(nid, result);
            result
        } else {
            // Not at swap level — just copy, recursing into children
            let ch = old_nodes[nid as usize];
            let mut new_ch = [DEAD; 4];
            for i in 0..4 {
                new_ch[i] = rebuild(
                    ch[i], current_level + 1, swap_level,
                    old_nodes, new_nodes, new_unique, memo,
                );
            }
            let result = Mdd4::make_node(new_nodes, new_unique, current_level, new_ch);
            memo.insert(nid, result);
            result
        }
    }

    let new_root = rebuild(
        mdd.root, 0, level,
        &old_nodes, &mut new_nodes, &mut new_unique, &mut memo,
    );

    mdd.nodes = new_nodes;
    mdd.root = new_root;
    *unique = new_unique;
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

    let mut unique: HashMap<(u16, [u32; 4]), u32> = HashMap::new();
    let total_swaps = k * (k - 1); // rough estimate
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

    let mut pass = 0;
    loop {
        let mut swapped = false;
        for i in 0..total_levels - 1 {
            if !labels[i] && labels[i + 1] {
                // xy before zw — swap them
                swap_adjacent(&mut mdd4, &mut unique, i as u16);
                labels.swap(i, i + 1);
                swaps_done += 1;
                swapped = true;
            }
        }
        pass += 1;
        eprintln!("  Reorder pass {}: {} swaps total, {} nodes", pass, swaps_done, mdd4.nodes.len());
        if !swapped { break; }
    }

    eprintln!("  Reorder complete: {} swaps, {} nodes", swaps_done, mdd4.nodes.len());
    mdd4
}
