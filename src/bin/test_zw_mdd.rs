/// Test ZW-first MDD via reordering from interleaved 16-way MDD.
#[path = "../mdd.rs"]
mod mdd;
#[path = "../mdd_reorder.rs"]
mod mdd_reorder;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3);

    // Build interleaved 16-way MDD
    let interleaved = mdd::BoundaryMdd::build(k);

    // Reorder to ZW-first
    let reordered = mdd_reorder::reorder_zw_first(&interleaved.nodes, interleaved.root, k);

    // Walk the ZW top half (first 2k levels)
    let zw_depth = 2 * k;
    let pos_order = interleaved.pos_order.clone();

    let mut zw_count = 0u64;
    let mut total_xy = 0u128;
    let mut xy_counts: std::collections::HashMap<u32, u128> = std::collections::HashMap::new();

    fn count_xy(nid: u32, level: usize, depth: usize, nodes: &[[u32; 4]],
                memo: &mut std::collections::HashMap<u32, u128>) -> u128 {
        if nid == mdd_reorder::DEAD { return 0; }
        if nid == mdd_reorder::LEAF {
            let remaining = depth - level;
            return 4u128.pow(remaining as u32);
        }
        if let Some(&c) = memo.get(&nid) { return c; }
        let total: u128 = nodes[nid as usize].iter()
            .map(|&child| count_xy(child, level + 1, depth, nodes, memo)).sum();
        memo.insert(nid, total);
        total
    }

    fn walk_zw<F: FnMut(u32, u32, u32)>(
        nid: u32, level: usize, zw_depth: usize,
        z_acc: u32, w_acc: u32,
        pos_order: &[usize],
        nodes: &[[u32; 4]],
        callback: &mut F,
    ) {
        if nid == mdd_reorder::DEAD { return; }
        if level == zw_depth {
            callback(z_acc, w_acc, nid);
            return;
        }
        if nid == mdd_reorder::LEAF {
            // All remaining zw levels are don't-care — enumerate all
            walk_zw_leaf(level, zw_depth, z_acc, w_acc, pos_order, callback);
            return;
        }
        let pos = pos_order[level];
        for branch in 0u32..4 {
            let child = nodes[nid as usize][branch as usize];
            if child == mdd_reorder::DEAD { continue; }
            let z_val = (branch >> 0) & 1;
            let w_val = (branch >> 1) & 1;
            walk_zw(child, level + 1, zw_depth, z_acc | (z_val << pos), w_acc | (w_val << pos),
                    pos_order, nodes, callback);
        }
    }

    fn walk_zw_leaf<F: FnMut(u32, u32, u32)>(
        level: usize, zw_depth: usize, z_acc: u32, w_acc: u32,
        pos_order: &[usize], callback: &mut F,
    ) {
        if level == zw_depth {
            callback(z_acc, w_acc, mdd_reorder::LEAF);
            return;
        }
        let pos = pos_order[level];
        for branch in 0u32..4 {
            let z_val = (branch >> 0) & 1;
            let w_val = (branch >> 1) & 1;
            walk_zw_leaf(level + 1, zw_depth, z_acc | (z_val << pos), w_acc | (w_val << pos),
                         pos_order, callback);
        }
    }

    walk_zw(reordered.root, 0, zw_depth, 0, 0, &pos_order, &reordered.nodes, &mut |z_bits, w_bits, xy_root| {
        zw_count += 1;
        let xy_count = if let Some(&c) = xy_counts.get(&xy_root) { c }
            else {
                let c = count_xy(xy_root, 0, zw_depth, &reordered.nodes, &mut std::collections::HashMap::new());
                xy_counts.insert(xy_root, c);
                c
            };
        total_xy += xy_count;

        if zw_count <= 10 {
            eprintln!("  z={:0width$b} w={:0width$b} → {} XY configs (node {})",
                z_bits, w_bits, xy_count, xy_root, width = 2 * k);
        }
    });

    eprintln!("\nTotal: {} ZW boundaries, {} total XY configs, {} unique XY root nodes",
        zw_count, total_xy, xy_counts.len());
}
