/// Analyze an MDD file: count ZW leaf nodes, unique XY roots, path counts.
/// Usage: analyze_mdd [file]

use std::collections::{HashMap, HashSet};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let file = args.get(1).map(|s| s.as_str()).unwrap_or("mdd-10.bin");

    eprintln!("Loading {}...", file);
    let mdd = turyn::mdd_reorder::Mdd4::load(file).expect("Failed to load MDD");
    let k = mdd.k;
    let zw_depth = 2 * k;

    // Bouncing order
    let mut pos_order: Vec<usize> = Vec::with_capacity(2 * k);
    for t in 0..k {
        pos_order.push(t);
        pos_order.push(2 * k - 1 - t);
    }

    eprintln!("Loaded: k={}, {} nodes, depth={}, ZW depth={}",
        k, mdd.nodes.len(), mdd.depth, zw_depth);

    // Collect all unique node IDs reachable at the ZW boundary (depth 2k).
    // These are the XY sub-MDD roots.
    let mut at_depth: HashSet<u32> = HashSet::new();
    fn collect_at_depth(
        nid: u32, level: usize, target: usize,
        nodes: &[[u32; 4]], visited: &mut HashSet<(u32, usize)>,
        result: &mut HashSet<u32>,
    ) {
        if nid == 0 || nid == u32::MAX { return; }
        if !visited.insert((nid, level)) { return; }
        if level == target {
            result.insert(nid);
            return;
        }
        for &child in &nodes[nid as usize] {
            collect_at_depth(child, level + 1, target, nodes, visited, result);
        }
    }
    let mut visited = HashSet::new();
    collect_at_depth(mdd.root, 0, zw_depth, &mdd.nodes, &mut visited, &mut at_depth);

    eprintln!("Unique XY root nodes at ZW boundary: {}", at_depth.len());

    // Count ZW paths (using memoized path counting)
    let mut path_memo: HashMap<u32, u128> = HashMap::new();
    fn count_zw_paths(
        nid: u32, level: usize, zw_depth: usize,
        nodes: &[[u32; 4]], memo: &mut HashMap<u32, u128>,
    ) -> u128 {
        if nid == 0 { return 0; }
        if level == zw_depth { return 1; } // reached boundary
        if nid == u32::MAX { return 1; } // LEAF
        if let Some(&c) = memo.get(&nid) { return c; }
        let total: u128 = nodes[nid as usize].iter()
            .map(|&child| count_zw_paths(child, level + 1, zw_depth, nodes, memo))
            .sum();
        memo.insert(nid, total);
        total
    }
    let total_paths = count_zw_paths(mdd.root, 0, zw_depth, &mdd.nodes, &mut path_memo);

    eprintln!("Total ZW paths: {}", total_paths);
    eprintln!("Nodes in ZW half (visited): {}", visited.len());

    // Count XY paths per root (just a few examples)
    let mut xy_path_memo: HashMap<u32, u128> = HashMap::new();
    fn count_xy_paths(nid: u32, nodes: &[[u32; 4]], memo: &mut HashMap<u32, u128>) -> u128 {
        if nid == 0 { return 0; }
        if nid == u32::MAX { return 1; }
        if let Some(&c) = memo.get(&nid) { return c; }
        let total: u128 = nodes[nid as usize].iter()
            .map(|&child| count_xy_paths(child, nodes, memo)).sum();
        memo.insert(nid, total);
        total
    }

    let mut total_xy_paths: u128 = 0;
    let mut max_xy_paths: u128 = 0;
    for &root in &at_depth {
        let paths = count_xy_paths(root, &mdd.nodes, &mut xy_path_memo);
        total_xy_paths += paths;
        max_xy_paths = max_xy_paths.max(paths);
    }

    eprintln!("\nSummary:");
    eprintln!("  ZW boundary depth: {}", zw_depth);
    eprintln!("  Unique XY roots: {}", at_depth.len());
    eprintln!("  Total ZW paths: {}", total_paths);
    eprintln!("  Total XY paths (across all roots): {}", total_xy_paths);
    eprintln!("  Max XY paths per root: {}", max_xy_paths);

    // Count unique (zw_sums, z_relevant, w_relevant) states for incremental extension.
    // For k→k+1 extension, we need: zw_sums[0..k-1], z[1..k-1], w[0..k-2]
    // (z[0] is always +1 from symmetry breaking)
    eprintln!("\n--- Incremental extension analysis (k→k+1) ---");

    // Walk ZW half collecting accumulated state at leaves
    let mut extension_states: HashSet<(u128, u32, u32)> = HashSet::new();
    // State: (packed_zw_sums, z_prefix_bits, w_prefix_bits)

    fn walk_for_extension(
        nid: u32, level: usize, zw_depth: usize, k: usize,
        z_acc: u32, w_acc: u32,
        sums: &mut Vec<i32>,
        pos_order: &[usize],
        nodes: &[[u32; 4]],
        // Lag pair info for computing sums
        zw_events_at_level: &Vec<Vec<(usize, usize, usize, bool)>>,
        states: &mut HashSet<(u128, u32, u32)>,
    ) {
        if nid == 0 { return; }
        if level == zw_depth {
            // Pack sums
            let mut packed = 0u128;
            for (i, &s) in sums.iter().enumerate() {
                packed |= ((s as i8 as u8 as u128) & 0xFF) << (i * 8);
            }
            // z_prefix bits 1..k-1 (skip 0, always +1)
            let z_rel = (z_acc >> 1) & ((1 << (k - 1)) - 1);
            // w_prefix bits 0..k-2
            let w_rel = w_acc & ((1 << (k - 1)) - 1);
            states.insert((packed, z_rel, w_rel));
            return;
        }
        if nid == u32::MAX { return; }

        let pos = pos_order[level];
        for branch in 0u32..4 {
            let child = nodes[nid as usize][branch as usize];
            if child == 0 { continue; }
            let z_val = (branch >> 0) & 1;
            let w_val = (branch >> 1) & 1;
            let _z_sign: i32 = if z_val == 1 { 1 } else { -1 };
            let _w_sign: i32 = if w_val == 1 { 1 } else { -1 };

            // Compute lag event contributions at this level
            let sums_backup: Vec<i32> = sums.clone();
            for &(lag_idx, pos_a, pos_b, is_z) in &zw_events_at_level[level] {
                // Get z/w values at pos_a and pos_b
                let za = z_acc | (z_val << pos);
                let wa = w_acc | (w_val << pos);
                let a_z = if (za >> pos_a) & 1 == 1 { 1i32 } else { -1 };
                let b_z = if (za >> pos_b) & 1 == 1 { 1i32 } else { -1 };
                let a_w = if (wa >> pos_a) & 1 == 1 { 1i32 } else { -1 };
                let b_w = if (wa >> pos_b) & 1 == 1 { 1i32 } else { -1 };
                if is_z {
                    sums[lag_idx] += 2 * a_z * b_z;
                } else {
                    sums[lag_idx] += 2 * a_w * b_w;
                }
            }

            walk_for_extension(
                child, level + 1, zw_depth, k,
                z_acc | (z_val << pos), w_acc | (w_val << pos),
                sums, pos_order, nodes, zw_events_at_level, states,
            );
            *sums = sums_backup;
        }
    }

    // Build zw_events_at_level for this k
    let mut pos_to_level_map: Vec<usize> = vec![0; 2 * k];
    for (level, &pos) in pos_order.iter().enumerate() {
        pos_to_level_map[pos] = level;
    }

    let mut zw_events_at_level: Vec<Vec<(usize, usize, usize, bool)>> =
        (0..zw_depth).map(|_| Vec::new()).collect();
    for j in 0..k {
        // Z pairs
        for i in 0..k-j {
            let (a, b) = (i, k + i + j);
            let complete = pos_to_level_map[a].max(pos_to_level_map[b]);
            zw_events_at_level[complete].push((j, a, b, true));
        }
        // W pairs
        if j < k - 1 {
            for i in 0..k-j-1 {
                let (a, b) = (i, k + i + j + 1);
                let complete = pos_to_level_map[a].max(pos_to_level_map[b]);
                zw_events_at_level[complete].push((j, a, b, false));
            }
        }
    }

    let mut sums = vec![0i32; k];
    walk_for_extension(
        mdd.root, 0, zw_depth, k, 0, 0,
        &mut sums, &pos_order, &mdd.nodes, &zw_events_at_level,
        &mut extension_states,
    );

    eprintln!("  Unique extension states (zw_sums, z_rel, w_rel): {}",
        extension_states.len());
    eprintln!("  Extension work: {} × 16 = {} constraint checks",
        extension_states.len(), extension_states.len() * 16);
}
