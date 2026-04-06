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
    eprintln!("  Total 4-tuples: {} (ZW paths × avg XY paths)",
        total_paths * total_xy_paths / at_depth.len() as u128);
}
