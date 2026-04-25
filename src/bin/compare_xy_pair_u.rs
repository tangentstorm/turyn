use std::collections::HashMap;
use turyn::mdd_zw_first::{self, DEAD, LEAF, ZwFirstMdd};

fn count_paths4(nid: u32, level: usize, depth: usize, nodes: &[[u32; 4]]) -> u128 {
    if nid == DEAD {
        return 0;
    }
    if nid == LEAF {
        return 4u128.pow((depth - level) as u32);
    }
    nodes[nid as usize]
        .iter()
        .map(|&c| count_paths4(c, level + 1, depth, nodes))
        .sum()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(7);

    eprintln!("Comparing standalone XY builders for k={}", k);
    let full = ZwFirstMdd::build(k);

    let mut sums_groups: HashMap<Vec<i8>, usize> = HashMap::new();
    full.enumerate_zw(|z_bits, w_bits, _xy_root| {
        let mut zw_sums = vec![0i8; k];
        for j in 0..k {
            let mut sum = 0i32;
            for i in 0..k - j {
                let pos_a = i;
                let pos_b = k + i + j;
                let za = if (z_bits >> pos_a) & 1 == 1 { 1i32 } else { -1 };
                let zb = if (z_bits >> pos_b) & 1 == 1 { 1i32 } else { -1 };
                sum += 2 * za * zb;
            }
            if j < k - 1 {
                for i in 0..k - j - 1 {
                    let pos_a = i;
                    let pos_b = k + i + j + 1;
                    let wa = if (w_bits >> pos_a) & 1 == 1 { 1i32 } else { -1 };
                    let wb = if (w_bits >> pos_b) & 1 == 1 { 1i32 } else { -1 };
                    sum += 2 * wa * wb;
                }
            }
            zw_sums[j] = sum as i8;
        }
        *sums_groups.entry(zw_sums).or_insert(0) += 1;
    });

    eprintln!("Distinct zw_sums: {}", sums_groups.len());

    let mut old_nodes_total = 0usize;
    let mut new_nodes_total = 0usize;
    let mut old_paths_total = 0u128;
    let mut new_paths_total = 0u128;
    let mut subset_boundaries = 0usize;
    let mut tested = 0usize;

    for zw_sums in sums_groups.keys() {
        tested += 1;
        let (old_nodes, old_root) = mdd_zw_first::build_xy_for_boundary_raw(k, zw_sums);
        let (new_nodes, new_root) = mdd_zw_first::build_xy_structural_for_boundary(k, zw_sums);
        old_nodes_total += old_nodes.len();
        new_nodes_total += new_nodes.len();
        let old_paths = count_paths4(old_root, 0, 2 * k, &old_nodes);
        let new_paths = count_paths4(new_root, 0, 2 * k, &new_nodes);
        old_paths_total += old_paths;
        new_paths_total += new_paths;
        if new_paths <= old_paths {
            subset_boundaries += 1;
        }
        if tested % 1000 == 0 {
            eprintln!("  tested {}", tested);
        }
    }

    eprintln!("Results over {} distinct boundaries:", tested);
    eprintln!("  old total nodes: {}", old_nodes_total);
    eprintln!("  new total nodes: {}", new_nodes_total);
    eprintln!("  old total paths: {}", old_paths_total);
    eprintln!("  new total paths: {}", new_paths_total);
    eprintln!(
        "  boundaries with new<=old path count: {}",
        subset_boundaries
    );
    if tested > 0 {
        eprintln!(
            "  avg old nodes: {:.1}",
            old_nodes_total as f64 / tested as f64
        );
        eprintln!(
            "  avg new nodes: {:.1}",
            new_nodes_total as f64 / tested as f64
        );
    }
}
