use std::collections::HashMap;
/// Test that build_xy_for_boundary produces correct results by comparing
/// against the full ZW-first MDD builder.
///
/// For each ZW boundary in the full MDD, we:
/// 1. Compute the zw_sums from the boundary bit values
/// 2. Call build_xy_for_boundary(k, &zw_sums)
/// 3. Count XY paths from both the full MDD and standalone builder
/// 4. Verify they match
use turyn::mdd_zw_first::{self, DEAD, LEAF, ZwFirstMdd};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(5);

    eprintln!("Testing build_xy_for_boundary for k={}", k);
    eprintln!("Step 1: Building full MDD...");
    let full_mdd = ZwFirstMdd::build(k);
    eprintln!("  {} nodes, root={}", full_mdd.nodes.len(), full_mdd.root);

    // Collect all ZW boundaries with their XY roots and zw_sums
    let zw_depth = 2 * k;
    let _pos_order = full_mdd.zw_pos_order.clone();

    // We need to compute zw_sums for each ZW boundary.
    // zw_sums[j] = sum of 2*z[i]*z[i+j] + 2*w[i]*w[i+j+1] over all valid pairs
    struct BoundaryInfo {
        z_bits: u32,
        w_bits: u32,
        xy_root: u32,
        zw_sums: Vec<i8>,
    }

    let mut boundaries: Vec<BoundaryInfo> = Vec::new();

    full_mdd.enumerate_zw(|z_bits, w_bits, xy_root| {
        // Compute zw_sums for this boundary
        let mut zw_sums = vec![0i8; k];
        for j in 0..k {
            let mut sum = 0i32;
            // Z pairs: z[i] * z[i+j] for i in 0..k-j (but positions are in 0..2k)
            // In the boundary, z has positions 0..k-1 (short) and k..2k-1 (long)
            // Lag j pairs: (i, k+i+j) for i in 0..k-j
            for i in 0..k - j {
                let pos_a = i;
                let pos_b = k + i + j;
                let za = if (z_bits >> pos_a) & 1 == 1 { 1i32 } else { -1 };
                let zb = if (z_bits >> pos_b) & 1 == 1 { 1i32 } else { -1 };
                sum += 2 * za * zb;
            }
            // W pairs: w[i] * w[i+j+1] for i in 0..k-j-1
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
        boundaries.push(BoundaryInfo {
            z_bits,
            w_bits,
            xy_root,
            zw_sums,
        });
    });

    eprintln!("Step 2: Found {} ZW boundaries", boundaries.len());

    // Count XY paths in the full MDD for each unique xy_root
    let mut full_xy_counts: HashMap<u32, u128> = HashMap::new();
    for b in &boundaries {
        if !full_xy_counts.contains_key(&b.xy_root) {
            let count = full_mdd.count_xy_paths(b.xy_root);
            full_xy_counts.insert(b.xy_root, count);
        }
    }

    // Group boundaries by zw_sums (many boundaries share the same sums)
    let mut sums_groups: HashMap<Vec<i8>, Vec<usize>> = HashMap::new();
    for (i, b) in boundaries.iter().enumerate() {
        sums_groups.entry(b.zw_sums.clone()).or_default().push(i);
    }
    eprintln!("Step 3: {} distinct zw_sums values", sums_groups.len());

    // Test build_xy_for_boundary for each distinct zw_sums
    let mut tested = 0;
    let mut passed = 0;
    let mut failed = 0;

    for (zw_sums, indices) in &sums_groups {
        tested += 1;

        // Build standalone XY sub-MDD
        let (xy_nodes, xy_root) = mdd_zw_first::build_xy_for_boundary(k, zw_sums);

        // Count paths in standalone
        let standalone_count = count_paths(xy_root, 0, zw_depth, &xy_nodes);

        // Get full MDD count (all boundaries with this zw_sums should have same XY count)
        let first_idx = indices[0];
        let full_count = *full_xy_counts.get(&boundaries[first_idx].xy_root).unwrap();

        if standalone_count == full_count {
            passed += 1;
        } else {
            failed += 1;
            let b = &boundaries[first_idx];
            eprintln!(
                "  MISMATCH at zw_sums={:?}: full={} standalone={}",
                zw_sums, full_count, standalone_count
            );
            eprintln!(
                "    z={:0width$b} w={:0width$b}",
                b.z_bits,
                b.w_bits,
                width = 2 * k
            );
            if failed >= 10 {
                eprintln!("  (stopping after 10 failures)");
                break;
            }
        }

        if tested % 1000 == 0 {
            eprint!(
                "\r  Tested {}/{} sums ({} passed, {} failed)   ",
                tested,
                sums_groups.len(),
                passed,
                failed
            );
        }
    }

    eprintln!(
        "\nResults: {} tested, {} passed, {} failed",
        tested, passed, failed
    );
    if failed == 0 {
        eprintln!("ALL TESTS PASSED for k={}", k);
    } else {
        eprintln!("FAILURES DETECTED");
        std::process::exit(1);
    }
}

fn count_paths(nid: u32, level: usize, depth: usize, nodes: &[[u32; 4]]) -> u128 {
    if nid == DEAD {
        return 0;
    }
    if nid == LEAF {
        return 4u128.pow((depth - level) as u32);
    }
    nodes[nid as usize]
        .iter()
        .map(|&child| count_paths(child, level + 1, depth, nodes))
        .sum()
}
