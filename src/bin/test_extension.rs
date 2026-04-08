/// Test build_extension by verifying that extending a base_k boundary
/// to target_k produces paths consistent with a full target_k MDD.
///
/// Strategy:
/// 1. Build full MDD at target_k
/// 2. Walk it to collect all (z,w,x,y) boundary configs
/// 3. For each config, check if the base_k prefix matches a base_k boundary
/// 4. Call build_extension(base_k, target_k, ...) for a sample of base boundaries
/// 5. Walk the extension MDD to count valid extensions
/// 6. Cross-check: count how many target_k boundaries have this base prefix

use turyn::mdd_zw_first::{self, ZwFirstMdd, DEAD, LEAF};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let base_k: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3);
    let target_k: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(5);

    assert!(target_k > base_k, "target_k must be > base_k");
    eprintln!("Testing build_extension: base_k={} → target_k={}", base_k, target_k);

    // Build full MDD at base_k to get boundary configs
    eprintln!("Building base MDD (k={})...", base_k);
    let base_mdd = ZwFirstMdd::build(base_k);

    // Collect all base boundary (z,w,x,y) configs
    let mut base_configs: Vec<(u32, u32, u32, u32)> = Vec::new();
    base_mdd.enumerate_zw(|z_bits, w_bits, xy_root| {
        base_mdd.enumerate_xy(xy_root, |x_bits, y_bits| {
            base_configs.push((z_bits, w_bits, x_bits, y_bits));
        });
    });
    eprintln!("  {} base configs at k={}", base_configs.len(), base_k);

    // Build full MDD at target_k
    eprintln!("Building target MDD (k={})...", target_k);
    let target_mdd = ZwFirstMdd::build(target_k);

    // Collect all target boundary (z,w,x,y) configs
    let mut target_configs: Vec<(u32, u32, u32, u32)> = Vec::new();
    target_mdd.enumerate_zw(|z_bits, w_bits, xy_root| {
        target_mdd.enumerate_xy(xy_root, |x_bits, y_bits| {
            target_configs.push((z_bits, w_bits, x_bits, y_bits));
        });
    });
    eprintln!("  {} target configs at k={}", target_configs.len(), target_k);

    // For a sample of base configs, test build_extension
    let sample_size = base_configs.len().min(100);
    let mut tested = 0;
    let mut passed = 0;
    let mut failed = 0;

    for (i, &(z, w, x, y)) in base_configs.iter().enumerate() {
        if i >= sample_size { break; }
        tested += 1;

        // Count target configs that match the base boundary.
        // Old prefix positions 0..base_k-1 stay the same in both layouts.
        // Old short: base 0..base_k-1 → target 0..base_k-1 (same).
        // Old long: base base_k..2*base_k-1 → target target_k+extra..2*target_k-1.
        // (Old long covers actual positions n-base_k..n-1, which in target encoding
        //  start at target_k+extra.)
        let extra = target_k - base_k;
        let expected_count = target_configs.iter().filter(|&&(tz, tw, tx, ty)| {
            // Check prefix: positions 0..base_k-1
            for p in 0..base_k {
                if ((tz >> p) & 1) != ((z >> p) & 1) { return false; }
                if ((tw >> p) & 1) != ((w >> p) & 1) { return false; }
                if ((tx >> p) & 1) != ((x >> p) & 1) { return false; }
                if ((ty >> p) & 1) != ((y >> p) & 1) { return false; }
            }
            // Check suffix: base pos base_k+m → target pos target_k+extra+m
            for m in 0..base_k {
                let base_pos = base_k + m;
                let target_pos = target_k + extra + m;
                if ((tz >> target_pos) & 1) != ((z >> base_pos) & 1) { return false; }
                if ((tw >> target_pos) & 1) != ((w >> base_pos) & 1) { return false; }
                if ((tx >> target_pos) & 1) != ((x >> base_pos) & 1) { return false; }
                if ((ty >> target_pos) & 1) != ((y >> base_pos) & 1) { return false; }
            }
            true
        }).count();

        // Build extension MDD
        let (ext_nodes, ext_root) = mdd_zw_first::build_extension(base_k, target_k, z, w, x, y);

        // Count paths in extension MDD
        // Extension MDD has 4*extra total levels (2*extra ZW + 2*extra XY)
        let ext_count = count_paths(ext_root, 0, 4 * (target_k - base_k), &ext_nodes);

        if ext_count as usize == expected_count {
            passed += 1;
        } else {
            failed += 1;
            eprintln!("  MISMATCH config #{}: z={:0w$b} w={:0w$b} x={:0w$b} y={:0w$b}",
                i, z, w, x, y, w = 2 * base_k);
            eprintln!("    extension says {} paths, brute force says {}",
                ext_count, expected_count);
            if failed >= 10 {
                eprintln!("  (stopping after 10 failures)");
                break;
            }
        }

        if tested % 10 == 0 {
            eprint!("\r  Tested {}/{} ({} passed, {} failed)   ", tested, sample_size, passed, failed);
        }
    }

    eprintln!("\nResults: {} tested, {} passed, {} failed", tested, passed, failed);
    if failed == 0 {
        eprintln!("ALL TESTS PASSED for base_k={} → target_k={}", base_k, target_k);
    } else {
        eprintln!("FAILURES DETECTED");
        std::process::exit(1);
    }
}

fn count_paths(nid: u32, level: usize, depth: usize, nodes: &[[u32; 4]]) -> u128 {
    if nid == DEAD { return 0; }
    if nid == LEAF {
        return 4u128.pow((depth - level) as u32);
    }
    nodes[nid as usize].iter()
        .map(|&child| count_paths(child, level + 1, depth, nodes))
        .sum()
}
