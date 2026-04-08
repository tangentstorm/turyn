/// Benchmark: extension filter hit rate and cost at k=5,7,10 bases.
fn main() {
    use turyn::mdd_zw_first;
    use turyn::mdd_reorder;
    use std::time::Instant;

    struct Entry { z_bits: u32, w_bits: u32, x_bits: u32, y_bits: u32 }

    fn extract_entries(mdd: &mdd_reorder::Mdd4, limit: usize) -> Vec<Entry> {
        let k = mdd.k;
        let half_depth = 2 * k;
        let pos_order: Vec<usize> = {
            let mut v = Vec::with_capacity(half_depth);
            for t in 0..k { v.push(t); v.push(2 * k - 1 - t); }
            v
        };
        let mut entries = Vec::new();
        walk(mdd.root, 0, half_depth, 0, 0, 0, 0, true, &pos_order, &mdd.nodes, &mut entries, limit);
        entries
    }

    fn walk(
        nid: u32, level: usize, hd: usize, z: u32, w: u32, x: u32, y: u32, in_zw: bool,
        po: &[usize], nodes: &[[u32; 4]], out: &mut Vec<Entry>, limit: usize,
    ) {
        if out.len() >= limit { return; }
        if nid == 0 { return; }
        if level == hd {
            if in_zw { walk(nid, 0, hd, z, w, 0, 0, false, po, nodes, out, limit); }
            else { out.push(Entry { z_bits: z, w_bits: w, x_bits: x, y_bits: y }); }
            return;
        }
        let branches: Vec<(u32, u32)> = if nid == u32::MAX {
            (0..4).map(|b| (u32::MAX, b)).collect()
        } else {
            (0..4u32).filter(|&b| nodes[nid as usize][b as usize] != 0)
                .map(|b| (nodes[nid as usize][b as usize], b)).collect()
        };
        let pos = po[level];
        for (child, b) in branches {
            if in_zw {
                walk(child, level+1, hd, z|((b&1)<<pos), w|(((b>>1)&1)<<pos), x, y, true, po, nodes, out, limit);
            } else {
                walk(child, level+1, hd, z, w, x|((b&1)<<pos), y|(((b>>1)&1)<<pos), false, po, nodes, out, limit);
            }
            if out.len() >= limit { return; }
        }
    }

    // Count paths in extension MDD
    fn count_paths(nid: u32, level: usize, depth: usize, nodes: &[[u32; 4]]) -> u64 {
        if nid == 0 { return 0; }
        if level == depth { return 1; }
        if nid == u32::MAX { return 4u64.pow((depth - level) as u32); }
        (0..4).map(|b| count_paths(nodes[nid as usize][b], level + 1, depth, nodes)).sum()
    }

    for base_k in [5, 7, 10] {
        let path = format!("mdd-{}.bin", base_k);
        let mdd = match mdd_reorder::Mdd4::load(&path) {
            Some(m) => m,
            None => { eprintln!("Skipping k={}: not found", base_k); continue; }
        };
        let entries = extract_entries(&mdd, 2000);
        eprintln!("\n============================================================");
        eprintln!("Base k={}, {} entries extracted", base_k, entries.len());

        for extra in 1..=4 {
            let target_k = base_k + extra;
            let ext_depth = 4 * extra; // ZW + XY
            let mut hits = 0u32;
            let mut total_paths = 0u64;
            let start = Instant::now();
            let test_n = entries.len().min(200);
            let mut timeout = false;
            for e in entries.iter().take(test_n) {
                let t0 = Instant::now();
                let (ext_nodes, ext_root) = mdd_zw_first::build_extension(
                    base_k, target_k, e.z_bits, e.w_bits, e.x_bits, e.y_bits);
                if ext_root != 0 { // not DEAD
                    hits += 1;
                    total_paths += count_paths(ext_root, 0, ext_depth, &ext_nodes);
                }
                if t0.elapsed().as_secs() > 10 { timeout = true; break; }
            }
            let avg_us = start.elapsed().as_micros() as f64 / test_n as f64;
            let pruned_pct = 100.0 * (1.0 - hits as f64 / test_n as f64);
            eprintln!("  k={}->{}:  {}/{} hits ({:.1}% pruned), avg={:.0}us/call, total_paths={}{}",
                base_k, target_k, hits, test_n, pruned_pct, avg_us, total_paths,
                if timeout { " (TIMEOUT)" } else { "" });
        }

        // Monotonicity check: +1 pruned set should equal +2 pruned set
        let test_n = entries.len().min(200);
        let dead1: Vec<bool> = entries.iter().take(test_n).map(|e| {
            let (_, r) = mdd_zw_first::build_extension(base_k, base_k+1, e.z_bits, e.w_bits, e.x_bits, e.y_bits);
            r == 0
        }).collect();
        let dead2: Vec<bool> = entries.iter().take(test_n).map(|e| {
            let (_, r) = mdd_zw_first::build_extension(base_k, base_k+2, e.z_bits, e.w_bits, e.x_bits, e.y_bits);
            r == 0
        }).collect();
        let mono_ok = dead1.iter().zip(dead2.iter()).all(|(&d1, &d2)| d1 == d2);
        eprintln!("  Monotonicity +1 vs +2: {}", if mono_ok { "OK" } else { "FAILED" });
    }
}
