/// Generate a ZW-first MDD boundary table and save to file.
/// Usage: gen_mdd [k] [outfile] [--legacy]
/// Default: k=8, outfile=mdd-{k}.bin
/// --legacy: use 16-way interleaved build + reorder (slower, more memory)

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(8);
    let default_out = format!("mdd-{}.bin", k);
    let outfile = args.get(2)
        .filter(|s| !s.starts_with("--"))
        .map(|s| s.as_str())
        .unwrap_or(&default_out);
    let zw_first = args.iter().any(|s| s == "--zw-first");
    let legacy = !zw_first; // legacy is default (better memory for k>=9)

    eprintln!("Building MDD for k={} (valid for all n >= {})", k, 2 * k);

    let start = std::time::Instant::now();

    let reordered = if legacy {
        eprintln!("Using legacy 16-way builder + reorder...");
        let interleaved = turyn::mdd::BoundaryMdd::build(k);
        eprintln!("Reordering to ZW-first...");
        let r = turyn::mdd_reorder::reorder_zw_first(&interleaved.nodes, interleaved.root, k);
        drop(interleaved);
        r
    } else {
        eprintln!("Using direct ZW-first builder...");
        let zw = turyn::mdd_zw_first::ZwFirstMdd::build(k);
        // Convert to Mdd4 format for saving
        turyn::mdd_reorder::Mdd4 {
            nodes: zw.nodes,
            root: zw.root,
            k: zw.k,
            depth: zw.total_depth,
        }
    };

    let elapsed = start.elapsed().as_secs_f64();
    let node_count = reordered.nodes.len();
    let size_bytes = 16 + node_count * 16;
    eprintln!("Built in {:.1}s: {} nodes, {:.1} MB",
        elapsed, node_count, size_bytes as f64 / 1_048_576.0);

    reordered.save(outfile).expect("Failed to write MDD file");
    let file_size = std::fs::metadata(outfile).map(|m| m.len()).unwrap_or(0);
    eprintln!("Wrote {} ({:.1} MB)", outfile, file_size as f64 / 1_048_576.0);
}
