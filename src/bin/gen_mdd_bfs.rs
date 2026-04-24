/// BFS MDD builder.
/// Usage: gen_mdd_bfs [k] [outfile]

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(7);
    let default_out = format!("mdd-{}.bin", k);
    let outfile = args
        .get(2)
        .filter(|s| !s.starts_with("--"))
        .map(|s| s.as_str())
        .unwrap_or(&default_out);

    eprintln!(
        "BFS building MDD for k={} (valid for all n >= {})",
        k,
        2 * k
    );
    let start = std::time::Instant::now();
    let mdd = turyn::mdd_bfs::build_bfs_mdd(k);
    let elapsed = start.elapsed();

    let node_count = mdd.nodes.len();
    let size_bytes = 16 + node_count * 16;
    eprintln!(
        "Built in {:.1?}: {} nodes, {:.1} MB",
        elapsed,
        node_count,
        size_bytes as f64 / 1_048_576.0
    );

    mdd.save(outfile).expect("Failed to write MDD file");
    let file_size = std::fs::metadata(outfile).map(|m| m.len()).unwrap_or(0);
    eprintln!(
        "Wrote {} ({:.1} MB)",
        outfile,
        file_size as f64 / 1_048_576.0
    );
}
