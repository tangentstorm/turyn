/// BFS MDD builder test.
/// Usage: gen_mdd_bfs [k]

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(7);

    eprintln!("BFS building ZW MDD for k={}", k);
    let start = std::time::Instant::now();
    let mdd = turyn::mdd_bfs::BfsMdd::build_zw_bfs(k);
    eprintln!("Done in {:.1?}", start.elapsed());
}
