/// Generate a ZW-first MDD boundary table and save to file.
/// Usage: gen_mdd [k] [outfile] [--legacy] [--zw-only]
/// Default: k=8, outfile=mdd-{k}.bin
/// --legacy: use 16-way interleaved build + reorder (slower, more memory)
/// --zw-only: build ZW half only (no XY sub-MDDs). Much faster, smaller file.
///            Use build_xy_for_boundary() at runtime for XY.
/// Default is ZW-first direct builder (faster, 4x less node memory)

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(8);
    let zw_only = args.iter().any(|s| s == "--zw-only");
    let default_out = if zw_only { format!("mdd-{}-zw.bin", k) } else { format!("mdd-{}.bin", k) };
    let outfile = args.get(2)
        .filter(|s| !s.starts_with("--"))
        .map(|s| s.as_str())
        .unwrap_or(&default_out);
    let legacy = args.iter().any(|s| s == "--legacy");
    let sequential = args.iter().any(|s| s == "--sequential");
    let parallel_depth: usize = args.iter()
        .position(|s| s == "--depth")
        .and_then(|i| args.get(i + 1)?.parse().ok())
        .unwrap_or(0); // 0 = auto-detect from cores

    if zw_only {
        unsafe { std::env::set_var("MDD_ZW_ONLY", "1"); }
    }

    eprintln!("Building MDD for k={}{} (valid for all n >= {})",
        k, if zw_only { " [ZW-only]" } else { "" }, 2 * k);

    let start = std::time::Instant::now();

    // For k >= 11, default to sequential (parallel 4× node duplication causes OOM)
    let use_sequential = sequential || (k >= 11 && parallel_depth == 0 && !legacy);

    let reordered = if legacy {
        eprintln!("Using legacy 16-way builder + reorder...");
        let interleaved = turyn::mdd::BoundaryMdd::build(k);
        eprintln!("Reordering to ZW-first...");
        let r = turyn::mdd_reorder::reorder_zw_first(&interleaved.nodes, interleaved.root, k);
        drop(interleaved);
        r
    } else if use_sequential {
        eprintln!("Using sequential ZW-first builder{}...",
            if k >= 11 && !sequential { " (auto: k>=11 saves memory)" } else { "" });
        let zw = turyn::mdd_zw_first::ZwFirstMdd::build(k);
        turyn::mdd_reorder::Mdd4 {
            nodes: zw.nodes, root: zw.root, k: zw.k, depth: zw.total_depth,
        }
    } else {
        let zw = if parallel_depth > 0 {
            eprintln!("Using parallel ZW-first builder (depth={}, {} subtrees, {} cores)...",
                parallel_depth, 4u32.pow(parallel_depth as u32), rayon::current_num_threads());
            turyn::mdd_zw_first::ZwFirstMdd::build_parallel_depth(k, parallel_depth)
        } else {
            eprintln!("Using parallel ZW-first builder ({} cores)...", rayon::current_num_threads());
            turyn::mdd_zw_first::ZwFirstMdd::build_parallel(k)
        };
        turyn::mdd_reorder::Mdd4 {
            nodes: zw.nodes, root: zw.root, k: zw.k, depth: zw.total_depth,
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
