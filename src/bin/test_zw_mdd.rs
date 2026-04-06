/// Quick test for ZW-first MDD.
#[path = "../mdd_zw_first.rs"]
mod mdd_zw_first;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3);

    let mdd = mdd_zw_first::ZwFirstMdd::build(k);

    let mut zw_count = 0u64;
    let mut total_xy = 0u128;
    let mut xy_memo: std::collections::HashMap<u32, u128> = std::collections::HashMap::new();

    mdd.enumerate_zw(|z_bits, w_bits, xy_root| {
        zw_count += 1;
        let xy_count = if let Some(&c) = xy_memo.get(&xy_root) { c }
            else { let c = mdd.count_xy_paths(xy_root); xy_memo.insert(xy_root, c); c };
        total_xy += xy_count;

        if zw_count <= 20 {
            eprintln!("  z={:0width$b} w={:0width$b} → {} XY configs (node {})",
                z_bits, w_bits, xy_count, xy_root, width = 2 * k);
        }
    });

    eprintln!("\nTotal: {} ZW boundaries, {} XY configs total, {} unique XY roots",
        zw_count, total_xy, xy_memo.len());
}
