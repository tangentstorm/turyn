/// Generate prefix/suffix lookup table for Turyn X/Y sequences.
///
/// For a given n and boundary length k, enumerate all valid
/// (x_prefix, x_suffix, y_prefix, y_suffix) configurations.
/// The table groups entries by (x_boundary_sum, y_boundary_sum) for fast lookup.
///
/// Output: binary file with header + grouped entries.
/// Each entry is just 8 bytes: (x_boundary_bits: u32, y_boundary_bits: u32).
/// The sum group structure enables O(1) lookup by required boundary sum.
use std::collections::HashMap;
use std::io::Write;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(26);
    let k: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(6);
    let outfile = args.get(3).map(|s| s.as_str()).unwrap_or("xy_table.bin");

    assert!(2 * k <= n, "2*k must be <= n");
    assert!(k <= 13, "k must be <= 13 (26 boundary bits for X+Y fits in u32)");

    eprintln!("Generating prefix/suffix table for n={}, k={}", n, k);

    let total_x_bits = 2 * k;
    let total_y_bits = 2 * k;
    // x[0] is always +1, so we have (total_x_bits - 1) free bits for X
    let x_free_bits = total_x_bits - 1;
    let y_free_bits = total_y_bits;
    let total_free_bits = x_free_bits + y_free_bits;
    let total_configs = 1u64 << total_free_bits;

    eprintln!("Free bits: {} ({} for X, {} for Y), total configs: {}",
        total_free_bits, x_free_bits, y_free_bits, total_configs);

    // Group entries by (x_bnd_sum, y_bnd_sum)
    let mut groups: HashMap<(i16, i16), Vec<(u32, u32)>> = HashMap::new();
    let mut tested = 0u64;

    for bits in 0..total_configs {
        tested += 1;
        if tested % 50_000_000 == 0 {
            eprintln!("[{:.0}%] tested={}", 100.0 * tested as f64 / total_configs as f64, tested);
        }

        let (x_boundary_bits, y_boundary_bits, x_sum, y_sum) = decode_and_sum(bits, n, k);

        groups.entry((x_sum, y_sum))
            .or_default()
            .push((x_boundary_bits, y_boundary_bits));
    }

    let total_entries: usize = groups.values().map(|v| v.len()).sum();
    eprintln!("Generated {} entries in {} groups", total_entries, groups.len());

    // Print group size distribution
    let mut group_sizes: Vec<(&(i16, i16), usize)> = groups.iter().map(|(k, v)| (k, v.len())).collect();
    group_sizes.sort_by_key(|&(_, s)| std::cmp::Reverse(s));
    eprintln!("Top 10 groups by size:");
    for &(key, size) in group_sizes.iter().take(10) {
        eprintln!("  sum=({},{}): {} entries", key.0, key.1, size);
    }

    // Write binary file
    write_table(outfile, n, k, &groups).expect("Failed to write table");

    let file_size = std::fs::metadata(outfile).map(|m| m.len()).unwrap_or(0);
    eprintln!("Wrote {} ({:.1} MB)", outfile, file_size as f64 / 1_048_576.0);
}

/// Decode bit pattern and compute boundary sums.
/// Returns (x_boundary_bits, y_boundary_bits, x_sum, y_sum)
fn decode_and_sum(bits: u64, n: usize, k: usize) -> (u32, u32, i16, i16) {
    let mut x_bits = 0u32;
    let mut y_bits = 0u32;
    let mut x_sum = 0i16;
    let mut y_sum = 0i16;

    // x[0] = +1 always (bit 0 of x_bits is 1)
    x_bits |= 1;
    x_sum += 1;

    let mut bit_idx = 0usize;

    // x_prefix[1..k]
    for i in 1..k {
        let val = ((bits >> bit_idx) & 1) as u32;
        bit_idx += 1;
        x_bits |= val << i;
        x_sum += if val == 1 { 1 } else { -1 };
    }
    // x_suffix[0..k] → positions n-k..n, stored as bits k..2k in x_bits
    for i in 0..k {
        let val = ((bits >> bit_idx) & 1) as u32;
        bit_idx += 1;
        x_bits |= val << (k + i);
        x_sum += if val == 1 { 1 } else { -1 };
    }
    // y_prefix[0..k]
    for i in 0..k {
        let val = ((bits >> bit_idx) & 1) as u32;
        bit_idx += 1;
        y_bits |= val << i;
        y_sum += if val == 1 { 1 } else { -1 };
    }
    // y_suffix[0..k]
    for i in 0..k {
        let val = ((bits >> bit_idx) & 1) as u32;
        bit_idx += 1;
        y_bits |= val << (k + i);
        y_sum += if val == 1 { 1 } else { -1 };
    }

    (x_bits, y_bits, x_sum, y_sum)
}

fn write_table(path: &str, n: usize, k: usize, groups: &HashMap<(i16, i16), Vec<(u32, u32)>>) -> std::io::Result<()> {
    let mut f = std::fs::File::create(path)?;

    // Header
    f.write_all(b"XYTT")?; // magic
    f.write_all(&2u32.to_le_bytes())?; // version
    f.write_all(&(n as u32).to_le_bytes())?;
    f.write_all(&(k as u32).to_le_bytes())?;
    f.write_all(&(groups.len() as u32).to_le_bytes())?;

    // Sort groups by key for deterministic output
    let mut sorted_keys: Vec<(i16, i16)> = groups.keys().cloned().collect();
    sorted_keys.sort();

    // Group directory: (x_sum: i16, y_sum: i16, offset: u64, count: u32)
    let mut offset: u64 = 0;
    for key in &sorted_keys {
        let entries = &groups[key];
        f.write_all(&key.0.to_le_bytes())?;
        f.write_all(&key.1.to_le_bytes())?;
        f.write_all(&offset.to_le_bytes())?;
        f.write_all(&(entries.len() as u32).to_le_bytes())?;
        offset += entries.len() as u64;
    }

    // Entry data: pairs of (x_bits: u32, y_bits: u32)
    for key in &sorted_keys {
        let entries = &groups[key];
        for &(xb, yb) in entries {
            f.write_all(&xb.to_le_bytes())?;
            f.write_all(&yb.to_le_bytes())?;
        }
    }

    Ok(())
}
