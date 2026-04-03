/// Generate Z/W-indexed boundary table for Turyn X/Y sequences.
///
/// The table is a pure function of k (boundary width). The exact-lag bit pairs
/// depend only on k, not on the sequence length n, so one table works for all
/// n ≥ 2k.
///
/// Deduplicated format: many Z/W configs share the same X/Y signature, so
/// we store unique (x,y) lists once and have the index point to them.
///
/// Format:
///   Header (24 bytes): magic "XYTT", version=1, k, zw_dim, num_sigs, sum_dim
///   ZW index (zw_dim × 4 bytes): sig_id (u32) per Z/W config, 0xFFFFFFFF = empty
///   Sig directory (num_sigs × 8 bytes): [offset_u32, count_u32] per signature
///   Sub-index (num_sigs × sum_dim² × 8 bytes): (offset_within_sig, count) per bucket
///   XY data: packed (x_bits: u32, y_bits: u32) pairs, 8 bytes each
use std::collections::HashMap;
use std::io::{BufWriter, Write};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(7);
    let default_outfile = format!("xy-table-k{}.bin", k);
    let outfile = args.get(2).map(|s| s.as_str()).unwrap_or(&default_outfile);

    assert!(k >= 1, "k must be >= 1");
    assert!(k <= 13, "k must be <= 13");

    let z_dim = 1usize << (2 * k);
    let w_dim = 1usize << (2 * k);
    let x_free = 2 * k - 1; // x[0]=+1
    let y_free = 2 * k - 1; // y[0]=+1
    let xy_configs = 1u64 << (x_free + y_free);
    let total_zw_index = z_dim * w_dim;

    eprintln!("Generating boundary table for k={} (valid for all n >= {})", k, 2 * k);
    eprintln!("X/Y configs: {}, Z/W index slots: {}", xy_configs, total_zw_index);

    // Build exact-lag bit pairs directly from k.
    // For lag index j (0..k), the absolute lag is s = n-k+j for any n >= 2k.
    // X/Y (length n): pairs (i, k+i+j) for i = 0..k-j-1
    // Z   (length n): same as X/Y
    // W   (length n-1): pairs (i, k+i+j+1) for i = 0..k-j-2  (only when j < k-1)
    struct ExactLag {
        xy_pairs: Vec<(u32, u32)>,
        z_pairs: Vec<(u32, u32)>,
        w_pairs: Vec<(u32, u32)>,
        has_w: bool,
    }
    let mut exact_lags: Vec<ExactLag> = Vec::new();
    for j in 0..k {
        let xy_pairs: Vec<(u32, u32)> = (0..k-j)
            .map(|i| (i as u32, (k + i + j) as u32))
            .collect();
        let z_pairs = xy_pairs.clone();
        let has_w = j < k - 1;
        let w_pairs: Vec<(u32, u32)> = if has_w {
            (0..k-j-1)
                .map(|i| (i as u32, (k + i + j + 1) as u32))
                .collect()
        } else {
            Vec::new()
        };
        exact_lags.push(ExactLag { xy_pairs, z_pairs, w_pairs, has_w });
    }
    eprintln!("{} exact lags (lag indices 0..{})", exact_lags.len(), k - 1);

    // Phase 1: Group X/Y configs by autocorrelation signature
    eprintln!("Phase 1: grouping {} X/Y configs by signature...", xy_configs);
    let compute_xy_sig = |xb: u32, yb: u32| -> Vec<i16> {
        exact_lags.iter().map(|el| {
            let mut val = 0i32;
            for &(bi, bj) in &el.xy_pairs {
                val += 1 - 2 * (((xb >> bi) ^ (xb >> bj)) & 1) as i32;
                val += 1 - 2 * (((yb >> bi) ^ (yb >> bj)) & 1) as i32;
            }
            val as i16
        }).collect()
    };

    let mut xy_groups: HashMap<Vec<i16>, Vec<(u32, u32)>> = HashMap::new();
    for bits in 0..xy_configs {
        let (xb, yb) = decode_xy(bits, k);
        let sig = compute_xy_sig(xb, yb);
        xy_groups.entry(sig).or_default().push((xb, yb));
    }

    // Assign signature IDs and build flat data, sorted by (x_sum, y_sum) within each sig.
    let num_sigs = xy_groups.len();
    let sum_dim = 2 * k + 1;
    let sub_idx_per_sig = sum_dim * sum_dim;
    eprintln!("  {} distinct signatures, {} sum sub-buckets per sig", num_sigs, sub_idx_per_sig);

    let mut sig_to_id: HashMap<Vec<i16>, u32> = HashMap::new();
    let mut sig_offsets: Vec<u32> = Vec::with_capacity(num_sigs);
    let mut sig_counts: Vec<u32> = Vec::with_capacity(num_sigs);
    let mut xy_data: Vec<(u32, u32)> = Vec::new();
    let mut sub_index: Vec<(u32, u32)> = Vec::with_capacity(num_sigs * sub_idx_per_sig);

    let sum_to_idx = |sum: i32| -> usize { ((sum + 2 * k as i32) / 2) as usize };

    let mut sorted_sigs: Vec<Vec<i16>> = xy_groups.keys().cloned().collect();
    sorted_sigs.sort();
    for sig in &sorted_sigs {
        let entries = &xy_groups[sig];
        let id = sig_to_id.len() as u32;
        sig_to_id.insert(sig.clone(), id);
        let sig_start = xy_data.len() as u32;
        sig_offsets.push(sig_start);
        sig_counts.push(entries.len() as u32);

        let mut sum_buckets: Vec<Vec<(u32, u32)>> = vec![Vec::new(); sub_idx_per_sig];
        for &(xb, yb) in entries {
            let xs = (2 * xb.count_ones() as i32) - (2 * k) as i32;
            let ys = (2 * yb.count_ones() as i32) - (2 * k) as i32;
            let bi = sum_to_idx(xs) * sum_dim + sum_to_idx(ys);
            sum_buckets[bi].push((xb, yb));
        }

        let mut within_offset = 0u32;
        for bi in 0..sub_idx_per_sig {
            let count = sum_buckets[bi].len() as u32;
            sub_index.push((within_offset, count));
            xy_data.extend_from_slice(&sum_buckets[bi]);
            within_offset += count;
        }
    }
    let total_xy = xy_data.len();
    let sub_index_size = sub_index.len() * 8;
    eprintln!("  Total unique X/Y entries: {} ({:.1} MB)", total_xy, total_xy as f64 * 8.0 / 1_048_576.0);
    eprintln!("  Sub-index: {} entries ({:.1} MB)", sub_index.len(), sub_index_size as f64 / 1_048_576.0);

    // Phase 2: Map each Z/W config to a signature ID
    eprintln!("Phase 2: mapping Z/W configs to signatures...");
    let z_free = 2 * k - 1;
    let w_free = 2 * k;
    let zw_configs = 1u64 << (z_free + w_free);

    let compute_required_xy_sig = |zb: u32, wb: u32| -> Vec<i16> {
        exact_lags.iter().map(|el| {
            let mut z_val = 0i32;
            for &(bi, bj) in &el.z_pairs {
                z_val += 1 - 2 * (((zb >> bi) ^ (zb >> bj)) & 1) as i32;
            }
            let mut w_val = 0i32;
            if el.has_w {
                for &(bi, bj) in &el.w_pairs {
                    w_val += 1 - 2 * (((wb >> bi) ^ (wb >> bj)) & 1) as i32;
                }
            }
            -(2 * z_val + 2 * w_val) as i16
        }).collect()
    };

    let empty_sig = 0xFFFFFFFFu32;
    let mut zw_index = vec![empty_sig; total_zw_index];
    let mut nonempty = 0usize;

    for zw_bits in 0..zw_configs {
        if zw_bits % 200_000_000 == 0 && zw_bits > 0 {
            eprintln!("  [{:.0}%]", 100.0 * zw_bits as f64 / zw_configs as f64);
        }
        let (zb, wb) = decode_zw(zw_bits, k);
        let zw_idx = zb as usize * w_dim + wb as usize;
        let req_sig = compute_required_xy_sig(zb, wb);
        if let Some(&id) = sig_to_id.get(&req_sig) {
            zw_index[zw_idx] = id;
            nonempty += 1;
        }
    }
    eprintln!("  Non-empty Z/W slots: {}/{}", nonempty, total_zw_index);

    // Write file
    let header_size = 24usize;
    let zw_index_size = total_zw_index * 4;
    let sig_dir_size = num_sigs * 8;
    let sub_idx_size = sub_index.len() * 8;
    let xy_data_size = total_xy * 8;
    let total_size = header_size + zw_index_size + sig_dir_size + sub_idx_size + xy_data_size;
    eprintln!("Writing: {:.1} MB total", total_size as f64 / 1_048_576.0);

    let file = std::fs::File::create(outfile).expect("Failed to create file");
    let mut f = BufWriter::with_capacity(8 * 1024 * 1024, file);

    #[cfg(target_endian = "little")]
    fn write_u32_slice(f: &mut impl Write, data: &[u32]) {
        let bytes = unsafe {
            std::slice::from_raw_parts(data.as_ptr() as *const u8, data.len() * 4)
        };
        f.write_all(bytes).unwrap();
    }
    #[cfg(target_endian = "little")]
    fn write_u32_pair_slice(f: &mut impl Write, data: &[(u32, u32)]) {
        let bytes = unsafe {
            std::slice::from_raw_parts(data.as_ptr() as *const u8, data.len() * 8)
        };
        f.write_all(bytes).unwrap();
    }

    // Header: magic, version=5, k, zw_dim, num_sigs, sum_dim
    f.write_all(b"XYTT").unwrap();
    f.write_all(&1u32.to_le_bytes()).unwrap();
    f.write_all(&(k as u32).to_le_bytes()).unwrap();
    f.write_all(&(total_zw_index as u32).to_le_bytes()).unwrap();
    f.write_all(&(num_sigs as u32).to_le_bytes()).unwrap();
    f.write_all(&(sum_dim as u32).to_le_bytes()).unwrap();

    write_u32_slice(&mut f, &zw_index);

    let mut sig_dir: Vec<u32> = Vec::with_capacity(num_sigs * 2);
    for i in 0..num_sigs {
        sig_dir.push(sig_offsets[i]);
        sig_dir.push(sig_counts[i]);
    }
    write_u32_slice(&mut f, &sig_dir);

    write_u32_pair_slice(&mut f, &sub_index);
    write_u32_pair_slice(&mut f, &xy_data);

    f.flush().unwrap();

    let file_size = std::fs::metadata(outfile).map(|m| m.len()).unwrap_or(0);
    eprintln!("Wrote {} ({:.1} MB)", outfile, file_size as f64 / 1_048_576.0);
}

fn decode_xy(bits: u64, k: usize) -> (u32, u32) {
    let mut xb = 1u32;
    let mut yb = 1u32;
    let mut bi = 0usize;
    for i in 1..(2*k) { let v = ((bits >> bi) & 1) as u32; bi += 1; xb |= v << i; }
    for i in 1..(2*k) { let v = ((bits >> bi) & 1) as u32; bi += 1; yb |= v << i; }
    (xb, yb)
}

fn decode_zw(bits: u64, k: usize) -> (u32, u32) {
    let mut zb = 1u32;
    let mut wb = 0u32;
    let mut bi = 0usize;
    for i in 1..(2*k) { let v = ((bits >> bi) & 1) as u32; bi += 1; zb |= v << i; }
    for i in 0..(2*k) { let v = ((bits >> bi) & 1) as u32; bi += 1; wb |= v << i; }
    (zb, wb)
}
