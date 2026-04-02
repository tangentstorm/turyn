/// Generate Z/W-indexed boundary table for Turyn X/Y sequences.
///
/// Deduplicated format: many Z/W configs share the same X/Y signature, so
/// we store unique (x,y) lists once and have the index point to them.
///
/// Format v4:
///   Header (24 bytes): magic "XYTT", version=4, n, k, zw_dim, num_sigs
///   ZW index (zw_dim × 4 bytes): sig_id (u32) per Z/W config, 0xFFFFFFFF = empty
///   Sig directory (num_sigs × 8 bytes): [offset_u32, count_u32] per signature
///   XY data: packed (x_bits: u32, y_bits: u32) pairs, 8 bytes each
use std::collections::HashMap;
use std::io::{BufWriter, Write};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(26);
    let k: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(7);
    let default_outfile = format!("xy-table-n{}-k{}.bin", n, k);
    let outfile = args.get(3).map(|s| s.as_str()).unwrap_or(&default_outfile);

    assert!(2 * k <= n, "2*k must be <= n");
    assert!(k <= 13, "k must be <= 13");
    let m = n - 1;

    let z_dim = 1usize << (2 * k);
    let w_dim = 1usize << (2 * k);
    let x_free = 2 * k - 1; // x[0]=+1
    let y_free = 2 * k - 1; // y[0]=+1
    let xy_configs = 1u64 << (x_free + y_free);
    let total_zw_index = z_dim * w_dim;

    eprintln!("Generating Z/W-indexed table for n={}, k={}", n, k);
    eprintln!("X/Y configs: {}, Z/W index slots: {}", xy_configs, total_zw_index);

    // Find exact lags
    let is_bnd = |pos: usize, len: usize, bk: usize| pos < bk || pos >= len - bk;
    let pos_to_bit = |pos: usize, len: usize, bk: usize| -> u32 {
        if pos < bk { pos as u32 } else { (bk + pos - (len - bk)) as u32 }
    };

    struct ExactLag {
        xy_pairs: Vec<(u32, u32)>,
        z_pairs: Vec<(u32, u32)>,
        w_pairs: Vec<(u32, u32)>,
        has_w: bool,
    }
    let mut exact_lags: Vec<ExactLag> = Vec::new();
    let mut exact_lag_indices: Vec<usize> = Vec::new();
    for s in 1..n {
        let mut xy_all = true; let mut xy_pairs = Vec::new();
        for i in 0..n-s {
            if is_bnd(i, n, k) && is_bnd(i+s, n, k) {
                xy_pairs.push((pos_to_bit(i, n, k), pos_to_bit(i+s, n, k)));
            } else { xy_all = false; }
        }
        if !xy_all || xy_pairs.is_empty() { continue; }

        let mut z_all = true; let mut z_pairs = Vec::new();
        for i in 0..n-s {
            if is_bnd(i, n, k) && is_bnd(i+s, n, k) {
                z_pairs.push((pos_to_bit(i, n, k), pos_to_bit(i+s, n, k)));
            } else { z_all = false; }
        }
        let has_w = s < m;
        let mut w_all = true; let mut w_pairs = Vec::new();
        if has_w {
            for i in 0..m-s {
                if is_bnd(i, m, k) && is_bnd(i+s, m, k) {
                    w_pairs.push((pos_to_bit(i, m, k), pos_to_bit(i+s, m, k)));
                } else { w_all = false; }
            }
        }
        if !z_all || (has_w && !w_all) { continue; }
        exact_lag_indices.push(s);
        exact_lags.push(ExactLag { xy_pairs, z_pairs, w_pairs, has_w });
    }
    eprintln!("Exact lags: {:?}", exact_lag_indices);

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
    // Also build a per-sig sub-index: for each (x_sum_idx, y_sum_idx) within the sig,
    // store the (offset_within_sig, count) so runtime can jump to matching entries.
    let num_sigs = xy_groups.len();
    let sum_dim = 2 * k + 1; // distinct sum values per axis
    let sub_idx_per_sig = sum_dim * sum_dim; // (x_sum_idx, y_sum_idx) buckets
    eprintln!("  {} distinct signatures, {} sum sub-buckets per sig", num_sigs, sub_idx_per_sig);

    let mut sig_to_id: HashMap<Vec<i16>, u32> = HashMap::new();
    let mut sig_offsets: Vec<u32> = Vec::with_capacity(num_sigs);
    let mut sig_counts: Vec<u32> = Vec::with_capacity(num_sigs);
    let mut xy_data: Vec<(u32, u32)> = Vec::new();
    // Per-sig sub-index: flattened [num_sigs * sub_idx_per_sig] of (offset_within_sig: u32, count: u16)
    // Packed as u64: offset in low 32, count in high 16, to save space.
    // Actually just use (u32, u32) for simplicity.
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

        // Group entries by (x_sum, y_sum)
        let mut sum_buckets: Vec<Vec<(u32, u32)>> = vec![Vec::new(); sub_idx_per_sig];
        for &(xb, yb) in entries {
            let xs = (2 * xb.count_ones() as i32) - (2 * k) as i32;
            let ys = (2 * yb.count_ones() as i32) - (2 * k) as i32;
            let bi = sum_to_idx(xs) * sum_dim + sum_to_idx(ys);
            sum_buckets[bi].push((xb, yb));
        }

        // Write entries sorted by sum bucket, build sub-index
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
    let header_size = 28usize; // added sum_dim field
    let zw_index_size = total_zw_index * 4;
    let sig_dir_size = num_sigs * 8;
    let sub_idx_size = sub_index.len() * 8;
    let xy_data_size = total_xy * 8;
    let total_size = header_size + zw_index_size + sig_dir_size + sub_idx_size + xy_data_size;
    eprintln!("Writing: {:.1} MB total", total_size as f64 / 1_048_576.0);

    let file = std::fs::File::create(outfile).expect("Failed to create file");
    let mut f = BufWriter::with_capacity(8 * 1024 * 1024, file);

    // Helper: write a &[u32] slice as raw little-endian bytes (no per-element loop)
    #[cfg(target_endian = "little")]
    fn write_u32_slice(f: &mut impl Write, data: &[u32]) {
        let bytes = unsafe {
            std::slice::from_raw_parts(data.as_ptr() as *const u8, data.len() * 4)
        };
        f.write_all(bytes).unwrap();
    }
    // Helper: write a &[(u32,u32)] slice as raw bytes
    #[cfg(target_endian = "little")]
    fn write_u32_pair_slice(f: &mut impl Write, data: &[(u32, u32)]) {
        let bytes = unsafe {
            std::slice::from_raw_parts(data.as_ptr() as *const u8, data.len() * 8)
        };
        f.write_all(bytes).unwrap();
    }

    // Header
    f.write_all(b"XYTT").unwrap();
    f.write_all(&4u32.to_le_bytes()).unwrap();
    f.write_all(&(n as u32).to_le_bytes()).unwrap();
    f.write_all(&(k as u32).to_le_bytes()).unwrap();
    f.write_all(&(total_zw_index as u32).to_le_bytes()).unwrap();
    f.write_all(&(num_sigs as u32).to_le_bytes()).unwrap();
    f.write_all(&(sum_dim as u32).to_le_bytes()).unwrap();

    // ZW index: sig_id per slot (bulk write)
    write_u32_slice(&mut f, &zw_index);

    // Sig directory: (offset, count) per signature
    let mut sig_dir: Vec<u32> = Vec::with_capacity(num_sigs * 2);
    for i in 0..num_sigs {
        sig_dir.push(sig_offsets[i]);
        sig_dir.push(sig_counts[i]);
    }
    write_u32_slice(&mut f, &sig_dir);

    // Sub-index: (offset_within_sig, count) per (sig, x_sum_idx, y_sum_idx)
    write_u32_pair_slice(&mut f, &sub_index);

    // XY data
    write_u32_pair_slice(&mut f, &xy_data);

    f.flush().unwrap();

    let file_size = std::fs::metadata(outfile).map(|m| m.len()).unwrap_or(0);
    eprintln!("Wrote {} ({:.1} MB)", outfile, file_size as f64 / 1_048_576.0);
}

fn decode_xy(bits: u64, k: usize) -> (u32, u32) {
    let mut xb = 1u32;
    let mut yb = 1u32; // y[0]=+1
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
