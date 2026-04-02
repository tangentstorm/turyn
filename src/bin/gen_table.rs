/// Generate Z/W-indexed boundary table for Turyn X/Y sequences.
///
/// For each possible Z/W boundary configuration, precompute which X/Y boundary
/// configurations satisfy the autocorrelation constraints at boundary-only lags.
///
/// Format: header | index (one entry per Z/W boundary config) | data ((x_bits, y_bits) pairs)
///   Header (20 bytes): magic "XYTT", version=3, n, k, zw_dim
///   Index (zw_dim × 12 bytes): [offset_u64, count_u32] per (z_bits, w_bits)
///   Data: packed (x_bits: u32, y_bits: u32) pairs, 8 bytes each
///
/// The Z/W boundary is packed into a single index: z_bits * w_dim + w_bits.
/// z_bits has 2k bits (z[0]=+1 fixed, so bit 0 is always 1).
/// w_bits has 2k bits (all free).
use std::collections::HashMap;
use std::io::{Write, Seek, SeekFrom};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(26);
    let k: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(6);
    let outfile = args.get(3).map(|s| s.as_str()).unwrap_or("xy-table.bin");

    assert!(2 * k <= n, "2*k must be <= n");
    assert!(k <= 13, "k must be <= 13");
    let m = n - 1; // W length

    let z_dim = 1usize << (2 * k); // z_bits space (z[0]=+1, so half empty)
    let w_dim = 1usize << (2 * k); // w_bits space
    let zw_dim = z_dim; // index by z_bits; w handled via required signature
    let x_dim = 1usize << (2 * k);
    let y_dim = 1usize << (2 * k);
    let x_free = 2 * k - 1; // x[0]=+1
    let y_free = 2 * k - 1; // y[0]=+1
    let xy_configs = 1u64 << (x_free + y_free);

    eprintln!("Generating Z/W-indexed table for n={}, k={}", n, k);
    eprintln!("X/Y configs: {} ({} free bits)", xy_configs, x_free + y_free);

    // Find exact lags: lags where ALL (i, i+s) pairs are in boundary for X/Y
    let is_xy_bnd = |pos: usize| pos < k || pos >= n - k;
    let is_w_bnd = |pos: usize| pos < k || pos >= m - k;
    let pos_to_bit = |pos: usize, len: usize, bk: usize| -> u32 {
        if pos < bk { pos as u32 } else { (bk + pos - (len - bk)) as u32 }
    };

    struct ExactLag {
        s: usize,
        xy_pairs: Vec<(u32, u32)>,  // (bit_i, bit_j) for X/Y positions
        z_pairs: Vec<(u32, u32)>,   // (bit_i, bit_j) for Z positions
        w_pairs: Vec<(u32, u32)>,   // (bit_i, bit_j) for W positions
        has_w: bool,
    }
    let mut exact_lags: Vec<ExactLag> = Vec::new();
    for s in 1..n {
        // Check X/Y: all pairs in boundary?
        let mut xy_all_bnd = true;
        let mut xy_pairs = Vec::new();
        for i in 0..n - s {
            if is_xy_bnd(i) && is_xy_bnd(i + s) {
                xy_pairs.push((pos_to_bit(i, n, k), pos_to_bit(i + s, n, k)));
            } else {
                xy_all_bnd = false;
            }
        }
        if !xy_all_bnd || xy_pairs.is_empty() { continue; }

        // Check Z: all pairs in boundary?
        let mut z_all_bnd = true;
        let mut z_pairs = Vec::new();
        for i in 0..n - s {
            let ib = i < k || i >= n - k;
            let jb = (i + s) < k || (i + s) >= n - k;
            if ib && jb { z_pairs.push((pos_to_bit(i, n, k), pos_to_bit(i + s, n, k))); }
            else { z_all_bnd = false; }
        }

        // Check W: all pairs in boundary? (W has length m, may not have pairs for this lag)
        let mut w_all_bnd = true;
        let mut w_pairs = Vec::new();
        let has_w = s < m;
        if has_w {
            for i in 0..m - s {
                if is_w_bnd(i) && is_w_bnd(i + s) {
                    w_pairs.push((pos_to_bit(i, m, k), pos_to_bit(i + s, m, k)));
                } else {
                    w_all_bnd = false;
                }
            }
        }

        // Only include if ALL terms are boundary-determined
        if !z_all_bnd || (has_w && !w_all_bnd) { continue; }

        exact_lags.push(ExactLag { s, xy_pairs, z_pairs, w_pairs, has_w });
    }
    eprintln!("Exact lags: {:?}", exact_lags.iter().map(|l| l.s).collect::<Vec<_>>());

    // Phase 1: Enumerate all X/Y boundary configs, compute autocorrelation signature,
    // group by signature.
    eprintln!("Phase 1: grouping {} X/Y configs by autocorrelation signature...", xy_configs);

    // Signature: for each exact lag, the combined X+Y boundary autocorrelation value
    let compute_xy_sig = |xb: u32, yb: u32| -> Vec<i16> {
        exact_lags.iter().map(|el| {
            let mut val = 0i32;
            for &(bi, bj) in &el.xy_pairs {
                // X contribution: agree if bits match
                val += 1 - 2 * (((xb >> bi) ^ (xb >> bj)) & 1) as i32;
                // Y contribution
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
    eprintln!("  {} distinct X/Y signatures", xy_groups.len());

    // Phase 2: For each Z/W config, compute required X/Y signature, count matches
    eprintln!("Phase 2: counting matches per Z/W config...");

    let z_free = 2 * k - 1;
    let w_free = 2 * k;
    let zw_configs = 1u64 << (z_free + w_free);
    eprintln!("  Z/W configs: {}", zw_configs);

    // For each exact lag: required_xy_autocorr = -(2*z_autocorr + 2*w_autocorr)
    // because N_X(s) + N_Y(s) + 2*N_Z(s) + 2*N_W(s) = 0
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

    // Two-pass: count, then write
    // Pack z_bits and w_bits into a single index: zw_idx = z_bits * w_dim + w_bits
    let total_zw_index = z_dim * w_dim;
    let mut counts = vec![0u32; total_zw_index];
    let mut total_entries = 0u64;

    for zw_bits in 0..zw_configs {
        let (zb, wb) = decode_zw(zw_bits, k);
        let zw_idx = zb as usize * w_dim + wb as usize;
        let req_sig = compute_required_xy_sig(zb, wb);
        if let Some(xy_list) = xy_groups.get(&req_sig) {
            counts[zw_idx] = xy_list.len() as u32;
            total_entries += xy_list.len() as u64;
        }
    }
    let nonempty = counts.iter().filter(|&&c| c > 0).count();
    eprintln!("  Total (z,w,x,y) matches: {}, non-empty Z/W slots: {}/{}", total_entries, nonempty, total_zw_index);

    // Compute offsets
    let mut offsets = vec![0u64; total_zw_index];
    let mut cum = 0u64;
    for i in 0..total_zw_index {
        offsets[i] = cum;
        cum += counts[i] as u64;
    }

    // Write file
    let header_size = 20u64;
    let index_size = (total_zw_index * 12) as u64;
    let data_start = header_size + index_size;
    let data_size = total_entries * 8;

    eprintln!("Writing: header={}B, index={}MB, data={}MB",
        header_size, index_size / 1_048_576, data_size / 1_048_576);

    let mut f = std::fs::File::create(outfile).expect("Failed to create file");

    // Header
    f.write_all(b"XYTT").unwrap();
    f.write_all(&3u32.to_le_bytes()).unwrap();
    f.write_all(&(n as u32).to_le_bytes()).unwrap();
    f.write_all(&(k as u32).to_le_bytes()).unwrap();
    f.write_all(&(total_zw_index as u32).to_le_bytes()).unwrap();

    // Index
    for i in 0..total_zw_index {
        f.write_all(&offsets[i].to_le_bytes()).unwrap();
        f.write_all(&(counts[i] as u32).to_le_bytes()).unwrap();
    }

    // Data: write (x_bits, y_bits) pairs grouped by Z/W config
    if data_size > 0 {
        f.seek(SeekFrom::Start(data_start + data_size - 1)).unwrap();
        f.write_all(&[0]).unwrap();
    }

    let mut write_pos = vec![0u64; total_zw_index];
    for zw_bits in 0..zw_configs {
        let (zb, wb) = decode_zw(zw_bits, k);
        let zw_idx = zb as usize * w_dim + wb as usize;
        let req_sig = compute_required_xy_sig(zb, wb);
        if let Some(xy_list) = xy_groups.get(&req_sig) {
            let byte_off = data_start + (offsets[zw_idx] + write_pos[zw_idx]) * 8;
            f.seek(SeekFrom::Start(byte_off)).unwrap();
            for &(xb, yb) in xy_list {
                f.write_all(&xb.to_le_bytes()).unwrap();
                f.write_all(&yb.to_le_bytes()).unwrap();
            }
            write_pos[zw_idx] += xy_list.len() as u64;
        }
    }

    let file_size = std::fs::metadata(outfile).map(|m| m.len()).unwrap_or(0);
    eprintln!("Wrote {} ({:.1} MB)", outfile, file_size as f64 / 1_048_576.0);
}

fn decode_xy(bits: u64, k: usize) -> (u32, u32) {
    let mut xb = 1u32; // x[0]=+1
    let mut yb = 0u32;
    let mut bi = 0usize;
    // x[1..2k]
    for i in 1..(2 * k) { let v = ((bits >> bi) & 1) as u32; bi += 1; xb |= v << i; }
    // y[0] is also fixed at +1 in the template (symmetry breaking)
    yb |= 1; // y[0]=+1
    // y[1..2k]
    for i in 1..(2 * k) { let v = ((bits >> bi) & 1) as u32; bi += 1; yb |= v << i; }
    (xb, yb)
}

fn decode_zw(bits: u64, k: usize) -> (u32, u32) {
    let mut zb = 1u32; // z[0]=+1
    let mut wb = 0u32;
    let mut bi = 0usize;
    for i in 1..(2 * k) { let v = ((bits >> bi) & 1) as u32; bi += 1; zb |= v << i; }
    for i in 0..(2 * k) { let v = ((bits >> bi) & 1) as u32; bi += 1; wb |= v << i; }
    (zb, wb)
}
