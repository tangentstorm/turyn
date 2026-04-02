/// Generate prefix/suffix lookup table for Turyn X/Y sequences.
///
/// Format v3: flat, mmap-friendly layout.
///   Header (20 bytes): magic "XYTT", version=3, n, k, dim
///   Index (dim² × 12 bytes): [offset_u64, count_u32] per sum bucket
///   Data: packed (x_bits: u32, y_bits: u32) entries, 8 bytes each
///
/// The index is a flat 2D array indexed by (x_sum_idx, y_sum_idx) where
/// sum_idx = (sum + 2k) / 2. This gives O(1) lookup with no hashing.
///
/// Two-pass generation: count entries per bucket first, then write.
/// This keeps memory usage O(buckets) not O(entries), enabling k=8+.
use std::io::{Write, Seek, SeekFrom};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(26);
    let k: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(6);
    let outfile = args.get(3).map(|s| s.as_str()).unwrap_or("xy-table.bin");

    assert!(2 * k <= n, "2*k must be <= n");
    assert!(k <= 13, "k must be <= 13 (26 boundary bits for X+Y fits in u32)");

    let dim = 2 * k + 1; // number of distinct sum values per axis
    let total_x_bits = 2 * k;
    let x_free_bits = total_x_bits - 1; // x[0]=+1 is fixed
    let y_free_bits = 2 * k;
    let total_free_bits = x_free_bits + y_free_bits;
    let total_configs = 1u64 << total_free_bits;

    eprintln!("Generating prefix/suffix table for n={}, k={}", n, k);
    eprintln!("Free bits: {} ({} for X, {} for Y), total configs: {}",
        total_free_bits, x_free_bits, y_free_bits, total_configs);
    eprintln!("Index: {}×{} = {} buckets", dim, dim, dim * dim);

    // Pass 1: count entries per (x_sum, y_sum) bucket
    let mut counts = vec![0u64; dim * dim];
    let sum_to_idx = |sum: i16| -> usize { ((sum + 2 * k as i16) / 2) as usize };
    let bucket = |xs: i16, ys: i16| -> usize { sum_to_idx(xs) * dim + sum_to_idx(ys) };

    eprintln!("Pass 1: counting...");
    for bits in 0..total_configs {
        if bits % 100_000_000 == 0 && bits > 0 {
            eprintln!("  [{:.0}%] {}/{}", 100.0 * bits as f64 / total_configs as f64, bits, total_configs);
        }
        let (_, _, xs, ys) = decode_and_sum(bits, k);
        counts[bucket(xs, ys)] += 1;
    }

    let total_entries: u64 = counts.iter().sum();
    let num_nonempty = counts.iter().filter(|&&c| c > 0).count();
    eprintln!("Total: {} entries in {} non-empty buckets", total_entries, num_nonempty);

    // Compute offsets (cumulative sum of counts)
    let mut offsets = vec![0u64; dim * dim];
    let mut cum = 0u64;
    for i in 0..dim * dim {
        offsets[i] = cum;
        cum += counts[i];
    }

    // Write file
    let header_size = 20u64;
    let index_size = (dim * dim * 12) as u64;
    let data_start = header_size + index_size;

    let mut f = std::fs::File::create(outfile).expect("Failed to create file");

    // Header
    f.write_all(b"XYTT").unwrap();
    f.write_all(&3u32.to_le_bytes()).unwrap(); // version
    f.write_all(&(n as u32).to_le_bytes()).unwrap();
    f.write_all(&(k as u32).to_le_bytes()).unwrap();
    f.write_all(&(dim as u32).to_le_bytes()).unwrap();

    // Index
    for i in 0..dim * dim {
        f.write_all(&offsets[i].to_le_bytes()).unwrap();
        f.write_all(&(counts[i] as u32).to_le_bytes()).unwrap();
    }

    // Pre-allocate data section (seek to end + write a byte)
    let data_size = total_entries * 8;
    f.seek(SeekFrom::Start(data_start + data_size - 1)).unwrap();
    f.write_all(&[0]).unwrap();

    // Pass 2: write entries directly to computed offsets
    eprintln!("Pass 2: writing entries...");
    let mut write_pos = vec![0u64; dim * dim]; // current write position per bucket
    // Buffer entries per bucket to reduce seeks
    let flush_threshold = 8192usize; // entries per bucket before flush
    let mut buffers: Vec<Vec<u8>> = (0..dim * dim).map(|_| Vec::with_capacity(flush_threshold * 8)).collect();

    for bits in 0..total_configs {
        if bits % 100_000_000 == 0 && bits > 0 {
            eprintln!("  [{:.0}%] {}/{}", 100.0 * bits as f64 / total_configs as f64, bits, total_configs);
        }
        let (xb, yb, xs, ys) = decode_and_sum(bits, k);
        let bi = bucket(xs, ys);
        let buf = &mut buffers[bi];
        buf.extend_from_slice(&xb.to_le_bytes());
        buf.extend_from_slice(&yb.to_le_bytes());

        if buf.len() >= flush_threshold * 8 {
            let byte_offset = data_start + (offsets[bi] + write_pos[bi]) * 8;
            f.seek(SeekFrom::Start(byte_offset)).unwrap();
            f.write_all(buf).unwrap();
            write_pos[bi] += (buf.len() / 8) as u64;
            buf.clear();
        }
    }
    // Flush remaining buffers
    for bi in 0..dim * dim {
        let buf = &buffers[bi];
        if !buf.is_empty() {
            let byte_offset = data_start + (offsets[bi] + write_pos[bi]) * 8;
            f.seek(SeekFrom::Start(byte_offset)).unwrap();
            f.write_all(buf).unwrap();
        }
    }

    let file_size = std::fs::metadata(outfile).map(|m| m.len()).unwrap_or(0);
    eprintln!("Wrote {} ({:.1} MB)", outfile, file_size as f64 / 1_048_576.0);

    // Print top buckets
    let mut bucket_sizes: Vec<(usize, u64)> = counts.iter().cloned().enumerate().filter(|&(_, c)| c > 0).collect();
    bucket_sizes.sort_by_key(|&(_, c)| std::cmp::Reverse(c));
    eprintln!("Top 10 buckets:");
    let idx_to_sum = |idx: usize| -> i16 { (idx as i16) * 2 - 2 * k as i16 };
    for &(bi, count) in bucket_sizes.iter().take(10) {
        let xi = bi / dim;
        let yi = bi % dim;
        eprintln!("  sum=({},{}): {} entries", idx_to_sum(xi), idx_to_sum(yi), count);
    }
}

/// Decode bit pattern and compute boundary sums.
fn decode_and_sum(bits: u64, k: usize) -> (u32, u32, i16, i16) {
    let mut x_bits = 1u32; // x[0] = +1
    let mut y_bits = 0u32;
    let mut x_sum = 1i16;
    let mut y_sum = 0i16;
    let mut bi = 0usize;

    for i in 1..k {
        let v = ((bits >> bi) & 1) as u32; bi += 1;
        x_bits |= v << i;
        x_sum += if v == 1 { 1 } else { -1 };
    }
    for i in 0..k {
        let v = ((bits >> bi) & 1) as u32; bi += 1;
        x_bits |= v << (k + i);
        x_sum += if v == 1 { 1 } else { -1 };
    }
    for i in 0..k {
        let v = ((bits >> bi) & 1) as u32; bi += 1;
        y_bits |= v << i;
        y_sum += if v == 1 { 1 } else { -1 };
    }
    for i in 0..k {
        let v = ((bits >> bi) & 1) as u32; bi += 1;
        y_bits |= v << (k + i);
        y_sum += if v == 1 { 1 } else { -1 };
    }
    (x_bits, y_bits, x_sum, y_sum)
}
