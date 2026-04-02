/// Generate prefix/suffix lookup table for Turyn X/Y sequences.
///
/// Format v3: flat, mmap-friendly layout indexed by x_bits.
///   Header (20 bytes): magic "XYTT", version=3, n, k, x_dim
///   Index (x_dim × 12 bytes): [offset_u64, count_u32] per x_bits value
///   Data: packed y_bits (u32) entries, 4 bytes each, grouped by x_bits
///
/// x_dim = 2^(2k) — one slot per possible x boundary bit pattern.
/// x[0]=+1 is baked in, so half the slots are empty.
///
/// Two-pass: count per x_bits, then write. O(x_dim) memory.
use std::io::{Write, Seek, SeekFrom};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(26);
    let k: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(6);
    let outfile = args.get(3).map(|s| s.as_str()).unwrap_or("xy-table.bin");

    assert!(2 * k <= n, "2*k must be <= n");
    assert!(k <= 16, "k must be <= 16 (32 boundary bits fits in u32)");

    let x_dim = 1usize << (2 * k); // 2^(2k) possible x_bits patterns
    let y_dim = 1usize << (2 * k);
    let x_free_bits = 2 * k - 1; // x[0]=+1 fixed
    let y_free_bits = 2 * k;
    let total_free_bits = x_free_bits + y_free_bits;
    let total_configs = 1u64 << total_free_bits;

    eprintln!("Generating table for n={}, k={}", n, k);
    eprintln!("x_dim={}, y_dim={}, total configs={}", x_dim, y_dim, total_configs);

    // Pass 1: count y entries per x_bits
    eprintln!("Pass 1: counting...");
    let mut counts = vec![0u32; x_dim];
    for bits in 0..total_configs {
        if bits % 200_000_000 == 0 && bits > 0 {
            eprintln!("  [{:.0}%]", 100.0 * bits as f64 / total_configs as f64);
        }
        let (xb, _yb) = decode_bits(bits, k);
        counts[xb as usize] += 1;
    }

    let total_entries: u64 = counts.iter().map(|&c| c as u64).sum();
    let nonempty = counts.iter().filter(|&&c| c > 0).count();
    eprintln!("Total: {} entries, {} non-empty x_bits buckets out of {}", total_entries, nonempty, x_dim);

    // Compute offsets
    let mut offsets = vec![0u64; x_dim];
    let mut cum = 0u64;
    for i in 0..x_dim {
        offsets[i] = cum;
        cum += counts[i] as u64;
    }

    // Write file
    let header_size = 20u64;
    let index_size = (x_dim * 12) as u64;
    let data_start = header_size + index_size;
    let data_size = total_entries * 4; // y_bits only, 4 bytes each

    let mut f = std::fs::File::create(outfile).expect("Failed to create file");

    // Header
    f.write_all(b"XYTT").unwrap();
    f.write_all(&3u32.to_le_bytes()).unwrap();
    f.write_all(&(n as u32).to_le_bytes()).unwrap();
    f.write_all(&(k as u32).to_le_bytes()).unwrap();
    f.write_all(&(x_dim as u32).to_le_bytes()).unwrap();

    // Index
    for i in 0..x_dim {
        f.write_all(&offsets[i].to_le_bytes()).unwrap();
        f.write_all(&(counts[i] as u32).to_le_bytes()).unwrap();
    }

    // Pre-allocate data section
    if data_size > 0 {
        f.seek(SeekFrom::Start(data_start + data_size - 1)).unwrap();
        f.write_all(&[0]).unwrap();
    }

    // Pass 2: write y_bits entries grouped by x_bits
    eprintln!("Pass 2: writing...");
    let flush_threshold = 16384usize;
    let mut buffers: Vec<Vec<u8>> = (0..x_dim).map(|_| Vec::new()).collect();
    let mut write_pos = vec![0u64; x_dim];

    for bits in 0..total_configs {
        if bits % 200_000_000 == 0 && bits > 0 {
            eprintln!("  [{:.0}%]", 100.0 * bits as f64 / total_configs as f64);
        }
        let (xb, yb) = decode_bits(bits, k);
        let xi = xb as usize;
        buffers[xi].extend_from_slice(&yb.to_le_bytes());

        if buffers[xi].len() >= flush_threshold * 4 {
            let byte_off = data_start + (offsets[xi] + write_pos[xi]) * 4;
            f.seek(SeekFrom::Start(byte_off)).unwrap();
            f.write_all(&buffers[xi]).unwrap();
            write_pos[xi] += (buffers[xi].len() / 4) as u64;
            buffers[xi].clear();
        }
    }
    for xi in 0..x_dim {
        if !buffers[xi].is_empty() {
            let byte_off = data_start + (offsets[xi] + write_pos[xi]) * 4;
            f.seek(SeekFrom::Start(byte_off)).unwrap();
            f.write_all(&buffers[xi]).unwrap();
        }
    }

    let file_size = std::fs::metadata(outfile).map(|m| m.len()).unwrap_or(0);
    eprintln!("Wrote {} ({:.1} MB)", outfile, file_size as f64 / 1_048_576.0);
}

/// Decode free bits into (x_bits, y_bits).
fn decode_bits(bits: u64, k: usize) -> (u32, u32) {
    let mut xb = 1u32; // x[0]=+1
    let mut yb = 0u32;
    let mut bi = 0usize;
    for i in 1..(2*k) { let v = ((bits >> bi) & 1) as u32; bi += 1; xb |= v << i; }
    for i in 0..(2*k) { let v = ((bits >> bi) & 1) as u32; bi += 1; yb |= v << i; }
    (xb, yb)
}
