//! Stage 0 prototype for the inside-out MDD design (see
//! `docs/INSIDE-OUT-MDD.md`).
//!
//! Verifies the lag-sum decomposition `A(s) = A_bb(s) + A_mm(s) +
//! A_bm(s) + A_mb(s)` on a known TT(n) solution and reports the
//! high-lag/low-lag split for various `(n, k)`. Also demonstrates the
//! boundary-index lookup: builds a small hash from
//! 4-sequence-boundary high-lag bb-vectors → boundary tuples, and
//! confirms the known solution's boundary tuple is retrievable from
//! the right key.
//!
//! Usage:
//!   target/release/lag_sum_decomp <n> <k>
//!
//! Reads `known_solutions.txt` for the n=<n> entry. n in the file
//! has X,Y,Z of length n and W of length n-1 (Turyn type), which we
//! handle by zero-padding W where needed.

use std::collections::HashMap;
use std::fs;

fn parse_seq(s: &str) -> Vec<i32> {
    s.chars()
        .map(|c| match c {
            '+' => 1i32,
            '-' => -1i32,
            _ => panic!("bad char {} in sequence", c),
        })
        .collect()
}

fn read_known(n: usize) -> (Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>) {
    let body = fs::read_to_string("known_solutions.txt").expect("read known_solutions.txt");
    for line in body.lines() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        let mut parts = line.split_whitespace();
        let n_str = parts.next().expect("n");
        if n_str.parse::<usize>().unwrap() != n {
            continue;
        }
        let x = parse_seq(parts.next().expect("X"));
        let y = parse_seq(parts.next().expect("Y"));
        let z = parse_seq(parts.next().expect("Z"));
        let w = parse_seq(parts.next().expect("W"));
        return (x, y, z, w);
    }
    panic!("no known solution for n={}", n);
}

/// Full aperiodic autocorrelation at lag `s`.
fn autocorr_full(x: &[i32], s: usize) -> i32 {
    let n = x.len();
    if s >= n {
        return 0;
    }
    (0..n - s).map(|i| x[i] * x[i + s]).sum()
}

/// `bb` part: pairs (i, j) with j = i + s, both in boundary
/// `[0..k] ∪ [n-k..n]`.
fn autocorr_bb(x: &[i32], s: usize, k: usize) -> i32 {
    let n = x.len();
    if s >= n {
        return 0;
    }
    let in_bd = |i: usize| i < k || i >= n - k;
    (0..n - s)
        .filter(|&i| in_bd(i) && in_bd(i + s))
        .map(|i| x[i] * x[i + s])
        .sum()
}

/// `mm` part: pairs both in middle `[k..n-k]`.
fn autocorr_mm(x: &[i32], s: usize, k: usize) -> i32 {
    let n = x.len();
    if s >= n {
        return 0;
    }
    let in_mid = |i: usize| i >= k && i < n - k;
    (0..n - s)
        .filter(|&i| in_mid(i) && in_mid(i + s))
        .map(|i| x[i] * x[i + s])
        .sum()
}

/// `bm + mb` cross part: pairs straddling boundary/middle.
fn autocorr_cross(x: &[i32], s: usize, k: usize) -> i32 {
    let n = x.len();
    if s >= n {
        return 0;
    }
    let in_bd = |i: usize| i < k || i >= n - k;
    let in_mid = |i: usize| i >= k && i < n - k;
    (0..n - s)
        .filter(|&i| (in_bd(i) && in_mid(i + s)) || (in_mid(i) && in_bd(i + s)))
        .map(|i| x[i] * x[i + s])
        .sum()
}

/// High-lag bb-vector for a single boundary: (A_bb(s) for s in
/// high-lag range). `n` is the FULL sequence length (pad W as
/// needed before calling).
fn high_lag_bb_vec(x: &[i32], n: usize, k: usize) -> Vec<i32> {
    let lo = n - 2 * k + 1;
    let hi = n - 1;
    (lo..=hi).map(|s| autocorr_bb(x, s, k)).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args
        .get(1)
        .and_then(|s| s.parse().ok())
        .expect("usage: lag_sum_decomp <n> <k>");
    let k: usize = args
        .get(2)
        .and_then(|s| s.parse().ok())
        .expect("usage: lag_sum_decomp <n> <k>");
    if 2 * k >= n {
        panic!("need 2*k < n");
    }

    let (x, y, z, w) = read_known(n);
    // Turyn type: X, Y, Z have length n; W has length n-1 (m).
    // Turyn condition: N_X(s) + N_Y(s) + 2*N_Z(s) + 2*N_W(s) = 0 for s in 1..n.
    // We do NOT pad W; we just take its autocorrelation natively. W has
    // a different bb partition (length-(n-1) sequence) so its high-lag
    // range is offset relative to X,Y,Z.
    if x.len() != n || y.len() != n || z.len() != n || w.len() != n - 1 {
        panic!(
            "bad sequence lengths: X={}, Y={}, Z={}, W={} (expected n={}, n, n, n-1={})",
            x.len(), y.len(), z.len(), w.len(), n, n - 1
        );
    }
    let m = n - 1; // W's length
    eprintln!("=== TT({}) decomposition at k={} ===", n, k);
    eprintln!("X len {}, Y len {}, Z len {}, W len {}", x.len(), y.len(), z.len(), w.len());

    // Verify the four-tuple Turyn condition holds.
    let mut ok = true;
    for s in 1..n {
        let nx = autocorr_full(&x, s);
        let ny = autocorr_full(&y, s);
        let nz = autocorr_full(&z, s);
        let nw = if s < m { autocorr_full(&w, s) } else { 0 };
        let total = nx + ny + 2 * nz + 2 * nw;
        if total != 0 {
            eprintln!(
                "  lag {:2}: NX={} NY={} 2NZ={} 2NW={}  total={} (expected 0)",
                s, nx, ny, 2 * nz, 2 * nw, total
            );
            ok = false;
        }
    }
    if ok {
        eprintln!("Turyn condition holds: NX(s)+NY(s)+2*NZ(s)+2*NW(s) = 0 for all s in 1..{}", n);
    } else {
        eprintln!("ERROR: Turyn condition not zero at all lags!");
        std::process::exit(1);
    }

    // Verify the decomposition for each sequence at each lag.
    for (name, seq) in [("X", &x), ("Y", &y), ("Z", &z), ("W", &w)] {
        for s in 1..n {
            let full = autocorr_full(seq, s);
            let bb = autocorr_bb(seq, s, k);
            let mm = autocorr_mm(seq, s, k);
            let cr = autocorr_cross(seq, s, k);
            assert_eq!(
                full,
                bb + mm + cr,
                "decomposition broken for {} at s={}: full={}, bb+mm+cr={}",
                name,
                s,
                full,
                bb + mm + cr
            );
        }
    }
    eprintln!("Decomposition verified: A(s) = A_bb(s) + A_mm(s) + A_cross(s) for every (sequence, lag).");

    // Quantify the high-lag/low-lag split.
    let low_hi = n - 2 * k - 1; // last low-lag
    let mid_lag = n - 2 * k;
    let high_lo = n - 2 * k + 1; // first high-lag
    eprintln!(
        "\nLag classes: low = 1..{}  ({} lags),   mid = {} (1 lag),   high = {}..{}  ({} lags)",
        low_hi, low_hi, mid_lag, high_lo, n - 1, n - high_lo
    );

    eprintln!("\nPer-lag contributions (Turyn-weighted: X+Y+2Z+2W):");
    eprintln!("  s    bb_total  mm_total  cross_total    total  (=0?)");
    for s in 1..n {
        let bb = autocorr_bb(&x, s, k)
            + autocorr_bb(&y, s, k)
            + 2 * autocorr_bb(&z, s, k)
            + if s < m { 2 * autocorr_bb(&w, s, k) } else { 0 };
        let mm = autocorr_mm(&x, s, k)
            + autocorr_mm(&y, s, k)
            + 2 * autocorr_mm(&z, s, k)
            + if s < m { 2 * autocorr_mm(&w, s, k) } else { 0 };
        let cr = autocorr_cross(&x, s, k)
            + autocorr_cross(&y, s, k)
            + 2 * autocorr_cross(&z, s, k)
            + if s < m { 2 * autocorr_cross(&w, s, k) } else { 0 };
        let class = if s <= low_hi {
            "low"
        } else if s == mid_lag {
            "mid"
        } else {
            "high"
        };
        eprintln!(
            "  {:2} ({:>4})  {:>7}   {:>7}    {:>8}     {:>5}",
            s,
            class,
            bb,
            mm,
            cr,
            bb + mm + cr
        );
    }

    // ---- Boundary indexing demo (Stage 1, mini version) ----
    eprintln!("\n=== Boundary index demo (high-lag bb-vector key) ===");

    // High-lag bb-vector for the KNOWN solution's 4-tuple boundary.
    // Use the Turyn weighting: bb_X + bb_Y + 2*bb_Z + 2*bb_W.
    let known_key: Vec<i32> = (high_lo..=n - 1)
        .map(|s| {
            autocorr_bb(&x, s, k)
                + autocorr_bb(&y, s, k)
                + 2 * autocorr_bb(&z, s, k)
                + if s < m { 2 * autocorr_bb(&w, s, k) } else { 0 }
        })
        .collect();
    eprintln!("known boundary's high-lag bb-vector (length {}, Turyn-weighted): {:?}", known_key.len(), known_key);

    // Build a SMALL index: enumerate all 4-sequence boundary tuples
    // for the *first* (low-side) k bits only, holding the known
    // solution's right-side boundary fixed. This is a feasibility
    // demo — the full index would be 4^(2k) and require careful
    // engineering. Here we just show the indexing principle works:
    // varying the low-side X-boundary alone, see how many distinct
    // high-lag bb-vectors result.

    // Fix Y, Z, W boundaries (low + high side) to the known solution.
    // Vary only X's low-side boundary (k bits).
    let mut bucket: HashMap<Vec<i32>, Vec<u32>> = HashMap::new();
    let n_x_low = 1u32 << k;
    for x_low_bits in 0..n_x_low {
        let mut x_test = x.clone();
        for i in 0..k {
            let bit = (x_low_bits >> i) & 1;
            x_test[i] = if bit == 1 { 1 } else { -1 };
        }
        let key: Vec<i32> = (high_lo..=n - 1)
            .map(|s| {
                autocorr_bb(&x_test, s, k)
                    + autocorr_bb(&y, s, k)
                    + 2 * autocorr_bb(&z, s, k)
                    + if s < m { 2 * autocorr_bb(&w, s, k) } else { 0 }
            })
            .collect();
        bucket.entry(key).or_default().push(x_low_bits);
    }
    eprintln!(
        "Sweep of X's low-side boundary (k={} bits, {} settings) → {} distinct keys (avg {:.1} per key)",
        k,
        n_x_low,
        bucket.len(),
        n_x_low as f64 / bucket.len() as f64,
    );

    // Confirm the known solution's X-low-bits is retrievable from the
    // known_key bucket.
    let known_x_low: u32 = (0..k)
        .map(|i| if x[i] == 1 { 1u32 << i } else { 0 })
        .sum();
    eprintln!(
        "known X low-side bits = {:0width$b}",
        known_x_low,
        width = k
    );
    if let Some(matches) = bucket.get(&known_key) {
        if matches.contains(&known_x_low) {
            eprintln!(
                "PASS: known X low-side bits found in bucket for known_key (bucket size {})",
                matches.len()
            );
        } else {
            eprintln!(
                "FAIL: known X low-side bits NOT in bucket for known_key (bucket has {})",
                matches.len()
            );
        }
    } else {
        eprintln!("FAIL: known_key not present in bucket map");
    }

    // Bucket size histogram.
    let mut sizes: Vec<usize> = bucket.values().map(|v| v.len()).collect();
    sizes.sort_unstable();
    let max_sz = *sizes.last().unwrap_or(&0);
    let median = sizes.get(sizes.len() / 2).copied().unwrap_or(0);
    eprintln!(
        "Bucket sizes: min={}, median={}, max={}",
        sizes.first().copied().unwrap_or(0),
        median,
        max_sz
    );

    // ---- Stage 2: meet-in-the-middle (T_xy + T_zw) ----
    eprintln!("\n=== Meet-in-the-middle demo (T_xy × T_zw) ===");

    // Each sequence's boundary is 2k bits. Per-sequence boundary count is 2^(2k).
    let bd_count = 1u64 << (2 * k);
    eprintln!("Per-sequence boundary count = 2^{}={}", 2 * k, bd_count);

    // For each (X-bd, Y-bd) pair, compute combined high-lag bb-vector
    // (Turyn-weighted: bb_X + bb_Y).
    // For each (Z-bd, W-bd) pair, compute (2*bb_Z + 2*bb_W).
    // The 4-tuple constraint: bb_X+bb_Y+2bb_Z+2bb_W = -mm_total - cross_total
    // (which the inside-out walker would supply).

    // Build T_xy: key = bb_X+bb_Y at high lags  →  list of (X-bd-bits, Y-bd-bits)
    // Note: W has length n-1, so bd partition for W is different.
    // For this demo, restrict to lags where W's length isn't a special
    // case — i.e., the high-lag block restricted to s < m.

    // Helper: build a length-n sequence with the boundary set from
    // 2k bits (low-k bits then high-k bits) and middle = 0.
    let mut t_xy: HashMap<Vec<i32>, Vec<(u32, u32)>> = HashMap::new();
    let mut t_zw: HashMap<Vec<i32>, Vec<(u32, u32)>> = HashMap::new();

    let make_bd = |seq_len: usize, bits: u32, k: usize| -> Vec<i32> {
        let mut s = vec![0i32; seq_len];
        for i in 0..k {
            let bit = (bits >> i) & 1;
            s[i] = if bit == 1 { 1 } else { -1 };
            let bit2 = (bits >> (k + i)) & 1;
            s[seq_len - k + i] = if bit2 == 1 { 1 } else { -1 };
        }
        s
    };

    let build_xy_table = |k: usize, n: usize, high_lo: usize, m: usize| -> HashMap<Vec<i32>, Vec<(u32, u32)>> {
        let mut t = HashMap::new();
        let bd_count = 1u64 << (2 * k);
        for x_bits in 0..bd_count {
            let xb = make_bd(n, x_bits as u32, k);
            for y_bits in 0..bd_count {
                let yb = make_bd(n, y_bits as u32, k);
                let key: Vec<i32> = (high_lo..=n - 1)
                    .map(|s| {
                        let bx = autocorr_bb(&xb, s, k);
                        let by = autocorr_bb(&yb, s, k);
                        bx + by
                    })
                    .collect();
                t.entry(key).or_insert_with(Vec::new).push((x_bits as u32, y_bits as u32));
            }
            let _ = m; // unused here but documents that W is length-m sequence
        }
        t
    };

    let build_zw_table = |k: usize, n: usize, high_lo: usize, m: usize| -> HashMap<Vec<i32>, Vec<(u32, u32)>> {
        let mut t = HashMap::new();
        let bd_count_z = 1u64 << (2 * k); // Z is length n
        let bd_count_w = 1u64 << (2 * k); // W is length m=n-1; same number of bd bits
        for z_bits in 0..bd_count_z {
            let zb = make_bd(n, z_bits as u32, k);
            for w_bits in 0..bd_count_w {
                let wb = make_bd(m, w_bits as u32, k);
                let key: Vec<i32> = (high_lo..=n - 1)
                    .map(|s| {
                        let bz = 2 * autocorr_bb(&zb, s, k);
                        let bw = if s < m { 2 * autocorr_bb(&wb, s, k) } else { 0 };
                        bz + bw
                    })
                    .collect();
                t.entry(key).or_insert_with(Vec::new).push((z_bits as u32, w_bits as u32));
            }
        }
        t
    };

    if (1u64 << (4 * k)) > 16_000_000 {
        eprintln!(
            "Skipping meet-in-the-middle demo (would build {} pair entries per table; budget 1M)",
            1u64 << (4 * k)
        );
    } else {
        eprintln!("Building T_xy...");
        let t_xy_built = build_xy_table(k, n, high_lo, m);
        let t_xy_len = t_xy_built.len();
        let t_xy_total: usize = t_xy_built.values().map(|v| v.len()).sum();
        eprintln!(
            "  T_xy: {} distinct keys, {} pair entries (avg {:.1} per key)",
            t_xy_len, t_xy_total, t_xy_total as f64 / t_xy_len.max(1) as f64
        );
        t_xy = t_xy_built;
        eprintln!("Building T_zw...");
        let t_zw_built = build_zw_table(k, n, high_lo, m);
        let t_zw_len = t_zw_built.len();
        let t_zw_total: usize = t_zw_built.values().map(|v| v.len()).sum();
        eprintln!(
            "  T_zw: {} distinct keys, {} pair entries (avg {:.1} per key)",
            t_zw_len, t_zw_total, t_zw_total as f64 / t_zw_len.max(1) as f64
        );
        t_zw = t_zw_built;

        // Verify: known solution's (X-bd, Y-bd) is retrievable from
        // T_xy at the right key, and same for T_zw. The cross-table
        // sum must equal the known_key.
        let known_x_bits: u32 = (0..k)
            .map(|i| if x[i] == 1 { 1u32 << i } else { 0 })
            .sum::<u32>()
            + (0..k)
                .map(|i| if x[n - k + i] == 1 { 1u32 << (k + i) } else { 0 })
                .sum::<u32>();
        let known_y_bits: u32 = (0..k)
            .map(|i| if y[i] == 1 { 1u32 << i } else { 0 })
            .sum::<u32>()
            + (0..k)
                .map(|i| if y[n - k + i] == 1 { 1u32 << (k + i) } else { 0 })
                .sum::<u32>();
        let known_z_bits: u32 = (0..k)
            .map(|i| if z[i] == 1 { 1u32 << i } else { 0 })
            .sum::<u32>()
            + (0..k)
                .map(|i| if z[n - k + i] == 1 { 1u32 << (k + i) } else { 0 })
                .sum::<u32>();
        let known_w_bits: u32 = (0..k)
            .map(|i| if w[i] == 1 { 1u32 << i } else { 0 })
            .sum::<u32>()
            + (0..k)
                .map(|i| if w[m - k + i] == 1 { 1u32 << (k + i) } else { 0 })
                .sum::<u32>();
        eprintln!(
            "Known boundary bits: X={:0width$b}, Y={:0width$b}, Z={:0width$b}, W={:0width$b} (low|high concatenated)",
            known_x_bits, known_y_bits, known_z_bits, known_w_bits, width = 2 * k
        );

        let xy_key: Vec<i32> = (high_lo..=n - 1)
            .map(|s| autocorr_bb(&x, s, k) + autocorr_bb(&y, s, k))
            .collect();
        let zw_key: Vec<i32> = (high_lo..=n - 1)
            .map(|s| {
                2 * autocorr_bb(&z, s, k)
                    + if s < m { 2 * autocorr_bb(&w, s, k) } else { 0 }
            })
            .collect();
        eprintln!("known XY-bb-vector: {:?}", xy_key);
        eprintln!("known ZW-bb-vector: {:?}", zw_key);
        eprintln!("sum (should equal known_key)  : {:?}", xy_key.iter().zip(&zw_key).map(|(a, b)| a + b).collect::<Vec<i32>>());
        eprintln!("known_key                     : {:?}", known_key);

        match t_xy.get(&xy_key) {
            Some(matches) if matches.contains(&(known_x_bits, known_y_bits)) => {
                eprintln!("PASS: known (X,Y) bits in T_xy[xy_key] (bucket size {})", matches.len());
            }
            Some(matches) => {
                eprintln!("FAIL: known (X,Y) NOT in bucket (bucket has {})", matches.len());
            }
            None => {
                eprintln!("FAIL: xy_key not present in T_xy");
            }
        }
        match t_zw.get(&zw_key) {
            Some(matches) if matches.contains(&(known_z_bits, known_w_bits)) => {
                eprintln!("PASS: known (Z,W) bits in T_zw[zw_key] (bucket size {})", matches.len());
            }
            Some(matches) => {
                eprintln!("FAIL: known (Z,W) NOT in bucket (bucket has {})", matches.len());
            }
            None => {
                eprintln!("FAIL: zw_key not present in T_zw");
            }
        }

        // Cross-lookup: how many (B_X,B_Y) match the known_key when we
        // pair with each possible (Z,W) high-lag contribution?
        let mut cross_matches = 0usize;
        for (zw_v, zw_pairs) in &t_zw {
            let xy_target: Vec<i32> = known_key.iter().zip(zw_v).map(|(a, b)| a - b).collect();
            if let Some(xy_pairs) = t_xy.get(&xy_target) {
                cross_matches += xy_pairs.len() * zw_pairs.len();
            }
        }
        eprintln!(
            "\nCross-table lookup: {} 4-tuple boundaries match known_key out of {} total ({:.4}% pass)",
            cross_matches,
            (1u64 << (8 * k)),
            100.0 * cross_matches as f64 / (1u64 << (8 * k)) as f64
        );
    }
}
