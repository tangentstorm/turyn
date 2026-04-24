use std::collections::{BTreeSet, HashMap};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug)]
struct Solution {
    n: usize,
    x: Vec<i8>,
    y: Vec<i8>,
    z: Vec<i8>,
    w: Vec<i8>,
}

impl Solution {
    fn tuple_sums(&self) -> (i32, i32, i32, i32) {
        (
            self.x.iter().map(|&v| v as i32).sum(),
            self.y.iter().map(|&v| v as i32).sum(),
            self.z.iter().map(|&v| v as i32).sum(),
            self.w.iter().map(|&v| v as i32).sum(),
        )
    }

    fn verify(&self) -> Result<(), String> {
        if self.x.len() != self.n
            || self.y.len() != self.n
            || self.z.len() != self.n
            || self.w.len() + 1 != self.n
        {
            return Err("length mismatch".into());
        }
        let (sx, sy, sz, sw) = self.tuple_sums();
        if sx * sx + sy * sy + 2 * sz * sz + 2 * sw * sw != (6 * self.n as i32) - 2 {
            return Err("energy identity mismatch".into());
        }
        for lag in 1..self.n {
            let lhs = autocorr(&self.x, lag)
                + autocorr(&self.y, lag)
                + 2 * autocorr(&self.z, lag)
                + 2 * autocorr(&self.w, lag);
            if lhs != 0 {
                return Err(format!("turyn identity fails at lag {lag}: {lhs}"));
            }
        }
        Ok(())
    }

    fn canonical_rule_ok(&self) -> bool {
        let n = self.n;
        let m = self.w.len();
        if self.x[0] != 1
            || self.x[n - 1] != 1
            || self.y[0] != 1
            || self.y[n - 1] != 1
            || self.z[0] != 1
            || self.w[0] != 1
        {
            return false;
        }
        if let Some(j) = (0..n).find(|&j| self.x[j] != self.x[n - 1 - j]) {
            if self.x[j] != 1 {
                return false;
            }
        }
        if let Some(j) = (0..n).find(|&j| self.y[j] != self.y[n - 1 - j]) {
            if self.y[j] != 1 {
                return false;
            }
        }
        if let Some(j) = (0..n).find(|&j| self.z[j] == self.z[n - 1 - j]) {
            if self.z[j] != 1 {
                return false;
            }
        }
        if let Some(j) = (0..(m / 2)).find(|&j| self.w[j] * self.w[m - 1 - j] != self.w[m - 1]) {
            if self.w[j] != 1 {
                return false;
            }
        }
        if n > 2 {
            if self.x[1] != self.y[1] {
                if self.x[1] != 1 {
                    return false;
                }
            } else if self.x[n - 2] != 1 || self.y[n - 2] != -1 {
                return false;
            }
        }
        true
    }
}

fn main() -> Result<(), String> {
    let opts = parse_args()?;
    let mut rows = Vec::new();
    for n in (2..=opts.max_n).step_by(2) {
        let path = opts.data_dir.join(format!("turyn-type-{n:02}"));
        if !path.exists() {
            continue;
        }
        let coverage = load_realized_tuples(&path, n)?;
        let tuple_space = enumerate_tuple_space(n);
        let missing: Vec<_> = tuple_space
            .difference(&coverage.realized)
            .copied()
            .collect();
        let missing_with_t3: Vec<_> = tuple_space
            .difference(&coverage.realized_with_t3)
            .copied()
            .collect();
        rows.push((n, tuple_space, coverage, missing, missing_with_t3));
    }

    for (n, tuple_space, coverage, missing, missing_with_t3) in rows {
        println!("n={n}");
        println!("  tuple_space_size={}", tuple_space.len());
        println!("  realized_tuple_count={}", coverage.realized.len());
        println!("  missing_tuple_count={}", missing.len());
        println!(
            "  realized_tuples={}",
            format_tuple_list(&coverage.realized.iter().copied().collect::<Vec<_>>())
        );
        println!(
            "  realized_with_t3_count={}",
            coverage.realized_with_t3.len()
        );
        println!("  missing_with_t3_count={}", missing_with_t3.len());
        if opts.list_t3 {
            println!(
                "  realized_with_t3={}",
                format_tuple_list(
                    &coverage
                        .realized_with_t3
                        .iter()
                        .copied()
                        .collect::<Vec<_>>()
                )
            );
        }
        if opts.list_missing {
            println!("  missing_tuples={}", format_tuple_list(&missing));
            println!("  missing_with_t3={}", format_tuple_list(&missing_with_t3));
        }
        println!();
    }
    Ok(())
}

struct Options {
    data_dir: PathBuf,
    max_n: usize,
    list_missing: bool,
    list_t3: bool,
}

fn parse_args() -> Result<Options, String> {
    let mut data_dir = PathBuf::from("data");
    let mut max_n = 32usize;
    let mut list_missing = true;
    let mut list_t3 = false;
    let mut args = env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--data-dir" => {
                let value = args.next().ok_or("--data-dir needs a path")?;
                data_dir = PathBuf::from(value);
            }
            "--max-n" => {
                let value = args.next().ok_or("--max-n needs a value")?;
                max_n = value
                    .parse::<usize>()
                    .map_err(|e| format!("invalid --max-n: {e}"))?;
            }
            "--no-missing" => {
                list_missing = false;
            }
            "--list-t3" => {
                list_t3 = true;
            }
            "--help" | "-h" => {
                print_help();
                std::process::exit(0);
            }
            other => return Err(format!("unknown arg: {other}")),
        }
    }
    Ok(Options {
        data_dir,
        max_n,
        list_missing,
        list_t3,
    })
}

fn print_help() {
    println!(
        "Usage: cargo run --release --bin tuple_coverage -- [--data-dir PATH] [--max-n N] [--no-missing] [--list-t3]"
    );
    println!(
        "Compares the full signed tuple shell against tuples realized by canonical representatives."
    );
}

struct Coverage {
    realized: BTreeSet<(i32, i32, i32, i32)>,
    realized_with_t3: BTreeSet<(i32, i32, i32, i32)>,
}

fn load_realized_tuples(path: &Path, n: usize) -> Result<Coverage, String> {
    let text = fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut realized = BTreeSet::new();
    let mut realized_with_t3 = BTreeSet::new();
    for (line_no, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() {
            continue;
        }
        let sol =
            decode_line(n, line).map_err(|e| format!("{}:{}: {e}", path.display(), line_no + 1))?;
        let canonical =
            canonicalize(&sol).map_err(|e| format!("{}:{}: {e}", path.display(), line_no + 1))?;
        let tuple = canonical.tuple_sums();
        realized.insert(tuple);
        realized_with_t3.insert(tuple);
        realized_with_t3.insert(alternated_tuple_sums(&canonical));
    }
    Ok(Coverage {
        realized,
        realized_with_t3,
    })
}

fn enumerate_tuple_space(n: usize) -> BTreeSet<(i32, i32, i32, i32)> {
    let target = (6 * n as i32) - 2;
    let mut out = BTreeSet::new();
    for sx in (-(n as i32)..=(n as i32)).step_by(2) {
        for sy in (-(n as i32)..=(n as i32)).step_by(2) {
            for sz in (-(n as i32)..=(n as i32)).step_by(2) {
                let rem = target - sx * sx - sy * sy - 2 * sz * sz;
                if rem < 0 || rem % 2 != 0 {
                    continue;
                }
                let sw_sq = rem / 2;
                let sw = (sw_sq as f64).sqrt() as i32;
                if sw * sw != sw_sq || sw % 2 == 0 {
                    continue;
                }
                out.insert((sx, sy, sz, sw));
                out.insert((sx, sy, sz, -sw));
            }
        }
    }
    out
}

fn decode_line(n: usize, line: &str) -> Result<Solution, String> {
    if line.len() != n - 1 {
        return Err(format!("expected {} hex digits, got {}", n - 1, line.len()));
    }
    let mut x = Vec::with_capacity(n);
    let mut y = Vec::with_capacity(n);
    let mut z = Vec::with_capacity(n);
    let mut w = Vec::with_capacity(n - 1);
    for ch in line.bytes() {
        let nibble = match ch {
            b'0'..=b'9' => ch - b'0',
            b'a'..=b'f' => 10 + (ch - b'a'),
            b'A'..=b'F' => 10 + (ch - b'A'),
            _ => return Err(format!("invalid hex char {}", ch as char)),
        };
        x.push(if (nibble & 0b1000) == 0 { 1 } else { -1 });
        y.push(if (nibble & 0b0100) == 0 { 1 } else { -1 });
        z.push(if (nibble & 0b0010) == 0 { 1 } else { -1 });
        w.push(if (nibble & 0b0001) == 0 { 1 } else { -1 });
    }

    let mut candidate_a = Solution {
        n,
        x: x.clone(),
        y: y.clone(),
        z: z.clone(),
        w: w.clone(),
    };
    candidate_a.x.push(1);
    candidate_a.y.push(1);
    candidate_a.z.push(-1);
    if candidate_a.verify().is_ok() {
        return Ok(candidate_a);
    }

    let mut candidate_b = Solution { n, x, y, z, w };
    candidate_b.x.push(-1);
    candidate_b.y.push(-1);
    candidate_b.z.push(1);
    if candidate_b.verify().is_ok() {
        return Ok(candidate_b);
    }

    Err("could not infer final (X,Y,Z) tail bits".into())
}

fn canonicalize(sol: &Solution) -> Result<Solution, String> {
    let mut unique: HashMap<String, Solution> = HashMap::new();
    for neg_mask in 0u8..16 {
        for rev_mask in 0u8..16 {
            for alt in [false, true] {
                for swap in [false, true] {
                    let mut x = sol.x.clone();
                    let mut y = sol.y.clone();
                    let mut z = sol.z.clone();
                    let mut w = sol.w.clone();

                    if (neg_mask & 0b0001) != 0 {
                        negate_in_place(&mut x);
                    }
                    if (neg_mask & 0b0010) != 0 {
                        negate_in_place(&mut y);
                    }
                    if (neg_mask & 0b0100) != 0 {
                        negate_in_place(&mut z);
                    }
                    if (neg_mask & 0b1000) != 0 {
                        negate_in_place(&mut w);
                    }
                    if (rev_mask & 0b0001) != 0 {
                        x.reverse();
                    }
                    if (rev_mask & 0b0010) != 0 {
                        y.reverse();
                    }
                    if (rev_mask & 0b0100) != 0 {
                        z.reverse();
                    }
                    if (rev_mask & 0b1000) != 0 {
                        w.reverse();
                    }
                    if alt {
                        alternate_in_place(&mut x);
                        alternate_in_place(&mut y);
                        alternate_in_place(&mut z);
                        alternate_in_place(&mut w);
                    }
                    if swap {
                        std::mem::swap(&mut x, &mut y);
                    }

                    let cand = Solution {
                        n: sol.n,
                        x,
                        y,
                        z,
                        w,
                    };
                    if cand.canonical_rule_ok() {
                        unique.entry(signature(&cand)).or_insert(cand);
                    }
                }
            }
        }
    }
    if unique.len() == 1 {
        Ok(unique.into_values().next().unwrap())
    } else {
        Err(format!(
            "expected unique canonical representative, found {}",
            unique.len()
        ))
    }
}

fn signature(sol: &Solution) -> String {
    let mut out = String::with_capacity(sol.n * 4);
    for seq in [&sol.x, &sol.y, &sol.z, &sol.w] {
        for &v in seq {
            out.push(if v == 1 { '+' } else { '-' });
        }
        out.push('|');
    }
    out
}

fn negate_in_place(seq: &mut [i8]) {
    for v in seq {
        *v = -*v;
    }
}

fn alternate_in_place(seq: &mut [i8]) {
    for (i, v) in seq.iter_mut().enumerate() {
        if i % 2 == 1 {
            *v = -*v;
        }
    }
}

fn alternated_tuple_sums(sol: &Solution) -> (i32, i32, i32, i32) {
    (
        alternating_sum(&sol.x),
        alternating_sum(&sol.y),
        alternating_sum(&sol.z),
        alternating_sum(&sol.w),
    )
}

fn alternating_sum(seq: &[i8]) -> i32 {
    seq.iter()
        .enumerate()
        .map(|(i, &v)| if i % 2 == 0 { v as i32 } else { -(v as i32) })
        .sum()
}

fn autocorr(seq: &[i8], lag: usize) -> i32 {
    if lag >= seq.len() {
        return 0;
    }
    let mut s = 0i32;
    for i in 0..(seq.len() - lag) {
        s += (seq[i] as i32) * (seq[i + lag] as i32);
    }
    s
}

fn format_tuple_list(tuples: &[(i32, i32, i32, i32)]) -> String {
    let parts: Vec<String> = tuples
        .iter()
        .map(|&(sx, sy, sz, sw)| format!("({sx:+},{sy:+},{sz:+},{sw:+})"))
        .collect();
    format!("[{}]", parts.join(", "))
}
