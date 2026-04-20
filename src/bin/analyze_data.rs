use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::path::Path;

#[derive(Clone, Debug)]
struct Solution {
    n: usize,
    x: Vec<i8>,
    y: Vec<i8>,
    z: Vec<i8>,
    w: Vec<i8>,
}

impl Solution {
    fn tuple(&self) -> (i32, i32, i32, i32) {
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
        for seq in [&self.x, &self.y, &self.z, &self.w] {
            if seq.iter().any(|&v| v != 1 && v != -1) {
                return Err("non +/- entry".into());
            }
        }
        if self.x[0] != 1 || self.y[0] != 1 || self.z[0] != 1 || self.w[0] != 1 {
            return Err("leading sign normalization mismatch".into());
        }
        let (sx, sy, sz, sw) = self.tuple();
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

    fn rule_ii_witness(&self) -> Option<usize> {
        first_non_pal_witness(&self.x)
    }

    fn rule_iii_witness(&self) -> Option<usize> {
        first_non_pal_witness(&self.y)
    }

    fn rule_iv_witness(&self) -> Option<usize> {
        first_pal_witness(&self.z)
    }

    fn rule_v_witness(&self) -> Option<usize> {
        let m = self.w.len();
        let tail = self.w[m - 1];
        (0..(m / 2))
            .find(|&i| self.w[i] * self.w[m - 1 - i] != tail)
            .map(|i| i + 1)
    }
}

fn reverse_seq(seq: &[i8]) -> Vec<i8> {
    seq.iter().rev().copied().collect()
}

fn negate_seq(seq: &[i8]) -> Vec<i8> {
    seq.iter().map(|&v| -v).collect()
}

fn alternate_seq(seq: &[i8]) -> Vec<i8> {
    seq.iter()
        .enumerate()
        .map(|(i, &v)| if i % 2 == 0 { v } else { -v })
        .collect()
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
                        x = negate_seq(&x);
                    }
                    if (neg_mask & 0b0010) != 0 {
                        y = negate_seq(&y);
                    }
                    if (neg_mask & 0b0100) != 0 {
                        z = negate_seq(&z);
                    }
                    if (neg_mask & 0b1000) != 0 {
                        w = negate_seq(&w);
                    }

                    if (rev_mask & 0b0001) != 0 {
                        x = reverse_seq(&x);
                    }
                    if (rev_mask & 0b0010) != 0 {
                        y = reverse_seq(&y);
                    }
                    if (rev_mask & 0b0100) != 0 {
                        z = reverse_seq(&z);
                    }
                    if (rev_mask & 0b1000) != 0 {
                        w = reverse_seq(&w);
                    }

                    if alt {
                        x = alternate_seq(&x);
                        y = alternate_seq(&y);
                        z = alternate_seq(&z);
                        w = alternate_seq(&w);
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
    for &v in &sol.x {
        out.push(pm(v));
    }
    out.push('|');
    for &v in &sol.y {
        out.push(pm(v));
    }
    out.push('|');
    for &v in &sol.z {
        out.push(pm(v));
    }
    out.push('|');
    for &v in &sol.w {
        out.push(pm(v));
    }
    out
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

fn first_non_pal_witness(seq: &[i8]) -> Option<usize> {
    (1..=(seq.len() / 2))
        .find(|&i| seq[i - 1] != seq[seq.len() - i])
        .map(|i| i + 0)
}

fn first_pal_witness(seq: &[i8]) -> Option<usize> {
    (1..=(seq.len() / 2)).find(|&i| seq[i - 1] == seq[seq.len() - i])
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

fn load_solutions(data_dir: &Path) -> Result<BTreeMap<usize, Vec<Solution>>, String> {
    let mut out = BTreeMap::new();
    for n in (2..=32).step_by(2) {
        let path = data_dir.join(format!("turyn-type-{n:02}"));
        if !path.exists() {
            continue;
        }
        let text = fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let mut sols = Vec::new();
        for (line_no, raw) in text.lines().enumerate() {
            let line = raw.trim();
            if line.is_empty() {
                continue;
            }
            let sol = decode_line(n, line)
                .map_err(|e| format!("{}:{}: {e}", path.display(), line_no + 1))?;
            sol.verify()
                .map_err(|e| format!("{}:{}: {e}", path.display(), line_no + 1))?;
            let canonical = canonicalize(&sol)
                .map_err(|e| format!("{}:{}: {e}", path.display(), line_no + 1))?;
            sols.push(canonical);
        }
        out.insert(n, sols);
    }
    Ok(out)
}

fn boundary_signature(sol: &Solution, k: usize) -> String {
    let mut s = String::new();
    for i in 0..k.min(sol.n) {
        s.push(pm(sol.x[i]));
        s.push(pm(sol.y[i]));
        s.push(pm(sol.z[i]));
        if i < sol.w.len() {
            s.push(pm(sol.w[i]));
        }
    }
    s.push('|');
    for offs in (0..k.min(sol.n)).rev() {
        let i = sol.n - 1 - offs;
        s.push(pm(sol.x[i]));
        s.push(pm(sol.y[i]));
        s.push(pm(sol.z[i]));
    }
    s.push('|');
    for offs in (0..k.min(sol.w.len())).rev() {
        let i = sol.w.len() - 1 - offs;
        s.push(pm(sol.w[i]));
    }
    s
}

fn pm(v: i8) -> char {
    if v == 1 { '+' } else { '-' }
}

fn entropy(p_plus: f64) -> f64 {
    if p_plus <= 0.0 || p_plus >= 1.0 {
        0.0
    } else {
        let p_minus = 1.0 - p_plus;
        -p_plus * p_plus.log2() - p_minus * p_minus.log2()
    }
}

fn print_tuple_concentration(solutions: &[Solution]) {
    let mut counts: HashMap<(i32, i32, i32, i32), usize> = HashMap::new();
    let mut nonneg_x = 0usize;
    let mut nonneg_y = 0usize;
    let mut nonneg_z = 0usize;
    let mut positive_w = 0usize;
    let mut abs_x = 0i64;
    let mut abs_y = 0i64;
    let mut abs_z = 0i64;
    let mut abs_w = 0i64;
    for sol in solutions {
        let t @ (x, y, z, w) = sol.tuple();
        *counts.entry(t).or_default() += 1;
        if x >= 0 {
            nonneg_x += 1;
        }
        if y >= 0 {
            nonneg_y += 1;
        }
        if z >= 0 {
            nonneg_z += 1;
        }
        if w > 0 {
            positive_w += 1;
        }
        abs_x += (x as i64).abs();
        abs_y += (y as i64).abs();
        abs_z += (z as i64).abs();
        abs_w += (w as i64).abs();
    }
    let mut freq: Vec<_> = counts.into_iter().collect();
    freq.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    let total = solutions.len() as f64;
    println!("  tuple_count={} top_tuples:", freq.len());
    for ((x, y, z, w), c) in freq.into_iter().take(5) {
        println!(
            "    ({x:+},{y:+},{z:+},{w:+}) -> {c} ({:.1}%)",
            100.0 * (c as f64) / total
        );
    }
    println!(
        "  tuple_bias: P(x>=0)={:.1}% P(y>=0)={:.1}% P(z>=0)={:.1}% P(w>0)={:.1}% avg|σ|=({:.2},{:.2},{:.2},{:.2})",
        100.0 * nonneg_x as f64 / total,
        100.0 * nonneg_y as f64 / total,
        100.0 * nonneg_z as f64 / total,
        100.0 * positive_w as f64 / total,
        abs_x as f64 / total,
        abs_y as f64 / total,
        abs_z as f64 / total,
        abs_w as f64 / total,
    );
}

fn print_witness_stats(name: &str, values: impl Iterator<Item = Option<usize>>) {
    let mut hist: BTreeMap<usize, usize> = BTreeMap::new();
    let mut total = 0usize;
    let mut early = 0usize;
    for v in values {
        total += 1;
        if let Some(idx) = v {
            *hist.entry(idx).or_default() += 1;
            if idx <= 4 {
                early += 1;
            }
        }
    }
    let mut top: Vec<_> = hist.into_iter().collect();
    top.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    let top_desc = top
        .into_iter()
        .take(4)
        .map(|(idx, c)| format!("{idx}:{c}"))
        .collect::<Vec<_>>()
        .join(", ");
    println!(
        "  {name}: early<=4 {:.1}% top_witnesses [{}]",
        100.0 * (early as f64) / (total as f64),
        top_desc
    );
}

fn print_position_bias(
    solutions: &[Solution],
    seq_name: &str,
    getter: impl Fn(&Solution) -> &[i8],
) {
    let n = solutions[0].n;
    let mut stats = Vec::new();
    for i in 0..getter(&solutions[0]).len() {
        let plus = solutions.iter().filter(|sol| getter(sol)[i] == 1).count();
        let p_plus = plus as f64 / solutions.len() as f64;
        stats.push((i + 1, p_plus, entropy(p_plus)));
    }
    let mut strongest = stats.clone();
    strongest.sort_by(|a, b| a.2.partial_cmp(&b.2).unwrap());
    let preview = strongest
        .into_iter()
        .take(6)
        .map(|(idx, p, h)| format!("{idx}:{:.0}%+/{h:.2}b", 100.0 * p))
        .collect::<Vec<_>>()
        .join(", ");
    println!("  {seq_name} strongest_bias [{preview}]");

    if n >= 18 {
        let mut mids = Vec::new();
        for (idx, p, h) in stats {
            if idx > 4 && idx + 4 <= n {
                mids.push((idx, p, h));
            }
        }
        mids.sort_by(|a, b| a.2.partial_cmp(&b.2).unwrap());
        let preview = mids
            .into_iter()
            .take(4)
            .map(|(idx, p, h)| format!("{idx}:{:.0}%+/{h:.2}b", 100.0 * p))
            .collect::<Vec<_>>()
            .join(", ");
        println!("    middle_bias [{preview}]");
    }
}

fn print_boundary_reuse(solutions: &[Solution], ks: &[usize]) {
    for &k in ks {
        if k >= solutions[0].n {
            continue;
        }
        let mut map: HashMap<String, usize> = HashMap::new();
        for sol in solutions {
            *map.entry(boundary_signature(sol, k)).or_default() += 1;
        }
        let buckets = map.len();
        let max_bucket = map.values().copied().max().unwrap_or(0);
        println!(
            "  boundary k={k}: unique={} ({:.1}% of sols) max_bucket={} avg_bucket={:.2}",
            buckets,
            100.0 * (buckets as f64) / (solutions.len() as f64),
            max_bucket,
            (solutions.len() as f64) / (buckets as f64)
        );
    }
}

fn print_same_pos_correlations(solutions: &[Solution]) {
    let overlap = solutions[0].w.len();
    let mut xy_same = 0usize;
    let mut zw_same = 0usize;
    let mut xz_same = 0usize;
    let denom = solutions.len() * overlap;
    for sol in solutions {
        for i in 0..overlap {
            if sol.x[i] == sol.y[i] {
                xy_same += 1;
            }
            if sol.z[i] == sol.w[i] {
                zw_same += 1;
            }
            if sol.x[i] == sol.z[i] {
                xz_same += 1;
            }
        }
    }
    println!(
        "  same-position equalities: P(X=Y)={:.1}% P(Z=W)={:.1}% P(X=Z)={:.1}%",
        100.0 * xy_same as f64 / denom as f64,
        100.0 * zw_same as f64 / denom as f64,
        100.0 * xz_same as f64 / denom as f64
    );
}

fn print_global_summary(all: &BTreeMap<usize, Vec<Solution>>) {
    let total: usize = all.values().map(Vec::len).sum();
    println!("loaded {} solutions across {} n-values", total, all.len());

    let mut rule_ii = Vec::new();
    let mut rule_iii = Vec::new();
    let mut rule_iv = Vec::new();
    let mut rule_v = Vec::new();
    for sols in all.values() {
        for sol in sols {
            rule_ii.push(sol.rule_ii_witness());
            rule_iii.push(sol.rule_iii_witness());
            rule_iv.push(sol.rule_iv_witness());
            rule_v.push(sol.rule_v_witness());
        }
    }
    println!("global canonical-witness distributions:");
    print_witness_stats("rule ii (X)", rule_ii.into_iter());
    print_witness_stats("rule iii (Y)", rule_iii.into_iter());
    print_witness_stats("rule iv (Z)", rule_iv.into_iter());
    print_witness_stats("rule v (W)", rule_v.into_iter());
}

fn main() {
    let data_dir = Path::new("data");
    let all = match load_solutions(data_dir) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    };

    print_global_summary(&all);
    println!();

    for (n, solutions) in &all {
        println!("n={n} count={}", solutions.len());
        print_tuple_concentration(solutions);
        print_witness_stats("rule ii (X)", solutions.iter().map(|s| s.rule_ii_witness()));
        print_witness_stats(
            "rule iii (Y)",
            solutions.iter().map(|s| s.rule_iii_witness()),
        );
        print_witness_stats("rule iv (Z)", solutions.iter().map(|s| s.rule_iv_witness()));
        print_witness_stats("rule v (W)", solutions.iter().map(|s| s.rule_v_witness()));
        print_same_pos_correlations(solutions);
        print_position_bias(solutions, "X", |s| &s.x);
        print_position_bias(solutions, "Y", |s| &s.y);
        print_position_bias(solutions, "Z", |s| &s.z);
        print_position_bias(solutions, "W", |s| &s.w);
        print_boundary_reuse(solutions, &[3, 4, 5, 6, 7]);
        println!();
    }
}
