use std::collections::{BTreeMap, HashMap};
use std::path::Path;

use turyn::corpus::*;

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

/// Corpus-wide falsification test for the XY product law.
///
/// The Lean theorem `Turyn.xy_product_law` assumes only `Canonical1`
/// (BDKR rule (i)) and `n >= 4`.  So the law must hold not merely on the
/// canonical representative of each orbit, but on *every* orbit member
/// that satisfies rule (i).  This walks the full 1024-element symmetry
/// orbit of every catalogued solution and checks exactly that.
fn print_product_law_audit(all: &BTreeMap<usize, Vec<Solution>>) {
    println!("XY product-law audit (hypothesis: BDKR rule (i), n >= 4)");
    println!("  checks every rule-(i) member of each solution's full symmetry orbit");
    let mut grand_checked = 0u64;
    let mut grand_violations = 0u64;
    for (&n, solutions) in all {
        if n < 4 {
            println!("  n={n:<3} skipped (theorem requires n >= 4)");
            continue;
        }
        let mut checked = 0u64;
        let mut violations = 0u64;
        for sol in solutions {
            for img in sol.orbit() {
                if !img.rule_i_ok() {
                    continue;
                }
                checked += 1;
                if !img.xy_product_law_ok() {
                    violations += 1;
                }
            }
        }
        grand_checked += checked;
        grand_violations += violations;
        println!(
            "  n={n:<3} solutions={:<6} rule-(i) orbit members={checked:<9} violations={violations}",
            solutions.len()
        );
    }
    println!(
        "  TOTAL rule-(i) orbit members checked={grand_checked} violations={grand_violations}"
    );
    if grand_violations == 0 {
        println!("  => no counterexample in the published corpus");
    } else {
        println!("  => COUNTEREXAMPLE FOUND -- do not enable the law as a search rule");
    }
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
    print_product_law_audit(&all);
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
