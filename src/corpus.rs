//! Shared machinery for reading the published Turyn-type catalogue
//! (`data/turyn-type-NN`, mirrored from Kharaghani's list) and putting
//! quadruples into BDKR canonical form.
//!
//! Extracted from `src/bin/analyze_data.rs` so that corpus analysis and
//! the search-coverage checker (`src/bin/check_coverage.rs`) agree
//! bit-for-bit on what "the same solution" means.

use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::path::Path;

#[derive(Clone, Debug)]
pub struct Solution {
    pub n: usize,
    pub x: Vec<i8>,
    pub y: Vec<i8>,
    pub z: Vec<i8>,
    pub w: Vec<i8>,
}

impl Solution {
    pub fn tuple(&self) -> (i32, i32, i32, i32) {
        (
            self.x.iter().map(|&v| v as i32).sum(),
            self.y.iter().map(|&v| v as i32).sum(),
            self.z.iter().map(|&v| v as i32).sum(),
            self.w.iter().map(|&v| v as i32).sum(),
        )
    }

    pub fn verify(&self) -> Result<(), String> {
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

    pub fn canonical_rule_ok(&self) -> bool {
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

    /// BDKR rule (i) alone -- the `Canonical1` hypothesis of the Lean
    /// theorem `Turyn.xy_product_law` (`lean/Turyn/XY.lean`).
    pub fn rule_i_ok(&self) -> bool {
        let n = self.n;
        self.x[0] == 1
            && self.x[n - 1] == 1
            && self.y[0] == 1
            && self.y[n - 1] == 1
            && self.z[0] == 1
            && self.w[0] == 1
    }

    /// XY product law: with `U_i = x_i * y_i` (1-indexed),
    /// `U_i = -U_{n+1-i}` for every `2 <= i <= n-1`.  Proved in Lean as
    /// `Turyn.xy_product_law` under `Canonical1` for `n >= 4`.
    pub fn xy_product_law_ok(&self) -> bool {
        let n = self.n;
        (1..=n - 2).all(|j| {
            let k = n - 1 - j;
            self.x[j] * self.y[j] * self.x[k] * self.y[k] == -1
        })
    }

    /// Every image of this solution under the full BDKR symmetry group
    /// T1 (negate) x T2 (reverse) x T3 (alternate) x T4 (swap X,Y).
    pub fn orbit(&self) -> Vec<Solution> {
        let mut out = Vec::with_capacity(1024);
        for neg_mask in 0u8..16 {
            for rev_mask in 0u8..16 {
                for alt in [false, true] {
                    for swap in [false, true] {
                        let mut seqs = [
                            self.x.clone(),
                            self.y.clone(),
                            self.z.clone(),
                            self.w.clone(),
                        ];
                        for (i, seq) in seqs.iter_mut().enumerate() {
                            if rev_mask & (1 << i) != 0 {
                                *seq = reverse_seq(seq);
                            }
                            if neg_mask & (1 << i) != 0 {
                                *seq = negate_seq(seq);
                            }
                        }
                        if alt {
                            for seq in seqs.iter_mut() {
                                *seq = alternate_seq(seq);
                            }
                        }
                        if swap {
                            seqs.swap(0, 1);
                        }
                        out.push(Solution {
                            n: self.n,
                            x: seqs[0].clone(),
                            y: seqs[1].clone(),
                            z: seqs[2].clone(),
                            w: seqs[3].clone(),
                        });
                    }
                }
            }
        }
        out
    }

    pub fn rule_ii_witness(&self) -> Option<usize> {
        first_non_pal_witness(&self.x)
    }

    pub fn rule_iii_witness(&self) -> Option<usize> {
        first_non_pal_witness(&self.y)
    }

    pub fn rule_iv_witness(&self) -> Option<usize> {
        first_pal_witness(&self.z)
    }

    pub fn rule_v_witness(&self) -> Option<usize> {
        let m = self.w.len();
        let tail = self.w[m - 1];
        (0..(m / 2))
            .find(|&i| self.w[i] * self.w[m - 1 - i] != tail)
            .map(|i| i + 1)
    }
}

pub fn reverse_seq(seq: &[i8]) -> Vec<i8> {
    seq.iter().rev().copied().collect()
}

pub fn negate_seq(seq: &[i8]) -> Vec<i8> {
    seq.iter().map(|&v| -v).collect()
}

pub fn alternate_seq(seq: &[i8]) -> Vec<i8> {
    seq.iter()
        .enumerate()
        .map(|(i, &v)| if i % 2 == 0 { v } else { -v })
        .collect()
}

pub fn canonicalize(sol: &Solution) -> Result<Solution, String> {
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

pub fn signature(sol: &Solution) -> String {
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

pub fn autocorr(seq: &[i8], lag: usize) -> i32 {
    if lag >= seq.len() {
        return 0;
    }
    let mut s = 0i32;
    for i in 0..(seq.len() - lag) {
        s += (seq[i] as i32) * (seq[i + lag] as i32);
    }
    s
}

pub fn first_non_pal_witness(seq: &[i8]) -> Option<usize> {
    (1..=(seq.len() / 2))
        .find(|&i| seq[i - 1] != seq[seq.len() - i])
        .map(|i| i + 0)
}

pub fn first_pal_witness(seq: &[i8]) -> Option<usize> {
    (1..=(seq.len() / 2)).find(|&i| seq[i - 1] == seq[seq.len() - i])
}

pub fn decode_line(n: usize, line: &str) -> Result<Solution, String> {
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

pub fn load_solutions(data_dir: &Path) -> Result<BTreeMap<usize, Vec<Solution>>, String> {
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

pub fn pm(v: i8) -> char {
    if v == 1 { '+' } else { '-' }
}
