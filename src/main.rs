use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap};
use std::env;
use std::fmt;
use std::sync::Arc;
use std::time::Instant;

#[derive(Clone, Copy, Debug)]
struct Problem {
    n: usize,
}

impl Problem {
    fn new(n: usize) -> Self {
        assert!(n >= 2, "n must be at least 2");
        Self { n }
    }

    fn m(self) -> usize {
        self.n - 1
    }

    fn target_energy(self) -> i32 {
        (6 * self.n as i32) - 2
    }

    fn spectral_bound(self) -> f64 {
        self.target_energy() as f64 / 2.0
    }

    fn valid_w_values(self) -> Vec<i32> {
        let max_abs = (((self.target_energy() as f64) / 2.0).sqrt().floor() as i32).max(1);
        (-max_abs..=max_abs).filter(|v| v.abs() % 2 == 1).collect()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct PackedSeq {
    len: usize,
    bits: Vec<u64>,
}

impl PackedSeq {
    fn new(len: usize) -> Self {
        let words = len.div_ceil(64);
        Self {
            len,
            bits: vec![0; words],
        }
    }

    fn from_values(values: &[i8]) -> Self {
        let mut seq = Self::new(values.len());
        for (i, &v) in values.iter().enumerate() {
            seq.set(i, v);
        }
        seq
    }

    fn len(&self) -> usize {
        self.len
    }

    fn get(&self, idx: usize) -> i8 {
        let word = self.bits[idx / 64];
        let bit = (word >> (idx % 64)) & 1;
        if bit == 1 { 1 } else { -1 }
    }

    fn set(&mut self, idx: usize, value: i8) {
        debug_assert!(value == 1 || value == -1);
        let mask = 1u64 << (idx % 64);
        let word = &mut self.bits[idx / 64];
        if value == 1 {
            *word |= mask;
        } else {
            *word &= !mask;
        }
    }

    fn sum(&self) -> i32 {
        (0..self.len).map(|i| self.get(i) as i32).sum()
    }

    #[allow(dead_code)]
    fn reverse(&self) -> Self {
        let mut out = Self::new(self.len);
        for i in 0..self.len {
            out.set(i, self.get(self.len - 1 - i));
        }
        out
    }

    #[allow(dead_code)]
    fn negate(&self) -> Self {
        let mut out = Self::new(self.len);
        for i in 0..self.len {
            out.set(i, -self.get(i));
        }
        out
    }

    #[allow(dead_code)]
    fn alternate(&self) -> Self {
        let mut out = Self::new(self.len);
        for i in 0..self.len {
            let mut v = self.get(i);
            if i % 2 == 1 {
                v = -v;
            }
            out.set(i, v);
        }
        out
    }

    fn autocorrelation(&self, shift: usize) -> i32 {
        debug_assert!(shift < self.len);
        let mut acc = 0;
        for i in 0..(self.len - shift) {
            acc += (self.get(i) as i32) * (self.get(i + shift) as i32);
        }
        acc
    }

    #[allow(dead_code)]
    fn boundary_signature(&self, k: usize) -> Vec<i8> {
        let k = k.min(self.len);
        let mut sig = Vec::with_capacity(k * 2);
        for i in 0..k {
            sig.push(self.get(i));
        }
        for i in (self.len - k)..self.len {
            sig.push(self.get(i));
        }
        sig
    }

    fn as_string(&self) -> String {
        (0..self.len)
            .map(|i| if self.get(i) == 1 { '+' } else { '-' })
            .collect()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
struct SumTuple {
    x: i32,
    y: i32,
    z: i32,
    w: i32,
}

impl SumTuple {
    fn norm_key(&self) -> (i32, i32, i32, i32) {
        let mut xx = self.x.abs();
        let mut yy = self.y.abs();
        if yy > xx {
            std::mem::swap(&mut xx, &mut yy);
        }
        (xx, yy, self.z.abs(), self.w.abs())
    }

    fn split_key(&self) -> (i32, i32) {
        (
            self.x * self.x + self.y * self.y,
            2 * self.z * self.z + 2 * self.w * self.w,
        )
    }
}

impl fmt::Display for SumTuple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(x={}, y={}, z={}, w={})",
            self.x, self.y, self.z, self.w
        )
    }
}

#[derive(Clone, Debug)]
struct SearchConfig {
    problem: Problem,
    theta_samples: usize,
    boundary_k: usize,
    max_z: usize,
    max_w: usize,
    max_pairs_per_bucket: usize,
    benchmark_repeats: usize,
}

impl Default for SearchConfig {
    fn default() -> Self {
        Self {
            problem: Problem::new(56),
            theta_samples: 256,
            boundary_k: 6,
            max_z: 10_000,
            max_w: 10_000,
            max_pairs_per_bucket: 5_000,
            benchmark_repeats: 0,
        }
    }
}

#[derive(Clone, Debug)]
struct CandidateZW {
    z: PackedSeq,
    w: PackedSeq,
    zw_autocorr: Vec<i32>,
}

#[derive(Default, Clone, Debug)]
struct SearchStats {
    z_generated: usize,
    z_spectral_ok: usize,
    w_generated: usize,
    w_spectral_ok: usize,
    candidate_pair_attempts: usize,
    candidate_pair_spectral_ok: usize,
    xy_nodes: usize,
    xy_pruned_sum: usize,
    xy_pruned_autocorr: usize,
    xy_pruned_lex: usize,
}

impl SearchStats {
    fn work_units(&self) -> usize {
        self.z_generated + self.w_generated + self.candidate_pair_attempts + self.xy_nodes
    }

    fn merge_from(&mut self, other: &SearchStats) {
        self.z_generated += other.z_generated;
        self.z_spectral_ok += other.z_spectral_ok;
        self.w_generated += other.w_generated;
        self.w_spectral_ok += other.w_spectral_ok;
        self.candidate_pair_attempts += other.candidate_pair_attempts;
        self.candidate_pair_spectral_ok += other.candidate_pair_spectral_ok;
        self.xy_nodes += other.xy_nodes;
        self.xy_pruned_sum += other.xy_pruned_sum;
        self.xy_pruned_autocorr += other.xy_pruned_autocorr;
        self.xy_pruned_lex += other.xy_pruned_lex;
    }
}

#[derive(Clone, Debug)]
struct SeqWithSpectrum {
    seq: PackedSeq,
    spectrum: Vec<f64>,
    autocorr: Vec<i32>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum BoundarySignature {
    Packed { bits: u64, len: u8 },
    Raw(Vec<i8>),
}

#[derive(Clone, Debug)]
struct SpectralTable {
    cos: Vec<Vec<f64>>,
    sin: Vec<Vec<f64>>,
}

impl SpectralTable {
    fn new(n: usize, samples: usize) -> Self {
        let mut cos = vec![vec![0.0; n]; samples];
        let mut sin = vec![vec![0.0; n]; samples];
        for i in 0..samples {
            let theta = (i as f64) * std::f64::consts::PI / ((samples - 1).max(1) as f64);
            for j in 0..n {
                let x = (j as f64) * theta;
                cos[i][j] = x.cos();
                sin[i][j] = x.sin();
            }
        }
        Self { cos, sin }
    }
}

fn enumerate_sum_tuples(problem: Problem) -> Vec<SumTuple> {
    let mut out = Vec::new();
    let w_values = problem.valid_w_values();

    for x in (-(problem.n as i32))..=(problem.n as i32) {
        if x % 2 != 0 {
            continue;
        }
        for y in (-(problem.n as i32))..=(problem.n as i32) {
            if y % 2 != 0 {
                continue;
            }
            for z in (-(problem.n as i32))..=(problem.n as i32) {
                if z % 2 != 0 {
                    continue;
                }
                for &w in &w_values {
                    let lhs = x * x + y * y + 2 * z * z + 2 * w * w;
                    if lhs == problem.target_energy() {
                        out.push(SumTuple { x, y, z, w });
                    }
                }
            }
        }
    }

    out
}

fn normalized_tuples(raw: &[SumTuple]) -> Vec<SumTuple> {
    let mut seen = HashMap::new();
    for t in raw {
        seen.entry(t.norm_key()).or_insert(*t);
    }
    let mut items: Vec<_> = seen.into_values().collect();
    items.sort_by_key(|t| t.norm_key());
    items
}

fn grouped_splits(raw: &[SumTuple]) -> BTreeMap<(i32, i32), Vec<SumTuple>> {
    let mut m = BTreeMap::new();
    for &t in raw {
        m.entry(t.split_key()).or_insert_with(Vec::new).push(t);
    }
    m
}

fn boundary_signature_from_values(values: &[i8], k: usize) -> BoundarySignature {
    let k = k.min(values.len());
    let len = k * 2;
    if len <= 64 {
        let mut bits = 0u64;
        for i in 0..k {
            if values[i] == 1 {
                bits |= 1u64 << i;
            }
        }
        for i in 0..k {
            if values[values.len() - k + i] == 1 {
                bits |= 1u64 << (k + i);
            }
        }
        BoundarySignature::Packed {
            bits,
            len: len as u8,
        }
    } else {
        let mut sig = Vec::with_capacity(len);
        sig.extend_from_slice(&values[..k]);
        sig.extend_from_slice(&values[values.len() - k..]);
        BoundarySignature::Raw(sig)
    }
}

fn autocorrs_from_values(values: &[i8]) -> Vec<i32> {
    let n = values.len();
    let mut out = vec![0; n];
    for s in 0..n {
        let mut acc = 0i32;
        for i in 0..(n - s) {
            acc += (values[i] as i32) * (values[i + s] as i32);
        }
        out[s] = acc;
    }
    out
}

fn spectrum_if_ok(values: &[i8], table: &SpectralTable, bound: f64) -> Option<Vec<f64>> {
    let mut spectrum = Vec::with_capacity(table.cos.len());
    for i in 0..table.cos.len() {
        let cos_row = &table.cos[i];
        let sin_row = &table.sin[i];
        let mut re = 0.0f64;
        let mut im = 0.0f64;
        for j in 0..values.len() {
            if values[j] == 1 {
                re += cos_row[j];
                im += sin_row[j];
            } else {
                re -= cos_row[j];
                im -= sin_row[j];
            }
        }
        let p = re * re + im * im;
        if p > bound {
            return None;
        }
        spectrum.push(p);
    }
    Some(spectrum)
}

fn spectral_pair_ok(z_spectrum: &[f64], w_spectrum: &[f64], bound: f64) -> bool {
    for i in 0..z_spectrum.len() {
        let pz = z_spectrum[i];
        let pw = w_spectrum[i];
        if pz > bound || pw > bound || pz + pw > bound {
            return false;
        }
    }
    true
}

#[allow(dead_code)]
fn generate_sequences_with_sum(
    len: usize,
    target_sum: i32,
    root_one: bool,
    tail_one: bool,
    limit: usize,
) -> Vec<PackedSeq> {
    let mut out = Vec::new();
    generate_sequences_with_sum_visit(len, target_sum, root_one, tail_one, limit, |values| {
        out.push(PackedSeq::from_values(values));
    });
    out
}

fn generate_sequences_with_sum_visit<F: FnMut(&[i8])>(
    len: usize,
    target_sum: i32,
    root_one: bool,
    tail_one: bool,
    limit: usize,
    mut visit: F,
) {
    let mut curr = vec![1i8; len];
    let mut emitted = 0usize;

    fn dfs(
        i: usize,
        len: usize,
        curr_sum: i32,
        target_sum: i32,
        curr: &mut [i8],
        emitted: &mut usize,
        limit: usize,
        root_one: bool,
        tail_one: bool,
        visit: &mut impl FnMut(&[i8]),
    ) {
        if *emitted >= limit {
            return;
        }
        if i == len {
            if curr_sum == target_sum {
                *emitted += 1;
                visit(curr);
            }
            return;
        }

        if root_one && i == 0 {
            curr[0] = 1;
            dfs(
                i + 1,
                len,
                curr_sum + 1,
                target_sum,
                curr,
                emitted,
                limit,
                root_one,
                tail_one,
                visit,
            );
            return;
        }

        if tail_one && i == len - 1 {
            curr[i] = 1;
            dfs(
                i + 1,
                len,
                curr_sum + 1,
                target_sum,
                curr,
                emitted,
                limit,
                root_one,
                tail_one,
                visit,
            );
            return;
        }

        let remaining_total = (len - i - 1) as i32;
        let forced_plus = if tail_one && i < (len - 1) { 1 } else { 0 };
        let free_remaining = remaining_total - forced_plus;

        curr[i] = 1;
        let max_pos = curr_sum + 1 + forced_plus + free_remaining;
        let min_pos = curr_sum + 1 + forced_plus - free_remaining;
        if target_sum >= min_pos && target_sum <= max_pos {
            dfs(
                i + 1,
                len,
                curr_sum + 1,
                target_sum,
                curr,
                emitted,
                limit,
                root_one,
                tail_one,
                visit,
            );
        }

        curr[i] = -1;
        let max_neg = curr_sum - 1 + forced_plus + free_remaining;
        let min_neg = curr_sum - 1 + forced_plus - free_remaining;
        if target_sum >= min_neg && target_sum <= max_neg {
            dfs(
                i + 1,
                len,
                curr_sum - 1,
                target_sum,
                curr,
                emitted,
                limit,
                root_one,
                tail_one,
                visit,
            );
        }
    }

    dfs(
        0,
        len,
        0,
        target_sum,
        &mut curr,
        &mut emitted,
        limit,
        root_one,
        tail_one,
        &mut visit,
    );
}

fn build_zw_candidates(
    problem: Problem,
    tuple: SumTuple,
    cfg: &SearchConfig,
    spectral_z: &SpectralTable,
    spectral_w: &SpectralTable,
    stats: &mut SearchStats,
) -> Vec<CandidateZW> {
    let mut z_buckets: HashMap<BoundarySignature, Vec<SeqWithSpectrum>> = HashMap::new();
    generate_sequences_with_sum_visit(problem.n, tuple.z, true, true, cfg.max_z, |values| {
        stats.z_generated += 1;
        if let Some(spectrum) = spectrum_if_ok(values, spectral_z, problem.spectral_bound()) {
            stats.z_spectral_ok += 1;
            z_buckets
                .entry(boundary_signature_from_values(values, cfg.boundary_k))
                .or_default()
                .push(SeqWithSpectrum {
                    spectrum,
                    autocorr: autocorrs_from_values(values),
                    seq: PackedSeq::from_values(values),
                });
        }
    });

    let mut w_buckets: HashMap<BoundarySignature, Vec<SeqWithSpectrum>> = HashMap::new();
    generate_sequences_with_sum_visit(problem.m(), tuple.w, true, false, cfg.max_w, |values| {
        stats.w_generated += 1;
        if let Some(spectrum) = spectrum_if_ok(values, spectral_w, problem.spectral_bound()) {
            stats.w_spectral_ok += 1;
            w_buckets
                .entry(boundary_signature_from_values(values, cfg.boundary_k))
                .or_default()
                .push(SeqWithSpectrum {
                    spectrum,
                    autocorr: autocorrs_from_values(values),
                    seq: PackedSeq::from_values(values),
                });
        }
    });

    let mut out = Vec::new();
    for (sig, zs) in &z_buckets {
        let Some(ws) = w_buckets.get(sig) else {
            continue;
        };

        let mut taken = 0usize;
        for z in zs {
            for w in ws {
                stats.candidate_pair_attempts += 1;
                if spectral_pair_ok(&z.spectrum, &w.spectrum, problem.spectral_bound()) {
                    stats.candidate_pair_spectral_ok += 1;
                    let mut zw = vec![0; problem.n];
                    for (s, slot) in zw.iter_mut().enumerate().skip(1) {
                        let nz = z.autocorr[s];
                        let nw = if s < problem.m() { w.autocorr[s] } else { 0 };
                        *slot = 2 * nz + 2 * nw;
                    }
                    out.push(CandidateZW {
                        z: z.seq.clone(),
                        w: w.seq.clone(),
                        zw_autocorr: zw,
                    });
                    taken += 1;
                    if taken >= cfg.max_pairs_per_bucket {
                        break;
                    }
                }
            }
            if taken >= cfg.max_pairs_per_bucket {
                break;
            }
        }
    }
    out
}

#[derive(Clone)]
struct XYState {
    x: Vec<i8>,
    y: Vec<i8>,
    assigned: Vec<bool>,
    assigned_positions: Vec<usize>,
    known_lag: Vec<i32>,
    unknown_lag: Vec<i32>,
    sum_x: i32,
    sum_y: i32,
    remaining_unassigned: usize,
}

impl XYState {
    fn new(n: usize) -> Self {
        let mut unknown_lag = vec![0; n];
        for (s, slot) in unknown_lag.iter_mut().enumerate().skip(1) {
            *slot = (n - s) as i32;
        }
        Self {
            x: vec![1; n],
            y: vec![1; n],
            assigned: vec![false; n],
            assigned_positions: Vec::with_capacity(n),
            known_lag: vec![0; n],
            unknown_lag,
            sum_x: 0,
            sum_y: 0,
            remaining_unassigned: n,
        }
    }

    fn set_pair(&mut self, idx: usize, xv: i8, yv: i8) {
        if !self.assigned[idx] {
            self.x[idx] = xv;
            self.y[idx] = yv;
            self.update_lags_for_set(idx);
            self.assigned[idx] = true;
            self.assigned_positions.push(idx);
            self.sum_x += xv as i32;
            self.sum_y += yv as i32;
            self.remaining_unassigned -= 1;
        }
    }

    fn unset_pair(&mut self, idx: usize) {
        if self.assigned[idx] {
            self.update_lags_for_unset(idx);
            self.sum_x -= self.x[idx] as i32;
            self.sum_y -= self.y[idx] as i32;
            self.assigned[idx] = false;
            if let Some(slot) = self.assigned_positions.iter().position(|&p| p == idx) {
                self.assigned_positions.swap_remove(slot);
            }
            self.remaining_unassigned += 1;
        }
    }

    fn update_lags_for_set(&mut self, idx: usize) {
        let xi = self.x[idx] as i32;
        let yi = self.y[idx] as i32;
        for &j in &self.assigned_positions {
            let s = idx.abs_diff(j);
            if s == 0 {
                continue;
            }
            self.unknown_lag[s] -= 1;
            self.known_lag[s] += (self.x[j] as i32) * xi + (self.y[j] as i32) * yi;
        }
    }

    fn update_lags_for_unset(&mut self, idx: usize) {
        let xi = self.x[idx] as i32;
        let yi = self.y[idx] as i32;
        for &j in &self.assigned_positions {
            let s = idx.abs_diff(j);
            if s == 0 {
                continue;
            }
            self.unknown_lag[s] += 1;
            self.known_lag[s] -= (self.x[j] as i32) * xi + (self.y[j] as i32) * yi;
        }
    }

    fn is_complete(&self) -> bool {
        self.remaining_unassigned == 0
    }
}

fn mirror_allowed(xi: i8, xj: i8, yi: i8, yj: i8) -> bool {
    (xi * xj + yi * yj) == 0
}

fn partial_autocorr_bounds(known: i32, unknown_pairs: i32, target: i32) -> bool {
    let min_possible = known - 2 * unknown_pairs;
    let max_possible = known + 2 * unknown_pairs;
    target >= min_possible && target <= max_possible
}

fn lex_leq(a: &[i8], b: &[i8]) -> bool {
    for (&x, &y) in a.iter().zip(b.iter()) {
        match x.cmp(&y) {
            Ordering::Less => return true,
            Ordering::Greater => return false,
            Ordering::Equal => continue,
        }
    }
    true
}

fn lex_leq_reversed(a: &[i8]) -> bool {
    let n = a.len();
    for i in 0..n {
        match a[i].cmp(&a[n - 1 - i]) {
            Ordering::Less => return true,
            Ordering::Greater => return false,
            Ordering::Equal => continue,
        }
    }
    true
}

fn backtrack_xy(
    problem: Problem,
    tuple: SumTuple,
    candidate: &CandidateZW,
    stats: &mut SearchStats,
) -> Option<(PackedSeq, PackedSeq)> {
    let mut st = XYState::new(problem.n);
    st.set_pair(0, 1, 1);

    fn recurse(
        pos: usize,
        problem: Problem,
        tuple: SumTuple,
        cand: &CandidateZW,
        st: &mut XYState,
        stats: &mut SearchStats,
    ) -> bool {
        stats.xy_nodes += 1;
        if pos == problem.n {
            if st.sum_x != tuple.x || st.sum_y != tuple.y || !st.is_complete() {
                return false;
            }
            for s in 1..problem.n {
                let mut acc = cand.zw_autocorr[s];
                for i in 0..(problem.n - s) {
                    acc += (st.x[i] as i32) * (st.x[i + s] as i32)
                        + (st.y[i] as i32) * (st.y[i + s] as i32);
                }
                if acc != 0 {
                    return false;
                }
            }
            return true;
        }

        if st.assigned[pos] {
            return recurse(pos + 1, problem, tuple, cand, st, stats);
        }

        let mirror = problem.n - 1 - pos;
        let assignments: &[(i8, i8)] = &[(-1, 1), (1, -1), (1, 1), (-1, -1)];

        for &(xp, yp) in assignments {
            for &xq in &[1, -1] {
                for &yq in &[1, -1] {
                    if pos != mirror && !mirror_allowed(xp, xq, yp, yq) {
                        continue;
                    }

                    st.set_pair(pos, xp, yp);
                    if pos != mirror {
                        st.set_pair(mirror, xq, yq);
                    }

                    let rem = st.remaining_unassigned as i32;
                    if (tuple.x < st.sum_x - rem)
                        || (tuple.x > st.sum_x + rem)
                        || (tuple.y < st.sum_y - rem)
                        || (tuple.y > st.sum_y + rem)
                    {
                        stats.xy_pruned_sum += 1;
                        if pos != mirror {
                            st.unset_pair(mirror);
                        }
                        st.unset_pair(pos);
                        continue;
                    }

                    let mut ok = true;
                    for s in 1..problem.n {
                        let target = -cand.zw_autocorr[s];
                        if !partial_autocorr_bounds(st.known_lag[s], st.unknown_lag[s], target) {
                            stats.xy_pruned_autocorr += 1;
                            ok = false;
                            break;
                        }
                    }

                    if ok {
                        if !lex_leq_reversed(&st.x) || !lex_leq_reversed(&st.y) {
                            stats.xy_pruned_lex += 1;
                            ok = false;
                        }
                        if ok && !lex_leq(&st.x, &st.y) {
                            stats.xy_pruned_lex += 1;
                            ok = false;
                        }
                    }

                    if ok && recurse(pos + 1, problem, tuple, cand, st, stats) {
                        return true;
                    }

                    if pos != mirror {
                        st.unset_pair(mirror);
                    }
                    st.unset_pair(pos);
                }
            }
        }

        false
    }

    if recurse(1, problem, tuple, candidate, &mut st, stats) {
        Some((PackedSeq::from_values(&st.x), PackedSeq::from_values(&st.y)))
    } else {
        None
    }
}

fn verify_tt(problem: Problem, x: &PackedSeq, y: &PackedSeq, z: &PackedSeq, w: &PackedSeq) -> bool {
    if x.len() != problem.n
        || y.len() != problem.n
        || z.len() != problem.n
        || w.len() != problem.m()
    {
        return false;
    }

    for s in 1..problem.n {
        let nx = x.autocorrelation(s);
        let ny = y.autocorrelation(s);
        let nz = z.autocorrelation(s);
        let nw = if s < problem.m() {
            w.autocorrelation(s)
        } else {
            0
        };
        if nx + ny + 2 * nz + 2 * nw != 0 {
            return false;
        }
    }
    true
}

#[derive(Clone, Debug)]
struct SearchReport {
    stats: SearchStats,
    elapsed: std::time::Duration,
    found_solution: bool,
}

fn run_search(cfg: &SearchConfig, verbose: bool) -> SearchReport {
    let problem = cfg.problem;
    let run_start = Instant::now();
    let mut stats = SearchStats::default();
    let spectral_z = SpectralTable::new(problem.n, cfg.theta_samples);
    let spectral_w = SpectralTable::new(problem.m(), cfg.theta_samples);

    let phase_a_start = Instant::now();
    let raw = enumerate_sum_tuples(problem);
    let norm = normalized_tuples(&raw);
    let groups = grouped_splits(&raw);
    let phase_a_elapsed = phase_a_start.elapsed();

    if verbose {
        println!(
            "TT({}): target energy {}. Phase A: {} raw tuples, {} normalized",
            problem.n,
            problem.target_energy(),
            raw.len(),
            norm.len()
        );
        println!("Phase A: {} split groups", groups.len());
        println!("Phase A elapsed: {:.3?}", phase_a_elapsed);
    }

    if !verbose {
        let workers = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
            .max(1);
        if norm.len() < workers * 2 {
            let mut found_solution = false;
            for tuple in &norm {
                let zw_candidates =
                    build_zw_candidates(problem, *tuple, cfg, &spectral_z, &spectral_w, &mut stats);
                for cand in &zw_candidates {
                    if let Some((x, y)) = backtrack_xy(problem, *tuple, cand, &mut stats) {
                        found_solution = verify_tt(problem, &x, &y, &cand.z, &cand.w);
                        if found_solution {
                            break;
                        }
                    }
                }
                if found_solution {
                    break;
                }
            }

            return SearchReport {
                stats,
                elapsed: run_start.elapsed(),
                found_solution,
            };
        }

        let chunk_size = norm.len().div_ceil(workers).max(1);
        let norm_arc = Arc::new(norm);
        let spectral_z = Arc::new(spectral_z);
        let spectral_w = Arc::new(spectral_w);
        let mut handles = Vec::new();

        for chunk_idx in 0..workers {
            let start = chunk_idx * chunk_size;
            if start >= norm_arc.len() {
                break;
            }
            let end = ((chunk_idx + 1) * chunk_size).min(norm_arc.len());
            let tuples = Arc::clone(&norm_arc);
            let sz = Arc::clone(&spectral_z);
            let sw = Arc::clone(&spectral_w);
            let cfg = cfg.clone();

            handles.push(std::thread::spawn(move || {
                let mut local_stats = SearchStats::default();
                let mut found_solution = false;
                for idx in start..end {
                    let tuple = tuples[idx];
                    let zw_candidates =
                        build_zw_candidates(problem, tuple, &cfg, &sz, &sw, &mut local_stats);
                    for cand in &zw_candidates {
                        if let Some((x, y)) = backtrack_xy(problem, tuple, cand, &mut local_stats) {
                            found_solution = verify_tt(problem, &x, &y, &cand.z, &cand.w);
                            if found_solution {
                                break;
                            }
                        }
                    }
                    if found_solution {
                        break;
                    }
                }
                (local_stats, found_solution)
            }));
        }

        let mut found_solution = false;
        for handle in handles {
            if let Ok((local, found)) = handle.join() {
                stats.merge_from(&local);
                found_solution |= found;
            }
        }

        return SearchReport {
            stats,
            elapsed: run_start.elapsed(),
            found_solution,
        };
    }

    for tuple in norm {
        let phase_b_start = Instant::now();
        if verbose {
            println!("Trying tuple family {tuple}");
        }
        let zw_candidates =
            build_zw_candidates(problem, tuple, cfg, &spectral_z, &spectral_w, &mut stats);
        if verbose {
            println!("  Phase B: {} candidate (Z,W) pairs", zw_candidates.len());
            println!("  Phase B elapsed: {:.3?}", phase_b_start.elapsed());
        }

        for (idx, cand) in zw_candidates.iter().enumerate() {
            let phase_c_start = Instant::now();
            if let Some((x, y)) = backtrack_xy(problem, tuple, cand, &mut stats) {
                if verbose {
                    println!("Found candidate solution in bucket {}", idx);
                    println!("X={} (sum={})", x.as_string(), x.sum());
                    println!("Y={} (sum={})", y.as_string(), y.sum());
                    println!("Z={} (sum={})", cand.z.as_string(), cand.z.sum());
                    println!("W={} (sum={})", cand.w.as_string(), cand.w.sum());
                }
                let ok = verify_tt(problem, &x, &y, &cand.z, &cand.w);
                if verbose {
                    println!("Verification: {ok}");
                    println!("Phase C elapsed: {:.3?}", phase_c_start.elapsed());
                    println!(
                        "Search stats: z_gen={}, z_spec_ok={}, w_gen={}, w_spec_ok={}, pair_attempts={}, pair_spec_ok={}, xy_nodes={}, prune_sum={}, prune_ac={}, prune_lex={}, total_elapsed={:.3?}",
                        stats.z_generated,
                        stats.z_spectral_ok,
                        stats.w_generated,
                        stats.w_spectral_ok,
                        stats.candidate_pair_attempts,
                        stats.candidate_pair_spectral_ok,
                        stats.xy_nodes,
                        stats.xy_pruned_sum,
                        stats.xy_pruned_autocorr,
                        stats.xy_pruned_lex,
                        run_start.elapsed(),
                    );
                }
                return SearchReport {
                    stats,
                    elapsed: run_start.elapsed(),
                    found_solution: ok,
                };
            }
            if verbose {
                println!(
                    "  Phase C elapsed (bucket {}): {:.3?}",
                    idx,
                    phase_c_start.elapsed()
                );
            }
        }
    }

    if verbose {
        println!(
            "Search stats: z_gen={}, z_spec_ok={}, w_gen={}, w_spec_ok={}, pair_attempts={}, pair_spec_ok={}, xy_nodes={}, prune_sum={}, prune_ac={}, prune_lex={}, total_elapsed={:.3?}",
            stats.z_generated,
            stats.z_spectral_ok,
            stats.w_generated,
            stats.w_spectral_ok,
            stats.candidate_pair_attempts,
            stats.candidate_pair_spectral_ok,
            stats.xy_nodes,
            stats.xy_pruned_sum,
            stats.xy_pruned_autocorr,
            stats.xy_pruned_lex,
            run_start.elapsed(),
        );
        println!("No solution found with current bounds; increase limits for deeper search.");
    }
    SearchReport {
        stats,
        elapsed: run_start.elapsed(),
        found_solution: false,
    }
}

fn run_benchmark(cfg: &SearchConfig) {
    let repeats = cfg.benchmark_repeats.max(1);
    let warmup = run_search(cfg, false);
    println!(
        "benchmark,warmup,elapsed_ms={:.3},work_units={},found_solution={}",
        warmup.elapsed.as_secs_f64() * 1000.0,
        warmup.stats.work_units(),
        warmup.found_solution
    );
    println!(
        "benchmark,run,elapsed_ms,work_units,work_units_per_sec,z_gen,w_gen,pair_attempts,xy_nodes,found_solution"
    );
    let mut elapsed_ms = Vec::with_capacity(repeats);
    for run in 1..=repeats {
        let report = run_search(cfg, false);
        let ms = report.elapsed.as_secs_f64() * 1000.0;
        let work = report.stats.work_units();
        let rate = if report.elapsed.as_secs_f64() > 0.0 {
            work as f64 / report.elapsed.as_secs_f64()
        } else {
            0.0
        };
        elapsed_ms.push(ms);
        println!(
            "benchmark,{},{:.3},{},{:.3},{},{},{},{},{}",
            run,
            ms,
            work,
            rate,
            report.stats.z_generated,
            report.stats.w_generated,
            report.stats.candidate_pair_attempts,
            report.stats.xy_nodes,
            report.found_solution
        );
    }

    elapsed_ms.sort_by(|a, b| a.partial_cmp(b).unwrap_or(Ordering::Equal));
    let median = elapsed_ms[elapsed_ms.len() / 2];
    let mean = elapsed_ms.iter().sum::<f64>() / elapsed_ms.len() as f64;
    println!(
        "benchmark,summary,mean_ms={:.3},median_ms={:.3},repeats={}",
        mean, median, repeats
    );
}

fn parse_args() -> SearchConfig {
    let mut cfg = SearchConfig::default();
    for arg in env::args().skip(1) {
        if let Some(v) = arg.strip_prefix("--n=") {
            cfg.problem = Problem::new(v.parse().unwrap_or(cfg.problem.n));
        } else if let Some(v) = arg.strip_prefix("--theta=") {
            cfg.theta_samples = v.parse().unwrap_or(cfg.theta_samples);
        } else if let Some(v) = arg.strip_prefix("--k=") {
            cfg.boundary_k = v.parse().unwrap_or(cfg.boundary_k);
        } else if let Some(v) = arg.strip_prefix("--max-z=") {
            cfg.max_z = v.parse().unwrap_or(cfg.max_z);
        } else if let Some(v) = arg.strip_prefix("--max-w=") {
            cfg.max_w = v.parse().unwrap_or(cfg.max_w);
        } else if let Some(v) = arg.strip_prefix("--max-pairs=") {
            cfg.max_pairs_per_bucket = v.parse().unwrap_or(cfg.max_pairs_per_bucket);
        } else if let Some(v) = arg.strip_prefix("--benchmark=") {
            cfg.benchmark_repeats = v.parse().unwrap_or(1);
        } else if arg == "--benchmark" {
            cfg.benchmark_repeats = 5;
        }
    }
    cfg
}

fn main() {
    let cfg = parse_args();
    if cfg.benchmark_repeats > 0 {
        run_benchmark(&cfg);
    } else {
        run_search(&cfg, true);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tuple_equation_holds_for_tt56() {
        let p = Problem::new(56);
        let tuples = enumerate_sum_tuples(p);
        assert!(!tuples.is_empty());
        assert!(tuples.iter().all(|t| t.x * t.x + t.y * t.y + 2 * t.z * t.z + 2 * t.w * t.w == p.target_energy()));
    }

    #[test]
    fn tuple_equation_holds_for_tt8() {
        let p = Problem::new(8);
        let tuples = enumerate_sum_tuples(p);
        assert!(!tuples.is_empty());
        assert!(tuples.iter().all(|t| t.x * t.x + t.y * t.y + 2 * t.z * t.z + 2 * t.w * t.w == p.target_energy()));
    }

    #[test]
    fn packed_seq_ops() {
        let s = PackedSeq::from_values(&[1, -1, 1, -1, 1]);
        assert_eq!(s.sum(), 1);
        assert_eq!(s.reverse().as_string(), "+-+-+");
        assert_eq!(s.negate().as_string(), "-+-+-");
        assert_eq!(s.alternate().as_string(), "+++++");
    }

    #[test]
    fn verify_handles_trivial_false() {
        let p = Problem::new(8);
        let x = PackedSeq::from_values(&vec![1; p.n]);
        let y = PackedSeq::from_values(&vec![1; p.n]);
        let z = PackedSeq::from_values(&vec![1; p.n]);
        let w = PackedSeq::from_values(&vec![1; p.m()]);
        assert!(!verify_tt(p, &x, &y, &z, &w));
    }

    #[test]
    fn generator_respects_sum() {
        let seqs = generate_sequences_with_sum(8, 2, true, false, 1000);
        assert!(!seqs.is_empty());
        assert!(seqs.iter().all(|s| s.sum() == 2));
        assert!(seqs.iter().all(|s| s.get(0) == 1));
    }
}
