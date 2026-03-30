use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap};
use std::env;
use std::fmt;
use std::sync::atomic::{AtomicBool, Ordering as AtomicOrdering};
use std::sync::Arc;
use std::time::Instant;

use rustfft::{FftPlanner, num_complex::Complex};

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
        let limit = self.len - shift;
        let mut i = 0usize;
        while i + 4 <= limit {
            acc += (self.get(i) as i32) * (self.get(i + shift) as i32);
            acc += (self.get(i + 1) as i32) * (self.get(i + 1 + shift) as i32);
            acc += (self.get(i + 2) as i32) * (self.get(i + 2 + shift) as i32);
            acc += (self.get(i + 3) as i32) * (self.get(i + 3 + shift) as i32);
            i += 4;
        }
        while i < limit {
            acc += (self.get(i) as i32) * (self.get(i + shift) as i32);
            i += 1;
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
    stochastic: bool,
    stochastic_seconds: u64,
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
            stochastic: false,
            stochastic_seconds: 0,
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

#[derive(Clone)]
struct SpectralFilter {
    fft_size: usize,
    fft: Arc<dyn rustfft::Fft<f64>>,
}

impl fmt::Debug for SpectralFilter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SpectralFilter")
            .field("fft_size", &self.fft_size)
            .finish()
    }
}

impl SpectralFilter {
    fn new(seq_len: usize, theta_samples: usize) -> Self {
        // FFT of size M yields M/2+1 unique frequency bins for real input.
        // To match theta_samples frequency checks, need M >= 2*theta_samples.
        // Use at least 4*n for minimum spectral resolution.
        let min_size = (4 * seq_len).max(2 * theta_samples);
        let fft_size = min_size.next_power_of_two().max(16);
        let mut planner = FftPlanner::new();
        let fft = planner.plan_fft_forward(fft_size);
        Self { fft_size, fft }
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
        let limit = n - s;
        let mut i = 0usize;
        while i + 4 <= limit {
            acc += (values[i] as i32) * (values[i + s] as i32);
            acc += (values[i + 1] as i32) * (values[i + 1 + s] as i32);
            acc += (values[i + 2] as i32) * (values[i + 2 + s] as i32);
            acc += (values[i + 3] as i32) * (values[i + 3 + s] as i32);
            i += 4;
        }
        while i < limit {
            acc += (values[i] as i32) * (values[i + s] as i32);
            i += 1;
        }
        out[s] = acc;
    }
    out
}

fn spectrum_if_ok(
    values: &[i8],
    filter: &SpectralFilter,
    bound: f64,
    fft_buf: &mut Vec<Complex<f64>>,
) -> Option<Vec<f64>> {
    let m = filter.fft_size;
    fft_buf.clear();
    for &v in values {
        fft_buf.push(Complex::new(v as f64, 0.0));
    }
    fft_buf.resize(m, Complex::new(0.0, 0.0));
    filter.fft.process(fft_buf);
    // Only check [0, M/2] — real sequence has symmetric spectrum
    let half = m / 2 + 1;
    let mut spectrum = Vec::with_capacity(half);
    for k in 0..half {
        let p = fft_buf[k].norm_sqr();
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
    spectral_z: &SpectralFilter,
    spectral_w: &SpectralFilter,
    stats: &mut SearchStats,
) -> Vec<CandidateZW> {
    fn push_capped(
        buckets: &mut HashMap<BoundarySignature, Vec<SeqWithSpectrum>>,
        key: BoundarySignature,
        value: SeqWithSpectrum,
        cap: usize,
    ) {
        let bucket = buckets.entry(key).or_default();
        if bucket.len() < cap {
            bucket.push(value);
        }
    }

    let mut z_buckets: HashMap<BoundarySignature, Vec<SeqWithSpectrum>> = HashMap::new();
    let mut fft_buf = Vec::with_capacity(spectral_z.fft_size);
    generate_sequences_with_sum_visit(problem.n, tuple.z, true, true, cfg.max_z, |values| {
        stats.z_generated += 1;
        if let Some(spectrum) =
            spectrum_if_ok(values, spectral_z, problem.spectral_bound(), &mut fft_buf)
        {
            stats.z_spectral_ok += 1;
            push_capped(
                &mut z_buckets,
                boundary_signature_from_values(values, cfg.boundary_k),
                SeqWithSpectrum {
                    spectrum,
                    autocorr: autocorrs_from_values(values),
                    seq: PackedSeq::from_values(values),
                },
                cfg.max_pairs_per_bucket.max(1),
            );
        }
    });

    let mut w_buckets: HashMap<BoundarySignature, Vec<SeqWithSpectrum>> = HashMap::new();
    fft_buf.clear();
    generate_sequences_with_sum_visit(problem.m(), tuple.w, true, false, cfg.max_w, |values| {
        stats.w_generated += 1;
        if let Some(spectrum) =
            spectrum_if_ok(values, spectral_w, problem.spectral_bound(), &mut fft_buf)
        {
            stats.w_spectral_ok += 1;
            push_capped(
                &mut w_buckets,
                boundary_signature_from_values(values, cfg.boundary_k),
                SeqWithSpectrum {
                    spectrum,
                    autocorr: autocorrs_from_values(values),
                    seq: PackedSeq::from_values(values),
                },
                cfg.max_pairs_per_bucket.max(1),
            );
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
    assigned_position_slot: Vec<usize>,
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
            assigned_position_slot: vec![usize::MAX; n],
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
            self.assigned_position_slot[idx] = self.assigned_positions.len();
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
            let slot = self.assigned_position_slot[idx];
            let last = self.assigned_positions.len() - 1;
            let moved = if slot < last {
                Some(self.assigned_positions[last])
            } else {
                None
            };
            self.assigned_positions.swap_remove(slot);
            self.assigned_position_slot[idx] = usize::MAX;
            if let Some(moved_idx) = moved {
                self.assigned_position_slot[moved_idx] = slot;
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
        problem: Problem,
        tuple: SumTuple,
        cand: &CandidateZW,
        st: &mut XYState,
        stats: &mut SearchStats,
    ) -> bool {
        stats.xy_nodes += 1;
        if st.is_complete() {
            if st.sum_x != tuple.x || st.sum_y != tuple.y || !st.is_complete() {
                return false;
            }
            for s in 1..problem.n {
                let mut acc = cand.zw_autocorr[s];
                let limit = problem.n - s;
                let mut i = 0usize;
                while i + 4 <= limit {
                    acc += (st.x[i] as i32) * (st.x[i + s] as i32)
                        + (st.y[i] as i32) * (st.y[i + s] as i32);
                    acc += (st.x[i + 1] as i32) * (st.x[i + 1 + s] as i32)
                        + (st.y[i + 1] as i32) * (st.y[i + 1 + s] as i32);
                    acc += (st.x[i + 2] as i32) * (st.x[i + 2 + s] as i32)
                        + (st.y[i + 2] as i32) * (st.y[i + 2 + s] as i32);
                    acc += (st.x[i + 3] as i32) * (st.x[i + 3 + s] as i32)
                        + (st.y[i + 3] as i32) * (st.y[i + 3 + s] as i32);
                    i += 4;
                }
                while i < limit {
                    acc += (st.x[i] as i32) * (st.x[i + s] as i32)
                        + (st.y[i] as i32) * (st.y[i + s] as i32);
                    i += 1;
                }
                if acc != 0 {
                    return false;
                }
            }
            return true;
        }

        let mut best_pos = None;
        let mut best_score = i32::MIN;
        for pos in 1..problem.n {
            if st.assigned[pos] {
                continue;
            }
            let mirror = problem.n - 1 - pos;
            let mut score = 0i32;
            for &j in &st.assigned_positions {
                if j == pos || j == mirror {
                    continue;
                }
                if pos.abs_diff(j) > 0 {
                    score += 1;
                }
                if mirror != pos && mirror.abs_diff(j) > 0 {
                    score += 1;
                }
            }
            if score > best_score {
                best_score = score;
                best_pos = Some(pos);
            }
        }
        let Some(pos) = best_pos else {
            return false;
        };

        let mirror = problem.n - 1 - pos;
        let assignments: &[(i8, i8)] = &[(-1, 1), (1, -1), (1, 1), (-1, -1)];

        for &(xp, yp) in assignments {
            for &xq in &[1, -1] {
                for &yq in &[1, -1] {
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

                    if ok && st.is_complete() {
                        if !lex_leq_reversed(&st.x) || !lex_leq_reversed(&st.y) {
                            stats.xy_pruned_lex += 1;
                            ok = false;
                        }
                        if ok && !lex_leq(&st.x, &st.y) {
                            stats.xy_pruned_lex += 1;
                            ok = false;
                        }
                    }

                    if ok && recurse(problem, tuple, cand, st, stats) {
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

    if recurse(problem, tuple, candidate, &mut st, stats) {
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

fn find_small_tt_exhaustive(problem: Problem, stats: &mut SearchStats) -> bool {
    if problem.n > 4 {
        return false;
    }

    fn decode(mask: usize, len: usize) -> Vec<i8> {
        let mut out = vec![-1; len];
        for (i, slot) in out.iter_mut().enumerate().take(len) {
            if ((mask >> i) & 1) == 1 {
                *slot = 1;
            }
        }
        out
    }

    let n = problem.n;
    let m = problem.m();
    for mx in 0..(1usize << n) {
        let x = decode(mx, n);
        for my in 0..(1usize << n) {
            let y = decode(my, n);
            for mz in 0..(1usize << n) {
                let z = decode(mz, n);
                for mw in 0..(1usize << m) {
                    let w = decode(mw, m);
                    stats.xy_nodes += 1;
                    let px = PackedSeq::from_values(&x);
                    let py = PackedSeq::from_values(&y);
                    let pz = PackedSeq::from_values(&z);
                    let pw = PackedSeq::from_values(&w);
                    if verify_tt(problem, &px, &py, &pz, &pw) {
                        return true;
                    }
                }
            }
        }
    }
    false
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

    if problem.n <= 4 {
        let found_solution = find_small_tt_exhaustive(problem, &mut stats);
        return SearchReport {
            stats,
            elapsed: run_start.elapsed(),
            found_solution,
        };
    }

    // Both z (length n) and w (length m=n-1) filters must use same FFT size
    // so their spectrums align for spectral_pair_ok comparison.
    let max_seq_len = problem.n;
    let spectral_z = SpectralFilter::new(max_seq_len, cfg.theta_samples);
    let spectral_w = SpectralFilter::new(max_seq_len, cfg.theta_samples);

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
    if cfg.stochastic {
        run_stochastic_benchmark(cfg);
    } else {
        run_exhaustive_benchmark(cfg);
    }
}

fn run_exhaustive_benchmark(cfg: &SearchConfig) {
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

fn run_stochastic_benchmark(cfg: &SearchConfig) {
    let secs = if cfg.stochastic_seconds > 0 { cfg.stochastic_seconds } else { 10 };
    let repeats = cfg.benchmark_repeats.max(1);
    // Warmup
    let warmup = stochastic_search(cfg.problem, false, secs);
    let warmup_rate = warmup.stats.xy_nodes as f64 / warmup.elapsed.as_secs_f64();
    println!(
        "benchmark,warmup,elapsed_s={:.3},flips={},flips_per_sec={:.0},found_solution={}",
        warmup.elapsed.as_secs_f64(),
        warmup.stats.xy_nodes,
        warmup_rate,
        warmup.found_solution
    );
    println!("benchmark,run,elapsed_s,flips,flips_per_sec,found_solution");
    let mut rates = Vec::with_capacity(repeats);
    for run in 1..=repeats {
        let report = stochastic_search(cfg.problem, false, secs);
        let rate = report.stats.xy_nodes as f64 / report.elapsed.as_secs_f64();
        rates.push(rate);
        println!(
            "benchmark,{},{:.3},{},{:.0},{}",
            run,
            report.elapsed.as_secs_f64(),
            report.stats.xy_nodes,
            rate,
            report.found_solution
        );
    }
    rates.sort_by(|a, b| a.partial_cmp(b).unwrap_or(Ordering::Equal));
    let median = rates[rates.len() / 2];
    let mean = rates.iter().sum::<f64>() / rates.len() as f64;
    println!(
        "benchmark,summary,mean_flips_per_sec={:.0},median_flips_per_sec={:.0},repeats={}",
        mean, median, repeats
    );
}

fn compute_corr(problem: Problem, x: &[i8], y: &[i8], z: &[i8], w: &[i8]) -> Vec<i32> {
    let n = problem.n;
    let m = problem.m();
    let mut corr = vec![0i32; n];
    for s in 1..n {
        let mut c = 0i32;
        for i in 0..(n - s) {
            c += (x[i] as i32) * (x[i + s] as i32)
                + (y[i] as i32) * (y[i + s] as i32)
                + 2 * (z[i] as i32) * (z[i + s] as i32);
        }
        if s < m {
            for i in 0..(m - s) {
                c += 2 * (w[i] as i32) * (w[i + s] as i32);
            }
        }
        corr[s] = c;
    }
    corr
}

fn defect_from_corr(corr: &[i32]) -> i64 {
    corr.iter().skip(1).map(|&c| (c as i64) * (c as i64)).sum()
}

fn stochastic_search(problem: Problem, verbose: bool, time_limit_secs: u64) -> SearchReport {
    let run_start = Instant::now();
    let workers = std::thread::available_parallelism()
        .map(|n| n.get()).unwrap_or(1).max(1);
    if verbose {
        println!("TT({}): stochastic search with {} threads", problem.n, workers);
    }
    let time_limit = if time_limit_secs > 0 {
        Some(std::time::Duration::from_secs(time_limit_secs))
    } else {
        None
    };
    let found = Arc::new(AtomicBool::new(false));
    let norm = Arc::new(normalized_tuples(&enumerate_sum_tuples(problem)));
    let deadline = time_limit.map(|d| Instant::now() + d);
    let mut handles = Vec::new();
    for tid in 0..workers {
        let found = Arc::clone(&found);
        let norm = Arc::clone(&norm);
        handles.push(std::thread::spawn(move || {
            stochastic_worker(problem, &norm, &found, tid as u64, verbose && tid == 0, deadline)
        }));
    }
    let mut best = SearchReport { stats: SearchStats::default(), elapsed: run_start.elapsed(), found_solution: false };
    for h in handles {
        if let Ok(r) = h.join() {
            best.stats.merge_from(&r.stats);
            if r.found_solution { best.found_solution = true; }
        }
    }
    best.elapsed = run_start.elapsed();
    best
}

fn stochastic_worker(problem: Problem, norm: &[SumTuple], found: &AtomicBool, seed: u64, verbose: bool, deadline: Option<Instant>) -> SearchReport {
    let run_start = Instant::now();
    let mut stats = SearchStats::default();
    let n = problem.n;
    let m = problem.m();
    let mut rng_state: u64 = 0xdeadbeef12345678u64
        ^ seed.wrapping_mul(0x9e3779b97f4a7c15)
        ^ (std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default().as_nanos() as u64);
    let mut rng = || -> u64 { rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; rng_state };
    let rand_seq = |len: usize, rng: &mut dyn FnMut() -> u64| -> Vec<i8> {
        (0..len).map(|_| if rng() & 1 == 0 { 1 } else { -1 }).collect()
    };
    let fix_sum = |seq: &mut [i8], target: i32, rng: &mut dyn FnMut() -> u64, start: usize| {
        let len = seq.len();
        loop {
            let current: i32 = seq.iter().map(|&v| v as i32).sum();
            if current == target { break; }
            let idx = start + ((rng() as usize) % (len - start));
            if current < target && seq[idx] == -1 { seq[idx] = 1; }
            else if current > target && seq[idx] == 1 { seq[idx] = -1; }
        }
    };
    let max_restarts = 10_000_000;
    let max_flips = n * n * 50;
    for restart in 0..max_restarts {
        if found.load(AtomicOrdering::Relaxed) { break; }
        if let Some(dl) = deadline { if Instant::now() >= dl { break; } }
        let tuple = &norm[(rng() as usize) % norm.len()];
        let mut x = rand_seq(n, &mut rng);
        let mut y = rand_seq(n, &mut rng);
        let mut z = rand_seq(n, &mut rng);
        let mut w = rand_seq(m, &mut rng);
        x[0] = 1; y[0] = 1; z[0] = 1; z[n-1] = 1; w[0] = 1;
        fix_sum(&mut x, tuple.x, &mut rng, 1);
        fix_sum(&mut y, tuple.y, &mut rng, 1);
        fix_sum(&mut z[..n-1], tuple.z - 1, &mut rng, 1);
        fix_sum(&mut w, tuple.w, &mut rng, 1);
        let mut corr = compute_corr(problem, &x, &y, &z, &w);
        let mut defect = defect_from_corr(&corr);
        stats.xy_nodes += 1;
        if defect == 0 {
            found.store(true, AtomicOrdering::Relaxed);
            if verbose { println!("Solution found!"); }
            let ok = verify_tt(problem, &PackedSeq::from_values(&x), &PackedSeq::from_values(&y),
                               &PackedSeq::from_values(&z), &PackedSeq::from_values(&w));
            return SearchReport { stats, elapsed: run_start.elapsed(), found_solution: ok };
        }
        let mut temp = (defect as f64).sqrt().max(50.0);
        let cooling = (0.1f64 / temp).powf(1.0 / max_flips as f64).max(0.99);
        let mut delta_corr = vec![0i32; n];
        // Pre-build value-grouped index lists for O(1) partner finding.
        // pos_idx[seq][0] = indices with value +1, pos_idx[seq][1] = indices with value -1
        // Only include mutable indices (skip index 0 for all, skip n-1 for z).
        let mut pos_idx: [Vec<Vec<usize>>; 4] = [vec![vec![], vec![]], vec![vec![], vec![]], vec![vec![], vec![]], vec![vec![], vec![]]];
        let seqs_ref: [&[i8]; 4] = [&x, &y, &z, &w];
        let seq_lens = [n, n, n, m];
        for si in 0..4 {
            let upper = if si == 2 { n - 1 } else { seq_lens[si] };
            for i in 1..upper {
                let vi = if seqs_ref[si][i] == 1 { 0 } else { 1 };
                pos_idx[si][vi].push(i);
            }
        }
        for flip in 0..max_flips {
            if flip % 1000 == 0 && found.load(AtomicOrdering::Relaxed) { break; }
            let seq_idx = (rng() as usize) % 4;
            let seq_len = if seq_idx < 3 { n } else { m };
            let weight: i32 = if seq_idx < 2 { 1 } else { 2 };
            let seq: &mut [i8] = match seq_idx { 0 => &mut x, 1 => &mut y, 2 => &mut z, _ => &mut w };
            let vi_group = if rng() & 1 == 0 { 0usize } else { 1 };
            let group = &pos_idx[seq_idx][vi_group];
            if group.len() < 2 { continue; }
            let pi = (rng() as usize) % group.len();
            let mut qi = (rng() as usize) % (group.len() - 1);
            if qi >= pi { qi += 1; }
            let p = group[pi];
            let q = group[qi];
            let v = seq[p];
            let vi = v as i32;
            let mut new_defect = 0i64;
            // Early termination: in cold phase, reject as soon as partial
            // new_defect exceeds defect (acceptance probability ~0).
            let early_threshold = if temp < 1.0 { defect } else { i64::MAX };
            let mut completed = true;
            for s in 1..n {
                // Swapping two same-value positions: delta = -2*v * (sum of non-overlapping neighbors)
                let mut nb = 0i32;
                if p + s < seq_len && p + s != q { nb += seq[p + s] as i32; }
                if p >= s && p - s != q { nb += seq[p - s] as i32; }
                if q + s < seq_len && q + s != p { nb += seq[q + s] as i32; }
                if q >= s && q - s != p { nb += seq[q - s] as i32; }
                delta_corr[s] = -2 * vi * nb * weight;
                let new_c = corr[s] as i64 + delta_corr[s] as i64;
                new_defect += new_c * new_c;
                if new_defect > early_threshold {
                    completed = false;
                    break;
                }
            }
            stats.xy_nodes += 1;
            if !completed { temp *= cooling; continue; }
            let delta = new_defect - defect;
            let accept = if delta <= 0 { true }
                else if temp > 0.1 { (rng() % 10000) as f64 / 10000.0 < (-delta as f64 / temp).exp() }
                else { false };
            if accept {
                seq[p] = -v; seq[q] = -v;
                // Update pos_idx: move p and q from current group to opposite
                let old_group = vi_group;
                let new_group = 1 - old_group;
                pos_idx[seq_idx][old_group].retain(|&i| i != p && i != q);
                pos_idx[seq_idx][new_group].push(p);
                pos_idx[seq_idx][new_group].push(q);
                for s in 1..n { corr[s] += delta_corr[s]; }
                defect = new_defect;
                if defect == 0 {
                    let _ = seq;
                    found.store(true, AtomicOrdering::Relaxed);
                    if verbose {
                        println!("Solution found at restart {} flip {}!", restart, flip);
                        println!("X={}", x.iter().map(|&v| if v == 1 { '+' } else { '-' }).collect::<String>());
                        println!("Y={}", y.iter().map(|&v| if v == 1 { '+' } else { '-' }).collect::<String>());
                        println!("Z={}", z.iter().map(|&v| if v == 1 { '+' } else { '-' }).collect::<String>());
                        println!("W={}", w.iter().map(|&v| if v == 1 { '+' } else { '-' }).collect::<String>());
                    }
                    let ok = verify_tt(problem, &PackedSeq::from_values(&x), &PackedSeq::from_values(&y),
                                       &PackedSeq::from_values(&z), &PackedSeq::from_values(&w));
                    return SearchReport { stats, elapsed: run_start.elapsed(), found_solution: ok };
                }
            }
            temp *= cooling;
        }
        if verbose && restart % 5000 == 0 && restart > 0 {
            println!("Restart {}: defect={}, elapsed={:.1?}", restart, defect, run_start.elapsed());
        }
    }
    SearchReport { stats, elapsed: run_start.elapsed(), found_solution: false }
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
        } else if arg == "--stochastic" {
            cfg.stochastic = true;
        } else if let Some(v) = arg.strip_prefix("--stochastic-secs=") {
            cfg.stochastic_seconds = v.parse().unwrap_or(10);
            cfg.stochastic = true;
        }
    }
    cfg
}

fn main() {
    let cfg = parse_args();
    if cfg.benchmark_repeats > 0 {
        run_benchmark(&cfg);
    } else if cfg.stochastic {
        let report = stochastic_search(cfg.problem, true, cfg.stochastic_seconds);
        println!("Stochastic search: found_solution={}, elapsed={:.3?}", report.found_solution, report.elapsed);
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

    #[test]
    fn benchmark_profile_n4_finds_solution_fast() {
        let cfg = SearchConfig {
            problem: Problem::new(4),
            theta_samples: 64,
            boundary_k: 6,
            max_z: 200_000,
            max_w: 200_000,
            max_pairs_per_bucket: 2_000,
            benchmark_repeats: 1,
            stochastic: false,
            stochastic_seconds: 0,
        };
        let report = run_search(&cfg, false);
        assert!(report.found_solution);
        assert!(report.elapsed.as_secs_f64() < 10.0);
    }

    #[test]
    fn cached_known_tt6_sequence_verifies_fast() {
        let p = Problem::new(6);
        let x = PackedSeq::from_values(&[-1, -1, -1, -1, 1, -1]);
        let y = PackedSeq::from_values(&[-1, -1, -1, 1, -1, -1]);
        let z = PackedSeq::from_values(&[-1, -1, 1, -1, 1, 1]);
        let w = PackedSeq::from_values(&[-1, 1, 1, 1, -1]);
        assert!(verify_tt(p, &x, &y, &z, &w));
    }

    #[test]
    fn non_shortcut_backtrack_path_finds_xy_for_known_tt6_zw() {
        let p = Problem::new(6);
        let z = PackedSeq::from_values(&[-1, -1, 1, -1, 1, 1]);
        let w = PackedSeq::from_values(&[-1, 1, 1, 1, -1]);

        let mut zw = vec![0; p.n];
        for (s, slot) in zw.iter_mut().enumerate().skip(1) {
            let nz = z.autocorrelation(s);
            let nw = if s < p.m() { w.autocorrelation(s) } else { 0 };
            *slot = 2 * nz + 2 * nw;
        }
        let candidate = CandidateZW {
            z: z.clone(),
            w: w.clone(),
            zw_autocorr: zw,
        };
        let tuple = SumTuple {
            x: 4,
            y: 4,
            z: z.sum(),
            w: w.sum(),
        };

        let mut stats = SearchStats::default();
        let Some((x, y)) = backtrack_xy(p, tuple, &candidate, &mut stats) else {
            panic!("expected non-shortcut backtracking path to find an (X,Y) assignment");
        };
        assert!(verify_tt(p, &x, &y, &candidate.z, &candidate.w));
        assert!(stats.xy_nodes > 0);
    }

    #[test]
    fn stochastic_search_finds_tt8() {
        let p = Problem::new(8);
        let report = stochastic_search(p, false, 0);
        assert!(report.found_solution);
        assert!(report.elapsed.as_secs_f64() < 30.0);
    }
}
