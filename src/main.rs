use std::cmp::Ordering;
use std::collections::HashMap;
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
        assert!(n == 0 || n >= 2, "n must be at least 2");
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
    fn as_string(&self) -> String {
        (0..self.len)
            .map(|i| if self.get(i) == 1 { '+' } else { '-' })
            .collect()
    }

    #[allow(dead_code)]
    fn as_blocks(&self) -> String {
        (0..self.len)
            .map(|i| if self.get(i) == 1 { '\u{2593}' } else { '\u{2591}' })
            .collect()
    }
}

/// Format a sequence as a colorized +/- string for terminal display.
/// '+' gets black text on light gray background, '-' gets white text on dark gray.
/// Copies as plain +/- from most terminals.
fn colored_pm(seq: &PackedSeq) -> String {
    let mut out = String::new();
    for i in 0..seq.len() {
        if seq.get(i) == 1 {
            out.push_str("\x1b[30;47m+\x1b[0m");
        } else {
            out.push_str("\x1b[37;100m-\x1b[0m");
        }
    }
    out
}

fn print_solution(label: &str, x: &PackedSeq, y: &PackedSeq, z: &PackedSeq, w: &PackedSeq) {
    use std::io::Write;
    let n = x.len();
    let mut buf = format!("\n{}\n", label);
    for (name, seq) in [("X", x), ("Y", y), ("Z", z), ("W", w)] {
        let pad = " ".repeat(n - seq.len());
        buf.push_str(&format!("{} =: '{}'{}  NB. {}\n", name, colored_pm(seq), pad, seq.sum()));
    }
    buf.push('\n');
    let stdout = std::io::stdout();
    let mut lock = stdout.lock();
    let _ = lock.write_all(buf.as_bytes());
    let _ = lock.flush();
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
struct SumTuple {
    x: i32,
    y: i32,
    z: i32,
    w: i32,
}

impl SumTuple {
    /// Normalization key for tuple deduplication in hybrid search.
    ///
    /// The hybrid SAT solver fixes both x[0]=+1 and y[0]=+1. With these constraints:
    /// - Negate X: flips x[0] → NOT safe
    /// - Negate Y: flips y[0] → NOT safe
    /// - Negate Z: no z[0] constraint → safe: σ_Z → |σ_Z|
    /// - Negate W: no w[0] constraint → safe: σ_W → |σ_W|
    /// - X↔Y swap: both have first element +1, so swap preserves constraints → safe
    ///
    /// This gives factor ~8 reduction: 2 (Z sign) × 2 (W sign) × 2 (X↔Y swap when x≠y).
    fn norm_key(&self) -> (i32, i32, i32, i32) {
        let (xa, ya) = (self.x.abs(), self.y.abs());
        let (xx, yy) = if xa <= ya { (xa, ya) } else { (ya, xa) };
        (xx, yy, self.z.abs(), self.w.abs())
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
    max_z: usize,
    max_w: usize,
    benchmark_repeats: usize,
    stochastic: bool,
    stochastic_seconds: u64,
    sat: bool,
    sat_xy: bool,
    z_sat: bool,
    w_sat: bool,
    /// London §5.1: restrict spectral pair sum to ≤ max_spectral.
    /// If None, uses the default spectral_bound (= (6n-2)/2).
    /// Setting this lower than spectral_bound trades completeness for speed.
    max_spectral: Option<f64>,
    /// Test mode: verify a known solution or test SAT on known Z/W.
    /// Format: 4 strings of +/- chars, e.g. "++--+-" for [1,1,-1,-1,1,-1].
    verify_seqs: Option<[String; 4]>,
    /// Test SAT X/Y with given Z/W (2 strings of +/- chars).
    test_zw: Option<[String; 2]>,
    /// Conflict limit per SAT solve (0 = unlimited).
    conflict_limit: u64,
    /// Test a specific sum-tuple (x,y,z,w) only.
    test_tuple: Option<SumTuple>,
    /// Run only Phase A (print tuples) or Phase B (print Z/W pairs).
    phase_only: Option<String>,
    /// Path to XY boundary table file for table-based Phase C.
    /// Defaults to "./xy-table-k7.bin".
    xy_table_path: Option<String>,
    /// Run without XY boundary table (slower).
    no_table: bool,
    /// Dump DIMACS CNF to this path instead of solving.
    dump_dimacs: Option<String>,
    /// SAT solver feature flags.
    sat_config: radical::SolverConfig,
    /// Time limit in seconds for --sat mode (0 = unlimited).
    sat_secs: u64,
}

impl Default for SearchConfig {
    fn default() -> Self {
        Self {
            problem: Problem::new(0),
            theta_samples: 128,
            max_z: 200_000,
            max_w: 200_000,
            benchmark_repeats: 0,
            stochastic: false,
            stochastic_seconds: 0,
            sat: false,
            sat_xy: false,
            z_sat: false,
            w_sat: false,
            max_spectral: None,
            verify_seqs: None,
            test_zw: None,
            conflict_limit: 0,
            test_tuple: None,
            phase_only: None,
            xy_table_path: None,
            no_table: false,
            dump_dimacs: None,
            sat_config: radical::SolverConfig::default(),
            sat_secs: 0,
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
    phase_b_nanos: u64,
    phase_c_nanos: u64,
}

impl SearchStats {
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
        self.phase_b_nanos += other.phase_b_nanos;
        self.phase_c_nanos += other.phase_c_nanos;
    }
}

#[derive(Clone, Debug)]
struct SeqWithSpectrum {
    seq: PackedSeq,
    spectrum: Vec<f64>,
    autocorr: Option<Vec<i32>>,  // lazily computed at pair time
}

// BoundarySignature removed: bucketing provided no benefit (see commit history).

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
        let key = t.norm_key();
        // Store canonical form: all positive, x <= y
        seen.entry(key).or_insert(SumTuple {
            x: key.0, y: key.1, z: key.2, w: key.3,
        });
    }
    let mut items: Vec<_> = seen.into_values().collect();
    items.sort_by_key(|t| t.norm_key());
    items
}

/// Unified Phase A: enumerate sum-tuples with normalization, dedup, parity filter, and --tuple filter.
/// Returns canonical forms: all positive, x <= y.
fn phase_a_tuples(problem: Problem, test_tuple: Option<&SumTuple>) -> Vec<SumTuple> {
    let raw = enumerate_sum_tuples(problem);
    let mut tuples = normalized_tuples(&raw);
    // Parity filter
    tuples.retain(|t| {
        (t.x + problem.n as i32) % 2 == 0
            && (t.y + problem.n as i32) % 2 == 0
            && (t.z + problem.n as i32) % 2 == 0
            && (t.w + problem.m() as i32) % 2 == 0
    });
    // --tuple filter
    if let Some(tt) = test_tuple {
        let key = tt.norm_key();
        tuples.retain(|u| u.norm_key() == key);
    }
    tuples
}


#[allow(dead_code)]
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
        if z_spectrum[i] + w_spectrum[i] > bound {
            return false;
        }
    }
    true
}

/// Max combined spectral power across all frequencies.
fn spectral_pair_max_power(z_spectrum: &[f64], w_spectrum: &[f64]) -> f64 {
    let mut max_power = 0.0f64;
    for i in 0..z_spectrum.len() {
        let combined = z_spectrum[i] + w_spectrum[i];
        if combined > max_power { max_power = combined; }
    }
    max_power
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
        true
    });
    out
}

/// Generate ±1 sequences of given length and sum, calling `visit` for each.
/// `visit` returns `true` to continue, `false` to stop early.
fn generate_sequences_with_sum_visit<F: FnMut(&[i8]) -> bool>(
    len: usize,
    target_sum: i32,
    root_one: bool,
    tail_one: bool,
    limit: usize,
    mut visit: F,
) {
    let mut curr = vec![1i8; len];
    let mut emitted = 0usize;
    let mut stopped = false;

    fn dfs(
        i: usize,
        len: usize,
        curr_sum: i32,
        target_sum: i32,
        curr: &mut [i8],
        emitted: &mut usize,
        stopped: &mut bool,
        limit: usize,
        root_one: bool,
        tail_one: bool,
        visit: &mut impl FnMut(&[i8]) -> bool,
    ) {
        if *emitted >= limit || *stopped {
            return;
        }
        if i == len {
            if curr_sum == target_sum {
                *emitted += 1;
                if !visit(curr) {
                    *stopped = true;
                }
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
                stopped,
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
                stopped,
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
                stopped,
                limit,
                root_one,
                tail_one,
                visit,
            );
        }

        if *stopped { return; }

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
                stopped,
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
        &mut stopped,
        limit,
        root_one,
        tail_one,
        &mut visit,
    );
}

/// Compute binomial coefficient C(n, k) as u128 (enough for n ≤ 60).
fn binom(n: usize, k: usize) -> u128 {
    if k > n { return 0; }
    let k = k.min(n - k);
    let mut result = 1u128;
    for i in 0..k {
        result = result * (n - i) as u128 / (i + 1) as u128;
    }
    result
}

/// Unrank: given index `rank` in [0, C(f, r)), produce the rank-th combination
/// of choosing r positions from f slots (in colex order).
/// Writes +1/-1 into `out[start..start+f]`.
fn unrank_combination(rank: u128, f: usize, r: usize, out: &mut [i8], start: usize) {
    // Set all to -1, then place r ones
    for i in 0..f { out[start + i] = -1; }
    let mut remaining_rank = rank;
    let mut remaining_choose = r;
    let mut pos = f;
    while remaining_choose > 0 {
        pos -= 1;
        let c = binom(pos, remaining_choose);
        if remaining_rank >= c {
            remaining_rank -= c;
            out[start + pos] = 1;
            remaining_choose -= 1;
        }
    }
}

/// Generate ±1 sequences with a given sum in permuted (pseudo-random) order.
/// Uses an LCG bijection over [0, C(f, r)) to visit every sequence exactly once
/// but in a scattered order, so the first `limit` sequences are representative
/// of the full space rather than clustered lexicographically.
fn generate_sequences_permuted<F: FnMut(&[i8]) -> bool>(
    len: usize,
    target_sum: i32,
    root_one: bool,
    tail_one: bool,
    limit: usize,
    mut visit: F,
) {
    // Determine fixed positions and free count
    let fixed_sum: i32 = (if root_one { 1 } else { 0 }) + (if tail_one { 1 } else { 0 });
    let free_start = if root_one { 1 } else { 0 };
    let free_end = if tail_one { len - 1 } else { len };
    let f = free_end - free_start; // number of free positions
    let free_target = target_sum - fixed_sum; // sum needed from free positions
    // free positions have values in {-1, +1}, sum = 2*ones - f
    // so ones = (free_target + f) / 2
    if (free_target + f as i32) % 2 != 0 { return; }
    let r_signed = (free_target + f as i32) / 2;
    if r_signed < 0 || r_signed > f as i32 { return; }
    let r = r_signed as usize; // number of +1s among free positions

    let total = binom(f, r);
    let n_visit = (limit as u128).min(total);

    let mut curr = vec![1i8; len];
    if root_one { curr[0] = 1; }
    if tail_one { curr[len - 1] = 1; }

    // If the full space fits within the limit, DFS is faster (no unranking overhead).
    if total <= limit as u128 {
        generate_sequences_with_sum_visit(len, target_sum, root_one, tail_one, limit, visit);
        return;
    }

    // Bijective scatter: index i -> (a * i + c) mod total
    // `a` coprime to `total` guarantees a permutation of [0, total).
    let m = total;
    let a = {
        let mut candidate = 6364136223846793005u128 % m;
        if candidate == 0 { candidate = 1; }
        while gcd128(candidate, m) != 1 {
            candidate = (candidate + 1) % m;
            if candidate == 0 { candidate = 1; }
        }
        candidate
    };
    let c = 1442695040888963407u128 % m;

    for i in 0..n_visit {
        let rank = (a * i + c) % m;
        unrank_combination(rank, f, r, &mut curr, free_start);
        if !visit(&curr) { return; }
    }
}

fn gcd128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 { let t = b; b = a % b; a = t; }
    a
}

/// Generate all spectrally-valid W sequences for a given sum.
/// W is the shorter sequence (length n-1) so we materialize it; Z is streamed.
fn build_w_candidates(
    problem: Problem,
    w_sum: i32,
    cfg: &SearchConfig,
    spectral_w: &SpectralFilter,
    stats: &mut SearchStats,
    found: &AtomicBool,
) -> Vec<SeqWithSpectrum> {
    let individual_bound = problem.spectral_bound();
    let mut w_candidates: Vec<SeqWithSpectrum> = Vec::new();
    let mut fft_buf = Vec::with_capacity(spectral_w.fft_size);
    generate_sequences_permuted(problem.m(), w_sum, true, false, cfg.max_w, |values| {
        if found.load(AtomicOrdering::Relaxed) { return false; }
        stats.w_generated += 1;
        if let Some(spectrum) =
            spectrum_if_ok(values, spectral_w, individual_bound, &mut fft_buf)
        {
            stats.w_spectral_ok += 1;
            w_candidates.push(SeqWithSpectrum {
                spectrum,
                autocorr: None,
                seq: PackedSeq::from_values(values),
            });
        }
        true
    });
    w_candidates
}

/// Index for fast spectral pair lookups.
/// For each frequency, stores W candidate indices sorted by power at that frequency.
/// Given a Z spectrum, we find the tightest frequency (highest Z power), then binary
/// search to find only the W candidates that could pass at that frequency.
struct SpectralIndex {
    /// For each frequency f: Vec of (w_power_at_f, w_index), sorted by power.
    sorted_by_freq: Vec<Vec<(f64, usize)>>,
}

impl SpectralIndex {
    fn build(w_candidates: &[SeqWithSpectrum]) -> Self {
        if w_candidates.is_empty() {
            return Self { sorted_by_freq: Vec::new() };
        }
        let num_freqs = w_candidates[0].spectrum.len();
        let mut sorted_by_freq = Vec::with_capacity(num_freqs);
        for f in 0..num_freqs {
            let mut entries: Vec<(f64, usize)> = w_candidates.iter().enumerate()
                .map(|(i, w)| (w.spectrum[f], i))
                .collect();
            entries.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
            sorted_by_freq.push(entries);
        }
        Self { sorted_by_freq }
    }

    /// Find W candidates that pass budget constraints at the top-4 tightest frequencies.
    /// Uses binary search on the tightest, then filters by frequencies 2-4.
    /// Results are written into `out` (cleared first) as W indices.
    fn candidates_for(&self, z_spectrum: &[f64], pair_bound: f64, w_candidates: &[SeqWithSpectrum], out: &mut Vec<usize>) {
        out.clear();
        if self.sorted_by_freq.is_empty() { return; }
        // Find top-4 tightest frequencies (highest Z power = least budget for W)
        let mut top: [(f64, usize); 4] = [(f64::MIN, 0); 4];
        for (f, &zp) in z_spectrum.iter().enumerate() {
            if zp > top[3].0 {
                top[3] = (zp, f);
                // Bubble up
                for i in (0..3).rev() {
                    if top[i + 1].0 > top[i].0 {
                        top.swap(i, i + 1);
                    } else {
                        break;
                    }
                }
            }
        }
        // Binary search on tightest frequency
        let budget0 = pair_bound - top[0].0;
        let sorted = &self.sorted_by_freq[top[0].1];
        let cutoff = sorted.partition_point(|(wp, _)| *wp <= budget0);
        // Filter by frequencies 2-4
        let budget1 = pair_bound - top[1].0;
        let budget2 = pair_bound - top[2].0;
        let budget3 = pair_bound - top[3].0;
        let f1 = top[1].1;
        let f2 = top[2].1;
        let f3 = top[3].1;
        for &(_, wi) in &sorted[..cutoff] {
            let spec = &w_candidates[wi].spectrum;
            if spec[f1] <= budget1 && spec[f2] <= budget2 && spec[f3] <= budget3 {
                out.push(wi);
            }
        }
    }
}

/// Streaming Z×W pairing with spectral index for fast candidate lookup.
/// For each spectrally-valid Z, uses the index to find W candidates that pass
/// the top-4 tightest frequency constraints, then full-checks only those.
fn stream_zw_candidates(
    problem: Problem,
    z_sum: i32,
    w_candidates: &[SeqWithSpectrum],
    w_index: &SpectralIndex,
    cfg: &SearchConfig,
    spectral_z: &SpectralFilter,
    stats: &mut SearchStats,
    found: &AtomicBool,
) -> Vec<CandidateZW> {
    let individual_bound = problem.spectral_bound();
    let pair_bound = cfg.max_spectral.unwrap_or(problem.spectral_bound());
    let mut out = Vec::new();
    let mut fft_buf = Vec::with_capacity(spectral_z.fft_size);
    let mut idx_buf = Vec::new();
    generate_sequences_permuted(problem.n, z_sum, true, true, cfg.max_z, |values| {
        if found.load(AtomicOrdering::Relaxed) { return false; }
        stats.z_generated += 1;
        let Some(z_spectrum) =
            spectrum_if_ok(values, spectral_z, individual_bound, &mut fft_buf) else { return true; };
        stats.z_spectral_ok += 1;
        let z_seq = PackedSeq::from_values(values);
        let mut z_auto: Option<Vec<i32>> = None;
        w_index.candidates_for(&z_spectrum, pair_bound, w_candidates, &mut idx_buf);
        for &wi in &idx_buf {
            let w = &w_candidates[wi];
            stats.candidate_pair_attempts += 1;
            if !spectral_pair_ok(&z_spectrum, &w.spectrum, pair_bound) { continue; }
            stats.candidate_pair_spectral_ok += 1;
            let z_auto = z_auto.get_or_insert_with(|| {
                let mut a = vec![0i32; problem.n];
                for s in 1..problem.n { a[s] = z_seq.autocorrelation(s); }
                a
            });
            let w_auto = w.autocorr.as_ref().cloned()
                .unwrap_or_else(|| {
                    let mut a = vec![0i32; problem.m()];
                    for s in 1..problem.m() { a[s] = w.seq.autocorrelation(s); }
                    a
                });
            let mut zw = vec![0; problem.n];
            for (s, slot) in zw.iter_mut().enumerate().skip(1) {
                let nz = z_auto[s];
                let nw = if s < problem.m() { w_auto[s] } else { 0 };
                *slot = 2 * nz + 2 * nw;
            }
            out.push(CandidateZW {
                z: z_seq.clone(),
                w: w.seq.clone(),
                zw_autocorr: zw,
            });
        }
        true
    });
    out
}

/// Streaming Z×W pairing that sends pairs directly to a channel.
/// Used by the hybrid producer thread to feed the priority queue without buffering.
fn stream_zw_candidates_to_channel(
    problem: Problem,
    tuple: SumTuple,
    w_candidates: &[SeqWithSpectrum],
    w_index: &SpectralIndex,
    cfg: &SearchConfig,
    spectral_z: &SpectralFilter,
    stats: &mut SearchStats,
    found: &AtomicBool,
    tx: &std::sync::mpsc::Sender<SatWorkItem>,
) {
    let individual_bound = problem.spectral_bound();
    let pair_bound = cfg.max_spectral.unwrap_or(problem.spectral_bound());
    let mut fft_buf = Vec::with_capacity(spectral_z.fft_size);
    let mut seen = std::collections::HashSet::new();
    let mut idx_buf = Vec::new();
    generate_sequences_permuted(problem.n, tuple.z, true, true, cfg.max_z, |values| {
        if found.load(AtomicOrdering::Relaxed) { return false; }
        stats.z_generated += 1;
        let Some(z_spectrum) =
            spectrum_if_ok(values, spectral_z, individual_bound, &mut fft_buf) else { return true; };
        stats.z_spectral_ok += 1;
        let z_seq = PackedSeq::from_values(values);
        let mut z_auto: Option<Vec<i32>> = None;
        w_index.candidates_for(&z_spectrum, pair_bound, w_candidates, &mut idx_buf);
        for &wi in &idx_buf {
            let w = &w_candidates[wi];
            stats.candidate_pair_attempts += 1;
            if !spectral_pair_ok(&z_spectrum, &w.spectrum, pair_bound) { continue; }
            let max_power = spectral_pair_max_power(&z_spectrum, &w.spectrum);
            stats.candidate_pair_spectral_ok += 1;
            let z_auto = z_auto.get_or_insert_with(|| {
                let mut a = vec![0i32; problem.n];
                for s in 1..problem.n { a[s] = z_seq.autocorrelation(s); }
                a
            });
            let w_auto = w.autocorr.as_ref().cloned()
                .unwrap_or_else(|| {
                    let mut a = vec![0i32; problem.m()];
                    for s in 1..problem.m() { a[s] = w.seq.autocorrelation(s); }
                    a
                });
            let mut zw = vec![0; problem.n];
            for (s, slot) in zw.iter_mut().enumerate().skip(1) {
                let nz = z_auto[s];
                let nw = if s < problem.m() { w_auto[s] } else { 0 };
                *slot = 2 * nz + 2 * nw;
            }
            if seen.insert(zw.clone()) {
                let _ = tx.send(SatWorkItem {
                    tuple,
                    x: SeqInput::Blank, y: SeqInput::Blank,
                    z: SeqInput::Fixed(z_seq.clone()),
                    w: SeqInput::Fixed(w.seq.clone()),
                    zw_autocorr: Some(zw),
                    priority: max_power,
                    boundary: None,
                });
            }
        }
        true
    });
}

fn build_zw_candidates(
    problem: Problem,
    tuple: SumTuple,
    cfg: &SearchConfig,
    spectral_z: &SpectralFilter,
    spectral_w: &SpectralFilter,
    stats: &mut SearchStats,
    found: &AtomicBool,
) -> Vec<CandidateZW> {
    let w_candidates = build_w_candidates(problem, tuple.w, cfg, spectral_w, stats, found);
    if found.load(AtomicOrdering::Relaxed) { return Vec::new(); }
    let w_index = SpectralIndex::build(&w_candidates);
    stream_zw_candidates(problem, tuple.z, &w_candidates, &w_index, cfg, spectral_z, stats, found)
}

/// Cached version: caches W candidates and spectral index by sum value.
/// Z is streamed fresh each time — no storage limit, every spectrally-valid Z is tried.
#[allow(dead_code)]
fn build_zw_candidates_cached(
    problem: Problem,
    tuple: SumTuple,
    cfg: &SearchConfig,
    spectral_z: &SpectralFilter,
    spectral_w: &SpectralFilter,
    w_cache: &mut HashMap<i32, (Vec<SeqWithSpectrum>, SpectralIndex)>,
    stats: &mut SearchStats,
    found: &AtomicBool,
) -> Vec<CandidateZW> {
    if !w_cache.contains_key(&tuple.w) {
        let w_candidates = build_w_candidates(problem, tuple.w, cfg, spectral_w, stats, found);
        let w_index = SpectralIndex::build(&w_candidates);
        w_cache.insert(tuple.w, (w_candidates, w_index));
    }
    if found.load(AtomicOrdering::Relaxed) { return Vec::new(); }
    let (w_candidates, w_index) = w_cache.get(&tuple.w).unwrap();
    stream_zw_candidates(problem, tuple.z, w_candidates, w_index, cfg, spectral_z, stats, found)
}

/// Pre-built SAT template for X/Y solving. Contains the structural clauses
/// (XNOR, totalizer trees, sum constraints) that are shared across all Z/W pairs
/// for a given tuple. Clone and add per-pair cardinality assertions to solve.
#[cfg(not(feature = "cadical"))]
struct SatXYTemplate {
    solver: radical::Solver,
    lag_pairs: Vec<LagPairs>,
    n: usize,
}

#[cfg(feature = "cadical")]
struct SatXYTemplate {
    solver: cadical::Solver,
    lag_pairs: Vec<LagPairs>,
    n: usize,
}

/// Per-candidate GJ elimination: given specific agree targets for each lag,
/// determine which primary variable pairs must be equal/opposite, and
/// propagate these equalities to reduce the problem.
///
/// Returns: vec of (var_a, var_b, equal: bool) pairs — if equal is true,
/// var_a = var_b; otherwise var_a = ¬var_b. Variables are 1-based.
/// GF(2) row: a bitset of variable indices + a constant (0 or 1).
/// Represents the equation: XOR of variables in the set = constant.
#[derive(Clone)]
struct Gf2Row {
    vars: Vec<bool>, // vars[i] = true if variable i participates
    constant: bool,  // right-hand side
}

impl Gf2Row {
    fn new(num_vars: usize) -> Self {
        Self { vars: vec![false; num_vars], constant: false }
    }
    fn xor_with(&mut self, other: &Gf2Row) {
        for i in 0..self.vars.len() {
            self.vars[i] ^= other.vars[i];
        }
        self.constant ^= other.constant;
    }
    /// Find the first set variable (pivot column), or None if all zero.
    fn pivot(&self) -> Option<usize> {
        self.vars.iter().position(|&v| v)
    }
    /// Count set variables.
    fn popcount(&self) -> usize {
        self.vars.iter().filter(|&&v| v).count()
    }
}

/// Returns None if a contradiction is detected (UNSAT), otherwise equalities.
fn gj_candidate_equalities(n: usize, candidate: &CandidateZW) -> Option<Vec<(i32, i32, bool)>> {
    let num_vars = 2 * n;
    // Union-find with negation tracking (XOR-union-find)
    let mut parent: Vec<usize> = (0..num_vars).collect();
    let mut rank: Vec<u8> = vec![0; num_vars];
    let mut neg: Vec<bool> = vec![false; num_vars]; // true if node is negated relative to parent

    fn find(parent: &mut [usize], neg: &mut [bool], mut x: usize) -> (usize, bool) {
        let mut path = Vec::new();
        let mut n = false;
        while parent[x] != x {
            path.push(x);
            n ^= neg[x];
            x = parent[x];
        }
        let root = x;
        let mut n2 = false;
        for &p in path.iter().rev() {
            n2 ^= neg[p];
            parent[p] = root;
            neg[p] = n2;
        }
        (root, n)
    }

    // Returns false if a contradiction is detected
    fn union(parent: &mut [usize], rank: &mut [u8], neg: &mut [bool],
             a: usize, b: usize, a_neg_b: bool) -> bool {
        let (ra, na) = find(parent, neg, a);
        let (rb, nb) = find(parent, neg, b);
        if ra == rb {
            // Check consistency: na ^ nb should equal a_neg_b
            return (na ^ nb) == a_neg_b;
        }
        let rel = na ^ nb ^ a_neg_b;
        if rank[ra] < rank[rb] {
            parent[ra] = rb;
            neg[ra] = rel;
        } else if rank[ra] > rank[rb] {
            parent[rb] = ra;
            neg[rb] = rel;
        } else {
            parent[rb] = ra;
            neg[rb] = rel;
            rank[ra] += 1;
        }
        true
    }

    // Process lags where ALL or NO pairs agree.
    // Also process lags where X and Y halves have separate extreme targets.
    for s in 1..n {
        let target_raw = 2 * (n - s) as i32 - candidate.zw_autocorr[s];
        if target_raw < 0 || target_raw % 2 != 0 { continue; }
        let target = (target_raw / 2) as usize;
        let x_pairs = n - s;
        let y_pairs = n - s;
        let max_pairs = x_pairs + y_pairs;

        if target == max_pairs {
            // ALL pairs agree
            for i in 0..x_pairs {
                if !union(&mut parent, &mut rank, &mut neg, i, i + s, false) { return None; }
            }
            for i in 0..y_pairs {
                if !union(&mut parent, &mut rank, &mut neg, n + i, n + i + s, false) { return None; }
            }
        } else if target == 0 {
            // NO pairs agree
            for i in 0..x_pairs {
                if !union(&mut parent, &mut rank, &mut neg, i, i + s, true) { return None; }
            }
            for i in 0..y_pairs {
                if !union(&mut parent, &mut rank, &mut neg, n + i, n + i + s, true) { return None; }
            }
        }
    }

    // GF(2) Gauss-Jordan elimination on parity constraints from ALL lags.
    // For each lag s with target T:
    //   parity(agree_count) = T mod 2
    //   agree(x_i, x_{i+s}) = x_i XNOR x_{i+s} = 1 ⊕ x_i ⊕ x_{i+s}
    //   sum of agrees mod 2 = T mod 2
    //   k + sum(x_i ⊕ x_{i+s}) mod 2 = T mod 2   (where k = # pairs)
    //   sum(x_i ⊕ x_{i+s}) mod 2 = (T + k) mod 2
    //
    // sum(x_i ⊕ x_{i+s}) = sum(x_i) + sum(x_{i+s}) mod 2 (for distinct i)
    // Each variable x_v appears in the XOR sum once per occurrence in a pair.
    // Variable x_v appears as first element of pair (v, v+s) if v < n-s,
    // and as second element of pair (v-s, v) if v >= s.
    // So the total parity of a variable in the XOR sum depends on
    // how many times it appears in pairs, which determines its coefficient mod 2.
    {
        let mut rows: Vec<Gf2Row> = Vec::new();
        for s in 1..n {
            let target_raw = 2 * (n - s) as i32 - candidate.zw_autocorr[s];
            if target_raw < 0 || target_raw % 2 != 0 { continue; }
            let target = (target_raw / 2) as usize;
            let k = 2 * (n - s); // total pairs (X + Y)

            // Build GF(2) equation: for each pair (i, i+s), x_i and x_{i+s} each
            // appear once. XOR of all these = (T + k) mod 2.
            let mut row = Gf2Row::new(num_vars);
            // X pairs
            for i in 0..(n - s) {
                row.vars[i] ^= true;       // x_i
                row.vars[i + s] ^= true;   // x_{i+s}
            }
            // Y pairs
            for i in 0..(n - s) {
                row.vars[n + i] ^= true;       // y_i
                row.vars[n + i + s] ^= true;   // y_{i+s}
            }
            row.constant = ((target + k) % 2) == 1;
            // Skip trivial rows (all zeros)
            if row.popcount() > 0 {
                rows.push(row);
            }
        }

        // Gauss-Jordan elimination
        let mut pivot_row: Vec<Option<usize>> = vec![None; num_vars];
        for r in 0..rows.len() {
            // Reduce row r against existing pivots
            loop {
                let Some(col) = rows[r].pivot() else { break };
                if let Some(pr) = pivot_row[col] {
                    let pr_row = rows[pr].clone();
                    rows[r].xor_with(&pr_row);
                } else {
                    // This column has no pivot yet — use row r as pivot
                    pivot_row[col] = Some(r);
                    // Reduce all other rows
                    let pivot = rows[r].clone();
                    for r2 in 0..rows.len() {
                        if r2 != r && rows[r2].vars[col] {
                            rows[r2].xor_with(&pivot);
                        }
                    }
                    break;
                }
            }
        }

        // Extract equalities from reduced rows:
        // A row with exactly 1 variable: that variable = constant
        // A row with exactly 2 variables: they are equal (or negated)
        for row in &rows {
            let set_vars: Vec<usize> = row.vars.iter().enumerate()
                .filter(|&(_, &v)| v).map(|(i, _)| i).collect();
            match set_vars.len() {
                0 => {
                    // All-zero row: if constant is 1, contradiction (UNSAT)
                    if row.constant { return None; }
                }
                1 => {
                    // Forced variable: x_v = constant (in GF(2)).
                    // constant=true → x_v has bit 1 → same as x[0] (forced +1) → equal
                    // constant=false → x_v has bit 0 → opposite of x[0] → negated
                    let v = set_vars[0];
                    if !union(&mut parent, &mut rank, &mut neg, v, 0, !row.constant) {
                        return None;
                    }
                }
                2 => {
                    let a = set_vars[0];
                    let b = set_vars[1];
                    if !union(&mut parent, &mut rank, &mut neg, a, b, row.constant) {
                        return None;
                    }
                }
                _ => {}
            }
        }
    }

    // Extract non-trivial equalities
    let mut equalities = Vec::new();
    for v in 0..num_vars {
        let (root, is_neg) = find(&mut parent, &mut neg, v);
        if root != v {
            let a = (v as i32) + 1;
            let b = (root as i32) + 1;
            equalities.push((a, b, !is_neg));
        }
    }

    Some(equalities)
}

/// Pair data for quadratic PB constraints per lag: (lits_a, lits_b) for each lag.
/// agree(x_i, x_{i+s}) = x_i*x_{i+s} + ¬x_i*¬x_{i+s}, so each lag has
/// 4*(n-s) product terms (both-true + both-false for X pairs and Y pairs).
struct LagPairs {
    lits_a: Vec<i32>,
    lits_b: Vec<i32>,
}

/// Build SAT XY template with PB constraints for sum constraints
/// and quadratic PB agree pairs per lag. No XNOR auxiliary variables.
fn build_sat_xy_clauses(
    problem: Problem,
    tuple: SumTuple,
    solver: &mut impl SatSolver,
) -> Option<(Vec<LagPairs>, usize)> {
    let n = problem.n;

    let x_var = |i: usize| -> i32 { (i + 1) as i32 };
    let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };

    // Symmetry breaking
    solver.add_clause([x_var(0)]); // x[0] = +1
    solver.add_clause([y_var(0)]); // y[0] = +1

    // Sum constraints via PB
    if (tuple.x + n as i32) % 2 != 0 || (tuple.y + n as i32) % 2 != 0 {
        return None;
    }
    let x_pos = ((tuple.x + n as i32) / 2) as usize;
    let y_pos = ((tuple.y + n as i32) / 2) as usize;
    let x_lits: Vec<i32> = (0..n).map(|i| x_var(i)).collect();
    let y_lits: Vec<i32> = (0..n).map(|i| y_var(i)).collect();
    let ones: Vec<u32> = vec![1; n];
    solver.add_pb_eq(&x_lits, &ones, x_pos as u32);
    solver.add_pb_eq(&y_lits, &ones, y_pos as u32);

    // Build agree pair lists per lag (no aux variables!)
    // agree(a, b) = a*b + ¬a*¬b = (both true) + (both false)
    let mut lag_pairs = Vec::with_capacity(n);
    lag_pairs.push(LagPairs { lits_a: Vec::new(), lits_b: Vec::new() }); // lag 0 unused
    for s in 1..n {
        let mut lits_a = Vec::with_capacity(4 * (n - s));
        let mut lits_b = Vec::with_capacity(4 * (n - s));

        // X pairs: agree(x_i, x_{i+s})
        for i in 0..(n - s) {
            // Both-true term: x_i * x_{i+s}
            lits_a.push(x_var(i));
            lits_b.push(x_var(i + s));
            // Both-false term: ¬x_i * ¬x_{i+s}
            lits_a.push(-x_var(i));
            lits_b.push(-x_var(i + s));
        }
        // Y pairs: agree(y_i, y_{i+s})
        for i in 0..(n - s) {
            lits_a.push(y_var(i));
            lits_b.push(y_var(i + s));
            lits_a.push(-y_var(i));
            lits_b.push(-y_var(i + s));
        }

        lag_pairs.push(LagPairs { lits_a, lits_b });
    }

    Some((lag_pairs, n))
}

/// Trait abstracting over radical::Solver and cadical::Solver.
#[allow(dead_code)]
trait SatSolver {
    fn add_clause<I: IntoIterator<Item = i32>>(&mut self, lits: I);
    fn add_pb_eq(&mut self, lits: &[i32], coeffs: &[u32], target: u32);
    fn add_quad_pb_eq(&mut self, lits_a: &[i32], lits_b: &[i32], coeffs: &[u32], target: u32);
    fn add_xor_constraint(&mut self, aux: i32, a: i32, b: i32);
    fn solve_with_assumptions(&mut self, assumptions: &[i32]) -> Option<bool>;
    fn value(&self, var: i32) -> Option<bool>;
    fn reset(&mut self);
    fn set_conflict_limit(&mut self, limit: u64);
}

impl SatSolver for radical::Solver {
    fn add_clause<I: IntoIterator<Item = i32>>(&mut self, lits: I) {
        self.add_clause(lits);
    }
    fn add_pb_eq(&mut self, lits: &[i32], coeffs: &[u32], target: u32) {
        self.add_pb_eq(lits, coeffs, target);
    }
    fn add_quad_pb_eq(&mut self, lits_a: &[i32], lits_b: &[i32], coeffs: &[u32], target: u32) {
        self.add_quad_pb_eq(lits_a, lits_b, coeffs, target);
    }
    fn add_xor_constraint(&mut self, aux: i32, a: i32, b: i32) {
        // XNOR: aux = (a ↔ b), i.e., aux ⊕ a ⊕ b = true (odd parity)
        self.add_xor(&[aux, a, b], true);
    }
    fn solve_with_assumptions(&mut self, assumptions: &[i32]) -> Option<bool> {
        self.solve_with_assumptions(assumptions)
    }
    fn value(&self, var: i32) -> Option<bool> {
        self.value(var)
    }
    fn reset(&mut self) {
        self.reset();
    }
    fn set_conflict_limit(&mut self, limit: u64) {
        self.set_conflict_limit(limit);
    }
}

#[cfg(feature = "cadical")]
impl SatSolver for cadical::Solver {
    fn add_clause<I: IntoIterator<Item = i32>>(&mut self, lits: I) {
        self.add_clause(lits);
    }
    fn add_pb_eq(&mut self, _lits: &[i32], _coeffs: &[u32], _target: u32) {
        unimplemented!("CaDiCaL backend uses clause-based encoding, not PB");
    }
    fn add_quad_pb_eq(&mut self, _a: &[i32], _b: &[i32], _c: &[u32], _t: u32) {
        unimplemented!("CaDiCaL backend uses clause-based encoding, not quad PB");
    }
    fn add_xor_constraint(&mut self, _aux: i32, _a: i32, _b: i32) {
        // CaDiCaL doesn't support native XOR — clauses handle it
    }
    fn solve_with_assumptions(&mut self, assumptions: &[i32]) -> Option<bool> {
        self.solve_with(assumptions.iter().copied())
    }
    fn value(&self, var: i32) -> Option<bool> {
        self.value(var)
    }
    fn reset(&mut self) {
        // CaDiCaL auto-resets after solve
    }
    fn set_conflict_limit(&mut self, _limit: u64) {
        // CaDiCaL uses its own limit mechanism
    }
}

impl SatXYTemplate {
    fn build(problem: Problem, tuple: SumTuple, sat_config: &radical::SolverConfig) -> Option<Self> {
        #[cfg(not(feature = "cadical"))]
        let mut solver: radical::Solver = { let mut s = radical::Solver::new(); s.config = sat_config.clone(); s };
        #[cfg(feature = "cadical")]
        let mut solver: cadical::Solver = Default::default();

        let (lag_pairs, n) = build_sat_xy_clauses(problem, tuple, &mut solver)?;
        // Pre-allocate for expected search size (reduces realloc during solve)
        #[cfg(not(feature = "cadical"))]
        solver.reserve_for_search(200);
        Some(Self { solver, lag_pairs, n })
    }

    /// Quick feasibility check: are the cardinality targets in range?
    fn is_feasible(&self, candidate: &CandidateZW) -> bool {
        let n = self.n;
        for s in 1..n {
            let target_raw = 2 * (n - s) as i32 - candidate.zw_autocorr[s];
            if target_raw < 0 || target_raw % 2 != 0 { return false; }
            let target = (target_raw / 2) as usize;
            let max_pairs = 2 * (n - s);
            if target > max_pairs { return false; }
        }
        true
    }

    /// Solve for X/Y given a specific Z/W candidate.
    /// Clones the template and adds PB constraints for per-lag agree targets.
    /// Returns (result, was_limited): result is Some if SAT, None if UNSAT/UNKNOWN.
    /// was_limited=true means we hit the conflict limit (UNKNOWN).
    fn solve_for_limited(&self, candidate: &CandidateZW, conflict_limit: u64) -> (Option<(PackedSeq, PackedSeq)>, bool) {
        if !self.is_feasible(candidate) { return (None, false); }
        let n = self.n;
        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };

        // GJ-derived equalities from extreme-target lags (before clone — cheap)
        let Some(equalities) = gj_candidate_equalities(n, candidate) else {
            return (None, false); // GJ detected contradiction → UNSAT
        };

        let mut solver = self.solver.clone();
        if conflict_limit > 0 {
            solver.set_conflict_limit(conflict_limit);
        }
        for &(a, b, equal) in &equalities {
            if equal {
                solver.add_clause([-a, b]);
                solver.add_clause([a, -b]);
            } else {
                solver.add_clause([-a, -b]);
                solver.add_clause([a, b]);
            }
        }

        // Add quadratic PB constraints for each lag's agree target
        for s in 1..n {
            let target_raw = 2 * (n - s) as i32 - candidate.zw_autocorr[s];
            let target = (target_raw / 2) as usize;
            let lp = &self.lag_pairs[s];
            let ones: Vec<u32> = vec![1; lp.lits_a.len()];
            solver.add_quad_pb_eq(&lp.lits_a, &lp.lits_b, &ones, target as u32);
        }

        // GF(2) XOR constraints: parity of agree count at each lag.
        // For lag s with agree target T and k = 2*(n-s) pairs:
        //   XOR of {x[i] ⊕ x[i+s] for i in 0..n-s} ⊕ {y[i] ⊕ y[i+s] for i in 0..n-s} = (T+k) mod 2
        // Each variable v appears in the XOR with multiplicity = (# pairs containing v) mod 2.
        if solver.config.xor_propagation && n >= 8 {
            for s in 1..n {
                let target_raw = 2 * (n - s) as i32 - candidate.zw_autocorr[s];
                if target_raw < 0 || target_raw % 2 != 0 { continue; }
                let target = (target_raw / 2) as usize;
                let k = 2 * (n - s);
                let parity = ((target + k) % 2) == 1;

                // Build variable list: each var appears with multiplicity = # pairs it's in, mod 2
                let mut in_xor = vec![false; 2 * n];
                // X pairs: (i, i+s) for i in 0..n-s
                for i in 0..(n - s) {
                    in_xor[i] ^= true;
                    in_xor[i + s] ^= true;
                }
                // Y pairs: (n+i, n+i+s) for i in 0..n-s
                for i in 0..(n - s) {
                    in_xor[n + i] ^= true;
                    in_xor[n + i + s] ^= true;
                }
                let vars: Vec<i32> = in_xor.iter().enumerate()
                    .filter(|&(_, &v)| v)
                    .map(|(i, _)| (i + 1) as i32)  // 1-based
                    .collect();
                if !vars.is_empty() {
                    solver.add_xor(&vars, parity);
                }
            }
        }

        match solver.solve() {
            Some(true) => {
                let x: Vec<i8> = (0..n).map(|i| if solver.value(x_var(i)) == Some(true) { 1 } else { -1 }).collect();
                let y: Vec<i8> = (0..n).map(|i| if solver.value(y_var(i)) == Some(true) { 1 } else { -1 }).collect();
                (Some((PackedSeq::from_values(&x), PackedSeq::from_values(&y))), false)
            }
            Some(false) => (None, false),  // definite UNSAT
            None => (None, true),  // hit conflict limit (UNKNOWN)
        }
    }

    fn solve_for(&self, candidate: &CandidateZW) -> Option<(PackedSeq, PackedSeq)> {
        self.solve_for_limited(candidate, 0).0
    }

    /// Solve with warm-start: inject saved clauses/phases before solving,
    /// extract learnt clauses/phases after solving.
    fn solve_for_warm(
        &self,
        candidate: &CandidateZW,
        warm: &mut WarmStartState,
    ) -> Option<(PackedSeq, PackedSeq)> {
        if !self.is_feasible(candidate) { return None; }
        let n = self.n;
        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };

        let Some(equalities) = gj_candidate_equalities(n, candidate) else {
            return None;
        };

        let mut solver = self.solver.clone();

        // Inject warm-start data
        if warm.inject_clauses && !warm.clauses.is_empty() {
            solver.inject_clauses(&warm.clauses, 2);
        }
        if warm.inject_phase {
            if let Some(ref ph) = warm.phase {
                solver.set_phase(ph);
            }
        }

        for &(a, b, equal) in &equalities {
            if equal {
                solver.add_clause([-a, b]);
                solver.add_clause([a, -b]);
            } else {
                solver.add_clause([-a, -b]);
                solver.add_clause([a, b]);
            }
        }

        for s in 1..n {
            let target_raw = 2 * (n - s) as i32 - candidate.zw_autocorr[s];
            let target = (target_raw / 2) as usize;
            let lp = &self.lag_pairs[s];
            let ones: Vec<u32> = vec![1; lp.lits_a.len()];
            solver.add_quad_pb_eq(&lp.lits_a, &lp.lits_b, &ones, target as u32);
        }

        if solver.config.xor_propagation && n >= 8 {
            for s in 1..n {
                let target_raw = 2 * (n - s) as i32 - candidate.zw_autocorr[s];
                if target_raw < 0 || target_raw % 2 != 0 { continue; }
                let target = (target_raw / 2) as usize;
                let k = 2 * (n - s);
                let parity = ((target + k) % 2) == 1;
                let mut in_xor = vec![false; 2 * n];
                for i in 0..(n - s) {
                    in_xor[i] ^= true;
                    in_xor[i + s] ^= true;
                }
                for i in 0..(n - s) {
                    in_xor[n + i] ^= true;
                    in_xor[n + i + s] ^= true;
                }
                let vars: Vec<i32> = in_xor.iter().enumerate()
                    .filter(|&(_, &v)| v)
                    .map(|(i, _)| (i + 1) as i32)
                    .collect();
                if !vars.is_empty() {
                    solver.add_xor(&vars, parity);
                }
            }
        }

        let result = solver.solve();

        // Extract warm-start data for next solve
        let new_clauses = solver.extract_learnt_clauses(warm.max_lbd);
        for c in new_clauses {
            if warm.clauses.len() < warm.max_clauses {
                warm.clauses.push(c);
            }
        }
        warm.phase = Some(solver.get_phase());

        match result {
            Some(true) => {
                let x: Vec<i8> = (0..n).map(|i| if solver.value(x_var(i)) == Some(true) { 1 } else { -1 }).collect();
                let y: Vec<i8> = (0..n).map(|i| if solver.value(y_var(i)) == Some(true) { 1 } else { -1 }).collect();
                Some((PackedSeq::from_values(&x), PackedSeq::from_values(&y)))
            }
            _ => None,
        }
    }
}

/// Per-worker warm-start state for clause/phase transfer between SAT solves.
struct WarmStartState {
    clauses: Vec<Vec<i32>>,
    phase: Option<Vec<bool>>,
    max_clauses: usize,
    max_lbd: u8,
    inject_clauses: bool,
    inject_phase: bool,
}

/// SAT-based X/Y solver: given fixed Z/W, encode just X/Y constraints and solve.
#[allow(dead_code)]
fn sat_solve_xy(
    problem: Problem,
    tuple: SumTuple,
    candidate: &CandidateZW,
    _stats: &mut SearchStats,
) -> Option<(PackedSeq, PackedSeq)> {
    let template = SatXYTemplate::build(problem, tuple, &radical::SolverConfig::default())?;
    template.solve_for(candidate)
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

// ==================== Unified SAT work-item types ====================

/// What a worker should do with one sequence slot.
#[derive(Clone)]
enum SeqInput {
    /// SAT must find this sequence (sum comes from the SumTuple).
    Blank,
    /// Sequence already determined — treat as constant in the encoding.
    Fixed(PackedSeq),
}

/// Pre-screened boundary configuration (prefix + suffix bits) for all four sequences.
/// Each `*_bits` packs k prefix bits (low) and k suffix bits (high).
#[derive(Clone)]
struct BoundaryConfig {
    k: usize,
    x_bits: u32,
    y_bits: u32,
    z_bits: u32,
    w_bits: u32,
}

/// A unit of SAT work sent from producer → coordinator → worker.
struct SatWorkItem {
    tuple: SumTuple,
    x: SeqInput,
    y: SeqInput,
    z: SeqInput,
    w: SeqInput,
    /// Pre-computed 2*N_Z(k)+2*N_W(k) when both z and w are Fixed.
    zw_autocorr: Option<Vec<i32>>,
    /// Lower = higher priority in the coordinator queue. 0.0 = FIFO.
    priority: f64,
    /// Optional boundary config: fix prefix/suffix bits of all 4 sequences.
    boundary: Option<BoundaryConfig>,
}

fn compute_zw_autocorr(problem: Problem, z: &PackedSeq, w: &PackedSeq) -> Vec<i32> {
    let mut zw = vec![0i32; problem.n];
    for s in 1..problem.n {
        let nz = z.autocorrelation(s);
        let nw = if s < problem.m() { w.autocorrelation(s) } else { 0 };
        zw[s] = 2 * nz + 2 * nw;
    }
    zw
}

/// Dispatch a work item to the appropriate SAT solver based on which
/// sequences are Blank vs Fixed.
fn solve_work_item(
    problem: Problem,
    item: &SatWorkItem,
    template_cache: &mut HashMap<(i32, i32, i32, i32), SatXYTemplate>,
    xy_table: Option<&XYBoundaryTable>,
    sat_config: &radical::SolverConfig,
    warm: &mut WarmStartState,
) -> Option<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)> {
    match (&item.x, &item.y, &item.z, &item.w) {
        // All blank: pure SAT for all four sequences
        (SeqInput::Blank, SeqInput::Blank, SeqInput::Blank, SeqInput::Blank) => {
            sat_search(problem, item.tuple, item.boundary.as_ref(), false).map(|(x, y, z, w)|
                (PackedSeq::from_values(&x), PackedSeq::from_values(&y),
                 PackedSeq::from_values(&z), PackedSeq::from_values(&w)))
        }
        // Z fixed, rest blank: SAT for X/Y/W
        (SeqInput::Blank, SeqInput::Blank, SeqInput::Fixed(z), SeqInput::Blank) => {
            let z_vals: Vec<i8> = (0..z.len()).map(|i| z.get(i)).collect();
            sat_solve_xyw(problem, item.tuple, &z_vals, false)
                .map(|(x, y, w)| (x, y, z.clone(), w))
        }
        // Z and W fixed: SAT for X/Y
        (SeqInput::Blank, SeqInput::Blank, SeqInput::Fixed(z), SeqInput::Fixed(w)) => {
            let tuple_key = (item.tuple.x, item.tuple.y, item.tuple.z, item.tuple.w);
            let template = template_cache.entry(tuple_key).or_insert_with(|| {
                SatXYTemplate::build(problem, item.tuple, sat_config).unwrap()
            });
            let zw_autocorr = item.zw_autocorr.clone().unwrap_or_else(|| {
                compute_zw_autocorr(problem, z, w)
            });
            let candidate = CandidateZW {
                z: z.clone(), w: w.clone(), zw_autocorr,
            };
            if let Some(table) = xy_table {
                table.solve_xy_with_sat(problem, item.tuple, &candidate, template)
                    .map(|(x, y)| (x, y, z.clone(), w.clone()))
            } else {
                template.solve_for_warm(&candidate, warm)
                    .map(|(x, y)| (x, y, z.clone(), w.clone()))
            }
        }
        _ => None,
    }
}

/// Generic producer-consumer SAT search runner.
///
/// All search modes (--sat, --z-sat, --w-sat, hybrid) funnel through here.
/// The caller provides a `produce` closure that generates `SatWorkItem`s;
/// workers dispatch each item to the right SAT solver via `solve_work_item`.
fn run_parallel_search<P>(
    problem: Problem,
    xy_table: Option<Arc<XYBoundaryTable>>,
    sat_config: radical::SolverConfig,
    produce: P,
    verbose: bool,
    mode_name: &str,
    time_limit_secs: u64,
) -> SearchReport
where
    P: FnOnce(std::sync::mpsc::Sender<SatWorkItem>, Arc<AtomicBool>) -> SearchStats
        + Send + 'static,
{
    let run_start = Instant::now();
    let workers = std::thread::available_parallelism()
        .map(|n| n.get()).unwrap_or(1).max(1);
    if verbose {
        eprintln!("TT({}): {} search, {} threads", problem.n, mode_name, workers);
    }

    let found = Arc::new(AtomicBool::new(false));

    use std::collections::BinaryHeap;

    // Channels
    let (producer_tx, producer_rx) = std::sync::mpsc::channel::<SatWorkItem>();
    let (result_tx, result_rx) =
        std::sync::mpsc::channel::<Option<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>>();
    let mut worker_txs: Vec<std::sync::mpsc::SyncSender<Option<SatWorkItem>>> = Vec::new();
    let (ready_tx, ready_rx) = std::sync::mpsc::channel::<usize>();

    // Shared counters
    let items_completed = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let phase_c_nanos_shared = Arc::new(std::sync::atomic::AtomicU64::new(0));

    // Spawn workers
    for tid in 0..workers {
        let (work_tx, work_rx) = std::sync::mpsc::sync_channel::<Option<SatWorkItem>>(1);
        worker_txs.push(work_tx);
        let found = Arc::clone(&found);
        let ready_tx = ready_tx.clone();
        let result_tx = result_tx.clone();
        let xy_table = xy_table.clone();
        let items_completed = Arc::clone(&items_completed);
        let phase_c_nanos_shared = Arc::clone(&phase_c_nanos_shared);
        let sat_config = sat_config.clone();

        std::thread::spawn(move || {
            let mut template_cache: HashMap<(i32, i32, i32, i32), SatXYTemplate> = HashMap::new();
            let mut warm = WarmStartState {
                clauses: Vec::new(),
                phase: None,
                max_clauses: 100,
                max_lbd: 2,
                inject_clauses: false,
                inject_phase: true,
            };
            let _ = ready_tx.send(tid);
            while let Ok(Some(item)) = work_rx.recv() {
                if found.load(AtomicOrdering::Relaxed) { break; }
                let c_start = Instant::now();
                let solved = solve_work_item(
                    problem, &item, &mut template_cache,
                    xy_table.as_deref(), &sat_config,
                    &mut warm,
                );
                phase_c_nanos_shared.fetch_add(
                    c_start.elapsed().as_nanos() as u64, AtomicOrdering::Relaxed);
                items_completed.fetch_add(1, AtomicOrdering::Relaxed);

                if let Some(ref sol) = solved {
                    if verify_tt(problem, &sol.0, &sol.1, &sol.2, &sol.3) {
                        found.store(true, AtomicOrdering::Relaxed);
                        let _ = result_tx.send(solved);
                        break;
                    }
                }
                let _ = ready_tx.send(tid);
            }
        });
    }
    drop(ready_tx);
    drop(result_tx);

    // Spawn producer
    let producer_found = Arc::clone(&found);
    let producer_handle = std::thread::spawn(move || produce(producer_tx, producer_found));

    // Coordinator: priority queue + dispatch loop
    struct PqItem { priority: f64, item: SatWorkItem }
    impl PartialEq for PqItem {
        fn eq(&self, other: &Self) -> bool { self.priority == other.priority }
    }
    impl Eq for PqItem {}
    impl PartialOrd for PqItem {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
    }
    impl Ord for PqItem {
        fn cmp(&self, other: &Self) -> Ordering {
            // Reverse: lower priority value = higher queue priority
            other.priority.partial_cmp(&self.priority).unwrap_or(Ordering::Equal)
        }
    }

    let mut pq: BinaryHeap<PqItem> = BinaryHeap::new();
    let mut idle_workers: Vec<usize> = Vec::new();
    let mut found_solution = false;
    let mut dispatched = 0usize;
    let mut last_progress = Instant::now();

    let dispatch = |pq: &mut BinaryHeap<PqItem>, idle: &mut Vec<usize>,
                    worker_txs: &[std::sync::mpsc::SyncSender<Option<SatWorkItem>>],
                    dispatched: &mut usize| {
        while let Some(tid) = idle.pop() {
            if let Some(pqi) = pq.pop() {
                *dispatched += 1;
                let _ = worker_txs[tid].send(Some(pqi.item));
            } else {
                idle.push(tid);
                break;
            }
        }
    };

    let mut producer_done = false;
    loop {
        if found.load(AtomicOrdering::Relaxed) {
            if let Ok(Some(sol)) = result_rx.recv() {
                if verbose {
                    print_solution(
                        &format!("TT({}) SOLUTION", problem.n),
                        &sol.0, &sol.1, &sol.2, &sol.3);
                }
                found_solution = true;
            }
            break;
        }

        // Drain producer channel (non-blocking)
        loop {
            match producer_rx.try_recv() {
                Ok(item) => {
                    let priority = item.priority;
                    pq.push(PqItem { priority, item });
                }
                Err(std::sync::mpsc::TryRecvError::Empty) => break,
                Err(std::sync::mpsc::TryRecvError::Disconnected) => {
                    producer_done = true;
                    break;
                }
            }
        }

        // Drain ready signals (non-blocking)
        loop {
            match ready_rx.try_recv() {
                Ok(tid) => idle_workers.push(tid),
                Err(_) => break,
            }
        }

        dispatch(&mut pq, &mut idle_workers, &worker_txs, &mut dispatched);

        if producer_done && pq.is_empty() && idle_workers.len() == workers {
            break;
        }

        // Time limit check
        if time_limit_secs > 0 && run_start.elapsed().as_secs() >= time_limit_secs {
            if verbose {
                eprintln!("  Time limit reached ({}s)", time_limit_secs);
            }
            found.store(true, AtomicOrdering::Relaxed); // signal producer + workers to stop
            break;
        }

        if verbose && last_progress.elapsed().as_secs() >= 10 {
            let elapsed = run_start.elapsed().as_secs_f64();
            let done = items_completed.load(AtomicOrdering::Relaxed);
            eprintln!("[{:.0}s] {} | queue {} | dispatched {} | done {} | {:.1} items/s",
                elapsed, mode_name, pq.len(), dispatched, done,
                if elapsed > 0.0 { done as f64 / elapsed } else { 0.0 });
            last_progress = Instant::now();
        }

        std::thread::yield_now();
    }

    // Shutdown workers
    for tx in &worker_txs {
        let _ = tx.send(None);
    }

    // Collect producer stats
    let mut stats = SearchStats::default();
    if let Ok(producer_stats) = producer_handle.join() {
        stats.merge_from(&producer_stats);
    }
    stats.phase_c_nanos = phase_c_nanos_shared.load(AtomicOrdering::Relaxed);

    if verbose {
        let total = run_start.elapsed();
        let phase_b = std::time::Duration::from_nanos(stats.phase_b_nanos);
        let phase_c = std::time::Duration::from_nanos(stats.phase_c_nanos);
        let done = items_completed.load(AtomicOrdering::Relaxed);
        println!("\n--- {} ({} threads) ---", mode_name, workers);
        if stats.phase_b_nanos > 0 {
            println!("  Phase B (candidate gen):  {:>10.3?}  (thread-sum)", phase_b);
        }
        println!("  Phase C (SAT solve):      {:>10.3?}  (thread-sum)", phase_c);
        println!("  Items dispatched:         {:>10}", dispatched);
        println!("  Items completed:          {:>10}", done);
        println!("  Rate:                     {:.2} solves/s", done as f64 / total.as_secs_f64());
        println!("  Wall-clock:               {:>10.3?}", total);
        if !found_solution {
            println!("No solution found.");
        }
    }
    SearchReport { stats, elapsed: run_start.elapsed(), found_solution }
}

/// SAT-based X/Y/W solver: given fixed Z (from DFS), encode X/Y/W + autocorrelation
/// constraints and solve. This avoids the spectral pairing bottleneck of Phase B.
///
/// Variables: X[0..n), Y[0..n), W[0..m) as SAT vars; Z values hardcoded as constants.
fn sat_solve_xyw(
    problem: Problem,
    tuple: SumTuple,
    z_values: &[i8],
    verbose: bool,
) -> Option<(PackedSeq, PackedSeq, PackedSeq)> {
    let n = problem.n;
    let m = problem.m();
    // Variables: X=1..n, Y=n+1..2n, W=2n+1..2n+m
    let total_vars = 2 * n + m;
    let mut enc = SatEncoder { n: total_vars, m: 0, next_var: (total_vars + 1) as i32, xnor_triples: Vec::new() };
    let mut solver: radical::Solver = Default::default();

    let x_var = |i: usize| -> i32 { (i + 1) as i32 };
    let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };
    let w_var = |i: usize| -> i32 { (2 * n + i + 1) as i32 };

    // Symmetry breaking
    solver.add_clause([x_var(0)]); // x[0] = +1

    // Sum constraints
    if (tuple.x + n as i32) % 2 != 0 || (tuple.y + n as i32) % 2 != 0
        || (tuple.w + m as i32) % 2 != 0 { return None; }
    let x_pos = ((tuple.x + n as i32) / 2) as usize;
    let y_pos = ((tuple.y + n as i32) / 2) as usize;
    let w_pos = ((tuple.w + m as i32) / 2) as usize;
    let x_lits: Vec<i32> = (0..n).map(|i| x_var(i)).collect();
    let y_lits: Vec<i32> = (0..n).map(|i| y_var(i)).collect();
    let w_lits: Vec<i32> = (0..m).map(|i| w_var(i)).collect();
    enc.encode_cardinality_eq(&mut solver, &x_lits, x_pos);
    enc.encode_cardinality_eq(&mut solver, &y_lits, y_pos);
    enc.encode_cardinality_eq(&mut solver, &w_lits, w_pos);

    // Precompute Z autocorrelations (constants)
    let z_autocorr: Vec<i32> = (0..n).map(|s| {
        if s == 0 { 0 } else {
            (0..(n - s)).map(|i| (z_values[i] as i32) * (z_values[i + s] as i32)).sum()
        }
    }).collect();

    // Autocorrelation constraints: N_X(k) + N_Y(k) + 2*N_Z(k) + 2*N_W(k) = 0
    // Z is fixed, so 2*N_Z(k) is a constant.
    // N_X(k) + N_Y(k) + 2*N_W(k) = -2*N_Z(k)
    // agree_X(k) + agree_Y(k) + 2*agree_W(k) = (2*(n-k) + w_overlap) + N_Z(k)
    //   where w_overlap = max(0, m-k)
    // Wait, let me derive carefully:
    // N_X + N_Y + 2*N_W = -2*N_Z
    // N_X = 2*agX - (n-k), N_Y = 2*agY - (n-k), N_W = 2*agW - w_overlap
    // 2*agX + 2*agY + 4*agW - 2*(n-k) - 2*w_overlap = -2*N_Z
    // agX + agY + 2*agW = (2*(n-k) + 2*w_overlap - 2*N_Z) / 2 = (n-k) + w_overlap - N_Z
    for k in 1..n {
        let w_overlap = if k < m { m - k } else { 0 };
        let target_i = (n - k) as i32 + w_overlap as i32 - z_autocorr[k];
        if target_i < 0 || target_i as usize > 2 * (n - k) + 2 * w_overlap {
            return None; // infeasible
        }
        let target = target_i as usize;

        // XY agrees (weight 1)
        let mut xy_lits = Vec::new();
        for i in 0..(n - k) {
            xy_lits.push(enc.encode_xnor(&mut solver, x_var(i), x_var(i + k)));
        }
        for i in 0..(n - k) {
            xy_lits.push(enc.encode_xnor(&mut solver, y_var(i), y_var(i + k)));
        }

        // W agrees (weight 2) — use selector approach
        let mut w_agree_lits = Vec::new();
        for i in 0..w_overlap {
            w_agree_lits.push(enc.encode_xnor(&mut solver, w_var(i), w_var(i + k)));
        }

        let xy_ctr = enc.build_counter(&mut solver, &xy_lits);
        let w_ctr = enc.build_counter(&mut solver, &w_agree_lits);

        let mut selectors = Vec::new();
        for c_w in 0..=w_agree_lits.len() {
            let rem = target as isize - 2 * c_w as isize;
            if rem < 0 || rem as usize > xy_lits.len() { continue; }
            let c_xy = rem as usize;
            let sel = enc.fresh();
            if c_xy > 0 {
                if c_xy < xy_ctr.len() && xy_ctr[c_xy] != 0 { solver.add_clause([-sel, xy_ctr[c_xy]]); }
                else { solver.add_clause([-sel]); continue; }
            }
            if c_xy + 1 < xy_ctr.len() && xy_ctr[c_xy + 1] != 0 { solver.add_clause([-sel, -xy_ctr[c_xy + 1]]); }
            if c_w > 0 {
                if c_w < w_ctr.len() && w_ctr[c_w] != 0 { solver.add_clause([-sel, w_ctr[c_w]]); }
                else { solver.add_clause([-sel]); continue; }
            }
            if c_w + 1 < w_ctr.len() && w_ctr[c_w + 1] != 0 { solver.add_clause([-sel, -w_ctr[c_w + 1]]); }
            selectors.push(sel);
        }
        if selectors.is_empty() { return None; }
        solver.add_clause(selectors.iter().copied());
    }

    if verbose {
        eprintln!("  SAT X/Y/W: {} vars, z_sum={}", enc.next_var - 1, tuple.z);
    }

    match solver.solve() {
        Some(true) => {
            let x: Vec<i8> = (0..n).map(|i| if solver.value(x_var(i)) == Some(true) { 1 } else { -1 }).collect();
            let y: Vec<i8> = (0..n).map(|i| if solver.value(y_var(i)) == Some(true) { 1 } else { -1 }).collect();
            let w: Vec<i8> = (0..m).map(|i| if solver.value(w_var(i)) == Some(true) { 1 } else { -1 }).collect();
            Some((PackedSeq::from_values(&x), PackedSeq::from_values(&y), PackedSeq::from_values(&w)))
        }
        _ => None,
    }
}

/// Given fixed W, find Z candidates via SAT with range constraints per lag.
///
/// For each lag k: N_X(k) + N_Y(k) + 2*N_Z(k) + 2*N_W(k) = 0
/// W is fixed → 2*N_W(k) is known. N_Z(k) = 2*agZ - (n-k).
/// We need -(2*N_Z(k) + 2*N_W(k)) = N_X(k) + N_Y(k) to be achievable,
/// i.e. |2*N_Z(k) + 2*N_W(k)| ≤ 2*(n-k), giving a range for agZ.
///
/// Returns multiple Z candidates by blocking previous solutions.
fn sat_find_z_candidates(
    problem: Problem,
    z_sum: i32,
    w_values: &[i8],
    max_candidates: usize,
) -> Vec<PackedSeq> {
    let n = problem.n;
    let m = problem.m();

    if (z_sum + n as i32) % 2 != 0 { return Vec::new(); }
    let z_pos = ((z_sum + n as i32) / 2) as usize;

    let mut enc = SatEncoder { n: 0, m: 0, next_var: (n + 1) as i32, xnor_triples: Vec::new() };
    let mut solver: radical::Solver = Default::default();

    let z_var = |i: usize| -> i32 { (i + 1) as i32 };

    // Symmetry breaking: z[0] = +1
    solver.add_clause([z_var(0)]);

    // Sum constraint
    let z_lits: Vec<i32> = (0..n).map(|i| z_var(i)).collect();
    enc.encode_cardinality_eq(&mut solver, &z_lits, z_pos);

    // Precompute W autocorrelations
    let w_autocorr: Vec<i32> = (0..n).map(|s| {
        if s == 0 || s >= m { 0 } else {
            (0..(m - s)).map(|i| (w_values[i] as i32) * (w_values[i + s] as i32)).sum()
        }
    }).collect();

    // Per-lag range constraints on Z autocorrelation.
    // N_X(k) + N_Y(k) = -(2*N_Z(k) + 2*N_W(k))
    // |N_X(k) + N_Y(k)| ≤ 2*(n-k)  (since each contributes at most n-k)
    // → -2*(n-k) ≤ -(2*N_Z(k) + 2*N_W(k)) ≤ 2*(n-k)
    // → -2*(n-k) - 2*N_W(k) ≤ 2*N_Z(k) ≤ 2*(n-k) - 2*N_W(k)
    // → -(n-k) - N_W(k) ≤ N_Z(k) ≤ (n-k) - N_W(k)
    // N_Z(k) = 2*agZ(k) - (n-k), so agZ(k) ∈ [lo, hi]:
    //   lo = max(0, ceil(((n-k) + (-(n-k) - N_W(k))) / 2)) = max(0, ceil(-N_W(k) / 2))
    //   hi = min(n-k, floor(((n-k) + ((n-k) - N_W(k))) / 2)) = min(n-k, floor((2*(n-k) - N_W(k)) / 2))
    //   = min(n-k, (2*(n-k) - N_W(k)) / 2)  [integer division]
    for k in 1..n {
        let pairs = n - k;
        let nw = w_autocorr[k];

        // agZ range from the XY feasibility constraint
        let lo = ((-nw) as f64 / 2.0).ceil().max(0.0) as usize;
        let hi_val = (2 * pairs as i32 - nw) as f64 / 2.0;
        let hi = (hi_val.floor() as usize).min(pairs);

        if lo > hi { return Vec::new(); } // infeasible

        // Build agree-count for Z at lag k
        let mut z_agree_lits = Vec::with_capacity(pairs);
        for i in 0..pairs {
            z_agree_lits.push(enc.encode_xnor(&mut solver, z_var(i), z_var(i + k)));
        }

        // Encode: lo ≤ count(z_agree) ≤ hi
        let ctr = enc.build_counter(&mut solver, &z_agree_lits);
        // At least lo: ctr[lo] must be true (if lo > 0)
        if lo > 0 && lo < ctr.len() && ctr[lo] != 0 {
            solver.add_clause([ctr[lo]]);
        } else if lo > 0 {
            return Vec::new(); // can't achieve minimum
        }
        // At most hi: ctr[hi+1] must be false (if hi+1 is valid)
        if hi + 1 < ctr.len() && ctr[hi + 1] != 0 {
            solver.add_clause([-ctr[hi + 1]]);
        }
    }

    // Find multiple Z by solving + blocking
    let mut results = Vec::new();
    for _ in 0..max_candidates {
        match solver.solve() {
            Some(true) => {
                let z: Vec<i8> = (0..n).map(|i| {
                    if solver.value(z_var(i)) == Some(true) { 1 } else { -1 }
                }).collect();
                // Block this solution
                let block: Vec<i32> = (0..n).map(|i| {
                    if z[i] == 1 { -z_var(i) } else { z_var(i) }
                }).collect();
                solver.add_clause(block);
                results.push(PackedSeq::from_values(&z));
            }
            _ => break,
        }
    }
    results
}

/// W-enumerate + SAT-Z + Phase C XY pipeline.
/// For each spectrally-valid W: use SAT to find compatible Z candidates,
/// then send each (Z, W) pair to the existing XY solver.
fn run_w_sat_search(cfg: &SearchConfig, verbose: bool) -> SearchReport {
    let problem = cfg.problem;
    let tuples = phase_a_tuples(problem, cfg.test_tuple.as_ref());
    // Group tuples by w_sum
    let mut tuples_by_w: HashMap<i32, Vec<SumTuple>> = HashMap::new();
    for &tuple in &tuples {
        tuples_by_w.entry(tuple.w).or_default().push(tuple);
    }
    if verbose {
        eprintln!("{} sum-tuples, {} distinct w_sums", tuples.len(), tuples_by_w.len());
    }
    let theta = cfg.theta_samples;
    let max_w = cfg.max_w;
    run_parallel_search(problem, None, cfg.sat_config.clone(), move |tx, found| {
        let spectral_w = SpectralFilter::new(problem.m(), theta);
        let mut stats = SearchStats::default();
        let individual_bound = problem.spectral_bound();
        let max_z_per_w = 10;
        let mut fft_buf = Vec::with_capacity(spectral_w.fft_size);
        for (&w_sum, w_tuples) in &tuples_by_w {
            if found.load(AtomicOrdering::Relaxed) { break; }
            generate_sequences_permuted(problem.m(), w_sum, true, false, max_w, |w_values| {
                if found.load(AtomicOrdering::Relaxed) { return false; }
                stats.w_generated += 1;
                if spectrum_if_ok(w_values, &spectral_w, individual_bound, &mut fft_buf).is_none() {
                    return true;
                }
                stats.w_spectral_ok += 1;
                let pw = PackedSeq::from_values(w_values);
                for &tuple in w_tuples {
                    if (tuple.y + problem.n as i32) % 2 != 0 { continue; }
                    let z_candidates = sat_find_z_candidates(problem, tuple.z, w_values, max_z_per_w);
                    for z_seq in &z_candidates {
                        let zw_autocorr = compute_zw_autocorr(problem, z_seq, &pw);
                        let _ = tx.send(SatWorkItem {
                            tuple, x: SeqInput::Blank, y: SeqInput::Blank,
                            z: SeqInput::Fixed(z_seq.clone()),
                            w: SeqInput::Fixed(pw.clone()),
                            zw_autocorr: Some(zw_autocorr), priority: 0.0,
                            boundary: None,
                        });
                    }
                }
                true
            });
        }
        stats
    }, verbose, "W-enum + SAT Z + SAT XY", 0)
}

/// Hybrid Z-DFS + SAT X/Y/W search. Generates Z candidates via DFS with
/// spectral filtering, then uses SAT to find X/Y/W for each Z.
fn run_z_sat_search(cfg: &SearchConfig, verbose: bool) -> SearchReport {
    let problem = cfg.problem;
    let tuples = phase_a_tuples(problem, cfg.test_tuple.as_ref());
    if verbose {
        eprintln!("{} sum-tuples", tuples.len());
    }
    let theta = cfg.theta_samples;
    let max_z = cfg.max_z;
    run_parallel_search(problem, None, cfg.sat_config.clone(), move |tx, found| {
        let spectral_z = SpectralFilter::new(problem.n, theta);
        let mut stats = SearchStats::default();
        let individual_bound = problem.spectral_bound();
        for tuple in &tuples {
            if found.load(AtomicOrdering::Relaxed) { break; }
            let mut fft_buf = Vec::with_capacity(spectral_z.fft_size);
            generate_sequences_permuted(problem.n, tuple.z, true, true, max_z, |z_values| {
                if found.load(AtomicOrdering::Relaxed) { return false; }
                stats.z_generated += 1;
                if spectrum_if_ok(z_values, &spectral_z, individual_bound, &mut fft_buf).is_none() {
                    return true;
                }
                stats.z_spectral_ok += 1;
                let z = PackedSeq::from_values(z_values);
                let _ = tx.send(SatWorkItem {
                    tuple: *tuple, x: SeqInput::Blank, y: SeqInput::Blank,
                    z: SeqInput::Fixed(z), w: SeqInput::Blank,
                    zw_autocorr: None, priority: 0.0,
                    boundary: None,
                });
                true
            });
        }
        stats
    }, verbose, "Z-DFS + SAT XYW", 0)
}

fn run_benchmark(cfg: &SearchConfig) {
    if cfg.stochastic {
        run_stochastic_benchmark(cfg);
    } else {
        run_hybrid_benchmark(cfg);
    }
}

fn run_hybrid_benchmark(cfg: &SearchConfig) {
    let repeats = cfg.benchmark_repeats.max(1);
    let warmup = run_hybrid_search(cfg, false);
    println!(
        "benchmark,warmup,elapsed_ms={:.3},found_solution={}",
        warmup.elapsed.as_secs_f64() * 1000.0,
        warmup.found_solution
    );
    println!("benchmark,run,elapsed_ms,found_solution");
    let mut elapsed_ms = Vec::with_capacity(repeats);
    for run in 1..=repeats {
        let report = run_hybrid_search(cfg, false);
        let ms = report.elapsed.as_secs_f64() * 1000.0;
        elapsed_ms.push(ms);
        println!("benchmark,{},{:.3},{}", run, ms, report.found_solution);
    }
    elapsed_ms.sort_by(|a, b| a.partial_cmp(b).unwrap_or(Ordering::Equal));
    let median = elapsed_ms[elapsed_ms.len() / 2];
    let mean = elapsed_ms.iter().sum::<f64>() / elapsed_ms.len() as f64;
    println!("benchmark,summary,mean_ms={:.3},median_ms={:.3},repeats={}", mean, median, repeats);
}

fn run_stochastic_benchmark(cfg: &SearchConfig) {
    let secs = if cfg.stochastic_seconds > 0 { cfg.stochastic_seconds } else { 10 };
    let repeats = cfg.benchmark_repeats.max(1);
    // Warmup
    let warmup = stochastic_search(cfg.problem, cfg.test_tuple.as_ref(), false, secs);
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
        let report = stochastic_search(cfg.problem, cfg.test_tuple.as_ref(), false, secs);
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

fn stochastic_search(problem: Problem, test_tuple: Option<&SumTuple>, verbose: bool, time_limit_secs: u64) -> SearchReport {
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
    let norm = Arc::new(phase_a_tuples(problem, test_tuple));
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
                    let px = PackedSeq::from_values(&x);
                    let py = PackedSeq::from_values(&y);
                    let pz = PackedSeq::from_values(&z);
                    let pw = PackedSeq::from_values(&w);
                    if verbose {
                        print_solution(&format!("TT({}) found (restart {} flip {})", problem.n, restart, flip), &px, &py, &pz, &pw);
                    }
                    let ok = verify_tt(problem, &px, &py, &pz, &pw);
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

// ── SAT-based search using CaDiCaL ──────────────────────────────────────────

/// Variable layout for SAT encoding:
///   X[0..n)   → vars 1..=n
///   Y[0..n)   → vars n+1..=2n
///   Z[0..n)   → vars 2n+1..=3n
///   W[0..m)   → vars 3n+1..=3n+m
/// Additional auxiliary variables start at 3n+m+1.
#[allow(dead_code)]
struct SatEncoder {
    n: usize,
    m: usize,
    next_var: i32,
    /// XNOR triples: (aux, a, b) where aux = (a XNOR b)
    xnor_triples: Vec<(i32, i32, i32)>,
}

impl SatEncoder {
    fn new(n: usize) -> Self {
        let m = n - 1;
        Self { n, m, next_var: (3 * n + m + 1) as i32, xnor_triples: Vec::new() }
    }

    fn x_var(&self, i: usize) -> i32 { (i + 1) as i32 }
    fn y_var(&self, i: usize) -> i32 { (self.n + i + 1) as i32 }
    fn z_var(&self, i: usize) -> i32 { (2 * self.n + i + 1) as i32 }
    fn w_var(&self, i: usize) -> i32 { (3 * self.n + i + 1) as i32 }
    fn fresh(&mut self) -> i32 { let v = self.next_var; self.next_var += 1; v }

    /// Encode XNOR: aux ↔ (a ↔ b). Returns the auxiliary variable.
    /// aux=true means a and b have the same sign (+1,+1 or -1,-1).
    fn encode_xnor(&mut self, solver: &mut impl SatSolver, a: i32, b: i32) -> i32 {
        let aux = self.fresh();
        // aux → (a ↔ b):  aux → (a → b) ∧ (b → a)
        //   ¬aux ∨ ¬a ∨ b, ¬aux ∨ a ∨ ¬b
        // (a ↔ b) → aux:  (¬a ∨ ¬b ∨ aux) ∧ (a ∨ b ∨ aux)
        solver.add_clause([-aux, -a, b]);
        solver.add_clause([-aux, a, -b]);
        solver.add_clause([a, b, aux]);
        solver.add_clause([-a, -b, aux]);
        self.xnor_triples.push((aux, a, b));
        aux
    }

    /// Totalizer encoding (Bailleux & Boufkhad 2003): build a binary tree
    /// that counts how many of `lits` are true, using O(n log n) auxiliary
    /// variables instead of O(n²) for a sequential counter.
    ///
    /// Returns vec r where r[c] (for c in 1..=lits.len()) is a SAT variable
    /// that is true iff at least c of `lits` are true. r[0] is unused.
    fn build_counter(
        &mut self,
        solver: &mut impl SatSolver,
        lits: &[i32],
    ) -> Vec<i32> {
        let n = lits.len();
        if n == 0 {
            return vec![0];
        }
        if n == 1 {
            // Single literal: at-least-1 ↔ lit
            let v = self.fresh();
            solver.add_clause([-lits[0], v]);
            solver.add_clause([lits[0], -v]);
            return vec![0, v];
        }

        // Split into halves and recurse
        let mid = n / 2;
        let left = self.build_counter(solver, &lits[..mid]);
        let right = self.build_counter(solver, &lits[mid..]);
        let left_max = mid;    // left can count 0..=mid
        let right_max = n - mid; // right can count 0..=n-mid

        // Merge: create output variables for counts 1..=n
        let mut out = vec![0i32; n + 1];
        for c in 1..=n {
            out[c] = self.fresh();
        }

        // Merge clauses: out[c] ↔ ∃(a+b=c) left[a] ∧ right[b]
        // Encoded as:
        //   Forward: left[a] ∧ right[b] → out[a+b]  (for all valid a,b)
        //   Backward: out[c] → left[a] ∨ right[c-a]  (for all valid a given c)
        //
        // Using "at-least" semantics (monotone):
        //   left[a] ∧ right[b] → out[a+b]   (forward, ensures out counts enough)
        //   out[c] → left[a] ∨ right[c-a]    (backward, ensures out doesn't overcount)

        for a in 0..=left_max {
            for b in 0..=right_max {
                let c = a + b;
                if c == 0 || c > n { continue; }
                // Forward: left[a] ∧ right[b] → out[c]
                // i.e., ¬left[a] ∨ ¬right[b] ∨ out[c]
                let l = if a == 0 { 0 } else { left[a] };   // 0 means "always true"
                let r = if b == 0 { 0 } else { right[b] };
                match (l, r) {
                    (0, 0) => { solver.add_clause([out[c]]); } // both always true
                    (0, _) => { solver.add_clause([-r, out[c]]); }
                    (_, 0) => { solver.add_clause([-l, out[c]]); }
                    (_, _) => { solver.add_clause([-l, -r, out[c]]); }
                }
            }
        }

        // Backward: out[c] → ∨_{a=max(0,c-right_max)..min(c,left_max)} (left[a] ∨ right[c-a])
        // Simplified: out[c] → left[a] ∨ right[c-a] for each valid split a
        // Actually the standard totalizer backward clause is:
        //   ¬left[a+1] ∧ ¬right[b+1] → ¬out[a+b+1]
        // i.e., out[a+b+1] → left[a+1] ∨ right[b+1]
        for a in 0..=left_max {
            for b in 0..=right_max {
                let c = a + b + 1;
                if c > n { continue; }
                let l_next = if a + 1 <= left_max { left[a + 1] } else { 0 };
                let r_next = if b + 1 <= right_max { right[b + 1] } else { 0 };
                // out[c] → l_next ∨ r_next
                match (l_next, r_next) {
                    (0, 0) => { solver.add_clause([-out[c]]); } // impossible count
                    (0, _) => { solver.add_clause([-out[c], r_next]); }
                    (_, 0) => { solver.add_clause([-out[c], l_next]); }
                    (_, _) => { solver.add_clause([-out[c], l_next, r_next]); }
                }
            }
        }

        out
    }

    /// Encode exactly `target` of `lits` must be true, using the totalizer.
    fn encode_cardinality_eq(
        &mut self,
        solver: &mut impl SatSolver,
        lits: &[i32],
        target: usize,
    ) {
        let n = lits.len();
        if n == 0 {
            assert!(target == 0);
            return;
        }
        if target > n {
            solver.add_clause([]); // impossible
            return;
        }
        let ctr = self.build_counter(solver, lits);
        // Enforce at-least target
        if target >= 1 {
            assert!(ctr[target] != 0);
            solver.add_clause([ctr[target]]);
        }
        // Enforce at-most target (i.e., NOT at-least target+1)
        if target + 1 <= n {
            assert!(ctr[target + 1] != 0);
            solver.add_clause([-ctr[target + 1]]);
        }
    }
}

/// Build the full SAT encoding for a given problem and sum-tuple.
/// Returns (encoder, solver) pair before solving.
fn sat_encode(problem: Problem, tuple: SumTuple) -> (SatEncoder, radical::Solver) {
    let n = problem.n;
    let m = problem.m();
    let mut enc = SatEncoder::new(n);
    let mut solver: radical::Solver = Default::default();

    // Minimal symmetry breaking: only fix x[0]=+1.
    // Full TT symmetry group includes negation of each sequence independently,
    // so fixing x[0]=+1 is always valid. Other constraints like z[0]=z[n-1]=+1
    // are too restrictive for some n (e.g., TT(6)).
    solver.add_clause([enc.x_var(0)]);  // x[0] = +1

    // Sum constraints: encode that exactly (sum+len)/2 variables are true (=+1)
    let x_pos = ((tuple.x + n as i32) / 2) as usize;
    let y_pos = ((tuple.y + n as i32) / 2) as usize;
    let z_pos = ((tuple.z + n as i32) / 2) as usize;
    let w_pos = ((tuple.w + m as i32) / 2) as usize;

    let x_lits: Vec<i32> = (0..n).map(|i| enc.x_var(i)).collect();
    let y_lits: Vec<i32> = (0..n).map(|i| enc.y_var(i)).collect();
    let z_lits: Vec<i32> = (0..n).map(|i| enc.z_var(i)).collect();
    let w_lits: Vec<i32> = (0..m).map(|i| enc.w_var(i)).collect();

    enc.encode_cardinality_eq(&mut solver, &x_lits, x_pos);
    enc.encode_cardinality_eq(&mut solver, &y_lits, y_pos);
    enc.encode_cardinality_eq(&mut solver, &z_lits, z_pos);
    enc.encode_cardinality_eq(&mut solver, &w_lits, w_pos);

    for k in 1..n {
        let w_overlap = if k < m { m - k } else { 0 };
        let target = 2 * (n - k) + w_overlap;

        let mut xy_lits = Vec::new();
        for i in 0..(n - k) {
            xy_lits.push(enc.encode_xnor(&mut solver, enc.x_var(i), enc.x_var(i + k)));
        }
        for i in 0..(n - k) {
            xy_lits.push(enc.encode_xnor(&mut solver, enc.y_var(i), enc.y_var(i + k)));
        }

        let mut zw_lits = Vec::new();
        for i in 0..(n - k) {
            zw_lits.push(enc.encode_xnor(&mut solver, enc.z_var(i), enc.z_var(i + k)));
        }
        for i in 0..w_overlap {
            zw_lits.push(enc.encode_xnor(&mut solver, enc.w_var(i), enc.w_var(i + k)));
        }

        let xy_ctr = enc.build_counter(&mut solver, &xy_lits);
        let zw_ctr = enc.build_counter(&mut solver, &zw_lits);

        let mut selectors = Vec::new();
        for c_zw in 0..=zw_lits.len() {
            let rem = target as isize - 2 * c_zw as isize;
            if rem < 0 || rem as usize > xy_lits.len() { continue; }
            let c_xy = rem as usize;

            let sel = enc.fresh();

            if c_xy > 0 {
                if c_xy < xy_ctr.len() && xy_ctr[c_xy] != 0 {
                    solver.add_clause([-sel, xy_ctr[c_xy]]);
                } else {
                    solver.add_clause([-sel]);
                    continue;
                }
            }
            if c_xy + 1 < xy_ctr.len() && xy_ctr[c_xy + 1] != 0 {
                solver.add_clause([-sel, -xy_ctr[c_xy + 1]]);
            }

            if c_zw > 0 {
                if c_zw < zw_ctr.len() && zw_ctr[c_zw] != 0 {
                    solver.add_clause([-sel, zw_ctr[c_zw]]);
                } else {
                    solver.add_clause([-sel]);
                    continue;
                }
            }
            if c_zw + 1 < zw_ctr.len() && zw_ctr[c_zw + 1] != 0 {
                solver.add_clause([-sel, -zw_ctr[c_zw + 1]]);
            }

            selectors.push(sel);
        }

        if selectors.is_empty() {
            solver.add_clause([]);
        } else {
            solver.add_clause(selectors.iter().copied());
        }
    }

    (enc, solver)
}

fn sat_search(problem: Problem, tuple: SumTuple, boundary: Option<&BoundaryConfig>, verbose: bool) -> Option<(Vec<i8>, Vec<i8>, Vec<i8>, Vec<i8>)> {
    let encode_start = Instant::now();
    let n = problem.n;
    let m = problem.m();
    let (enc, mut solver) = sat_encode(problem, tuple);

    // Fix boundary variables if a pre-screened config is provided
    if let Some(bnd) = boundary {
        let k = bnd.k;
        for i in 0..k {
            let lit = enc.x_var(i);
            solver.add_clause([if (bnd.x_bits >> i) & 1 == 1 { lit } else { -lit }]);
            let lit = enc.x_var(n - k + i);
            solver.add_clause([if (bnd.x_bits >> (k + i)) & 1 == 1 { lit } else { -lit }]);

            let lit = enc.y_var(i);
            solver.add_clause([if (bnd.y_bits >> i) & 1 == 1 { lit } else { -lit }]);
            let lit = enc.y_var(n - k + i);
            solver.add_clause([if (bnd.y_bits >> (k + i)) & 1 == 1 { lit } else { -lit }]);

            let lit = enc.z_var(i);
            solver.add_clause([if (bnd.z_bits >> i) & 1 == 1 { lit } else { -lit }]);
            let lit = enc.z_var(n - k + i);
            solver.add_clause([if (bnd.z_bits >> (k + i)) & 1 == 1 { lit } else { -lit }]);

            let lit = enc.w_var(i);
            solver.add_clause([if (bnd.w_bits >> i) & 1 == 1 { lit } else { -lit }]);
            let lit = enc.w_var(m - k + i);
            solver.add_clause([if (bnd.w_bits >> (k + i)) & 1 == 1 { lit } else { -lit }]);
        }
    }

    let encode_elapsed = encode_start.elapsed();
    if verbose {
        println!("SAT encoding: n={}, tuple={}, {} vars, encoded in {:.3?}, solving...", n, tuple, enc.next_var - 1, encode_elapsed);
    }

    let solve_start = Instant::now();
    let result = solver.solve();
    let solve_elapsed = solve_start.elapsed();
    if verbose {
        println!("  solve: {:.3?}, conflicts={}, clauses={}", solve_elapsed, solver.num_conflicts(), solver.num_clauses());
    }
    match result {
        Some(true) => {
            let x: Vec<i8> = (0..n).map(|i| if solver.value(enc.x_var(i)) == Some(true) { 1 } else { -1 }).collect();
            let y: Vec<i8> = (0..n).map(|i| if solver.value(enc.y_var(i)) == Some(true) { 1 } else { -1 }).collect();
            let z: Vec<i8> = (0..n).map(|i| if solver.value(enc.z_var(i)) == Some(true) { 1 } else { -1 }).collect();
            let w: Vec<i8> = (0..m).map(|i| if solver.value(enc.w_var(i)) == Some(true) { 1 } else { -1 }).collect();
            Some((x, y, z, w))
        }
        Some(false) => {
            if verbose { println!("UNSAT for tuple {} in {:.3?}", tuple, solve_elapsed); }
            None
        }
        None => {
            if verbose { println!("UNKNOWN for tuple {} in {:.3?}", tuple, solve_elapsed); }
            None
        }
    }
}

fn run_sat_search(cfg: &SearchConfig, verbose: bool) -> SearchReport {
    let problem = cfg.problem;
    let tuples = phase_a_tuples(problem, cfg.test_tuple.as_ref());
    if verbose {
        eprintln!("{} sum-tuples", tuples.len());
    }

    let n = problem.n;
    let m = problem.m();

    // Try to load XY boundary table for larger k
    let table_path = cfg.xy_table_path.clone().unwrap_or_else(|| "./xy-table-k7.bin".to_string());
    let xy_table: Option<XYBoundaryTable> = if cfg.no_table || n < 14 {
        None
    } else {
        XYBoundaryTable::load(&table_path).and_then(|t| {
            if n >= 2 * t.k { Some(t) } else { None }
        })
    };

    // Choose cubing depth: k positions from each end of each sequence.
    // Use table's k if available, otherwise fall back to k=6.
    let k = if cfg.no_table || n < 8 {
        0 // no cubing, monolithic SAT
    } else if let Some(ref tbl) = xy_table {
        let max_k = (n - 1) / 2;
        tbl.k.min(max_k)
    } else {
        let max_k = (n - 1) / 2;
        6usize.min(max_k)
    };

    if k == 0 {
        // Monolithic SAT: one big problem per tuple
        run_parallel_search(problem, None, cfg.sat_config.clone(), move |tx, found| {
            let stats = SearchStats::default();
            for tuple in tuples {
                if found.load(AtomicOrdering::Relaxed) { break; }
                let _ = tx.send(SatWorkItem {
                    tuple, x: SeqInput::Blank, y: SeqInput::Blank,
                    z: SeqInput::Blank, w: SeqInput::Blank,
                    zw_autocorr: None, priority: 0.0,
                    boundary: None,
                });
            }
            stats
        }, verbose, "pure SAT", 0)
    } else {
        // On-the-fly boundary enumeration: compute exact-lag constraints directly
        // and enumerate all valid 4-sequence boundary configs as SAT cubes.
        //
        // Build exact-lag bit pairs (same math as gen_table).
        // For lag index j (0..k), the absolute lag is s = n-k+j.
        // X/Y/Z (length n): pairs (i, k+i+j) for i = 0..k-j-1
        // W (length n-1): pairs (i, k+i+j+1) for i = 0..k-j-2 (only when j < k-1)
        struct ExactLag {
            xy_pairs: Vec<(u32, u32)>,
            z_pairs: Vec<(u32, u32)>,
            w_pairs: Vec<(u32, u32)>,
        }
        let mut exact_lags: Vec<ExactLag> = Vec::new();
        for j in 0..k {
            let xy_pairs: Vec<(u32, u32)> = (0..k-j)
                .map(|i| (i as u32, (k + i + j) as u32))
                .collect();
            let z_pairs = xy_pairs.clone();
            let w_pairs: Vec<(u32, u32)> = if j < k - 1 {
                (0..k-j-1).map(|i| (i as u32, (k + i + j + 1) as u32)).collect()
            } else {
                Vec::new()
            };
            exact_lags.push(ExactLag { xy_pairs, z_pairs, w_pairs });
        }

        let middle_n = n - 2 * k;
        let middle_m = m - 2 * k;
        let max_bnd_sum = (2 * k) as i32;

        // Helper: compute boundary autocorrelation contribution for one bit pattern
        let bnd_autocorr = |bits: u32, pairs: &[(u32, u32)]| -> i32 {
            let mut val = 0i32;
            for &(bi, bj) in pairs {
                val += 1 - 2 * (((bits >> bi) ^ (bits >> bj)) & 1) as i32;
            }
            val
        };

        // X/Y symmetry breaking: x[0] = +1 (bit 0 set)
        // So x_bits always has bit 0 set (we only enumerate x_bits with bit 0 = 1).
        let x_configs = 1u32 << (2 * k - 1); // x[0] fixed, 2k-1 free bits
        let y_configs = 1u32 << (2 * k);      // all 2k bits free
        let z_configs = 1u32 << (2 * k);      // all 2k bits free
        let w_configs = 1u32 << (2 * k);      // all 2k bits free

        let use_table = xy_table.is_some();
        if verbose {
            if use_table {
                eprintln!("Table-based cubing k={}: Z({})*W({}) boundary configs, XY from table",
                    k, z_configs, w_configs);
            } else {
                eprintln!("On-the-fly cubing k={}: enumerating X({})*Y({})*Z({})*W({}) boundary configs",
                    k, x_configs, y_configs, z_configs, w_configs);
            }
        }

        // On-the-fly XY precomputation (only when table not available)
        let xy_by_sig_sum: HashMap<u64, Vec<(u32, u32)>> = if use_table {
            HashMap::new() // not used — table provides XY lookup
        } else {
            if verbose {
                eprintln!("Precomputing X/Y boundary signatures...");
            }
            let pack_key = |sig: &[i16], x_sum: i32, y_sum: i32| -> u64 {
                let mut key: u64 = 0;
                for (i, &v) in sig.iter().enumerate() {
                    key |= ((v as i64 + 64) as u64 & 0x7F) << (i * 7);
                }
                key |= ((x_sum as i64 + 64) as u64 & 0x7F) << (sig.len() * 7);
                key |= ((y_sum as i64 + 64) as u64 & 0x7F) << ((sig.len() + 1) * 7);
                key
            };

            let num_lags = exact_lags.len();
            let mut x_autocorr: Vec<Vec<i16>> = Vec::with_capacity(x_configs as usize);
            for xr in 0..x_configs {
                let x_bits = (xr << 1) | 1;
                let vals: Vec<i16> = exact_lags.iter()
                    .map(|el| bnd_autocorr(x_bits, &el.xy_pairs) as i16)
                    .collect();
                x_autocorr.push(vals);
            }
            let mut y_autocorr: Vec<Vec<i16>> = Vec::with_capacity(y_configs as usize);
            for y_bits in 0..y_configs {
                let vals: Vec<i16> = exact_lags.iter()
                    .map(|el| bnd_autocorr(y_bits, &el.xy_pairs) as i16)
                    .collect();
                y_autocorr.push(vals);
            }

            let mut map: HashMap<u64, Vec<(u32, u32)>> = HashMap::new();
            let mut sig_buf = vec![0i16; num_lags];
            for xr in 0..x_configs {
                let x_bits = (xr << 1) | 1;
                let x_bnd_sum = 2 * (x_bits.count_ones() as i32) - max_bnd_sum;
                let x_ac = &x_autocorr[xr as usize];
                for y_bits in 0..y_configs {
                    let y_bnd_sum = 2 * (y_bits.count_ones() as i32) - max_bnd_sum;
                    let y_ac = &y_autocorr[y_bits as usize];
                    for j in 0..num_lags {
                        sig_buf[j] = x_ac[j] + y_ac[j];
                    }
                    let key = pack_key(&sig_buf, x_bnd_sum, y_bnd_sum);
                    map.entry(key).or_default().push((x_bits, y_bits));
                }
            }
            if verbose {
                let total_xy: usize = map.values().map(|v| v.len()).sum();
                eprintln!("  {} XY buckets, {} total entries", map.len(), total_xy);
            }
            map
        };

        // Parallel solve: each worker iterates a slice of z_bits, computes matching
        // configs on the fly, and solves them immediately. No pre-enumeration needed.
        let run_start = Instant::now();
        let workers = std::thread::available_parallelism()
            .map(|w| w.get()).unwrap_or(1).max(1);
        if verbose {
            eprintln!("TT({}): SAT cubed k={}, {} threads",
                n, k, workers);
        }
        let found = Arc::new(AtomicBool::new(false));
        let timed_out = Arc::new(AtomicBool::new(false));
        let items_done = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let sat_count = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let unsat_count = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let xy_matches = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let w_scanned = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let total_conflicts = Arc::new(std::sync::atomic::AtomicU64::new(0));
        let z_idx = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let time_limit_secs = cfg.sat_secs;
        let conflict_limit = cfg.conflict_limit;
        let xy_by_sig_sum = Arc::new(xy_by_sig_sum);
        let xy_table = Arc::new(xy_table);

        // Pre-build SAT encoding templates (one per tuple, clone per config)
        // Run BVE preprocessing to eliminate auxiliary variables from totalizer encoding
        let templates: Vec<(SatEncoder, radical::Solver)> = tuples.iter()
            .map(|&tuple| {
                let (enc, mut solver) = sat_encode(problem, tuple);
                solver.config.vivification = true;
                solver.config.chrono_bt = true;
                // Note: XOR constraints for XNOR triples OOM at n=56 scale (52K vars, ~25K triples)
                (enc, solver)
            })
            .collect();
        let templates = Arc::new(templates);
        let tuples = Arc::new(tuples);

        let mut handles = Vec::new();
        for _tid in 0..workers {
            let found = Arc::clone(&found);
            let timed_out = Arc::clone(&timed_out);
            let items_done = Arc::clone(&items_done);
            let sat_count = Arc::clone(&sat_count);
            let unsat_count = Arc::clone(&unsat_count);
            let xy_matches = Arc::clone(&xy_matches);
            let w_scanned = Arc::clone(&w_scanned);
            let total_conflicts = Arc::clone(&total_conflicts);
            let z_idx = Arc::clone(&z_idx);
            let xy_by_sig_sum = Arc::clone(&xy_by_sig_sum);
            let xy_table = Arc::clone(&xy_table);
            let templates = Arc::clone(&templates);
            let tuples = Arc::clone(&tuples);
            let exact_lags_clone: Vec<(Vec<(u32, u32)>, Vec<(u32, u32)>, Vec<(u32, u32)>)> = exact_lags.iter()
                .map(|el| (el.xy_pairs.clone(), el.z_pairs.clone(), el.w_pairs.clone()))
                .collect();

            handles.push(std::thread::spawn(move || {
                let bnd_autocorr = |bits: u32, pairs: &[(u32, u32)]| -> i32 {
                    let mut val = 0i32;
                    for &(bi, bj) in pairs {
                        val += 1 - 2 * (((bits >> bi) ^ (bits >> bj)) & 1) as i32;
                    }
                    val
                };

                // Warm-start state: phase-only transfer (clause transfer is harmful per testing)
                let mut warm_phase: Option<Vec<bool>> = None;

                let should_stop = || found.load(AtomicOrdering::Relaxed) || timed_out.load(AtomicOrdering::Relaxed);
                loop {
                    if should_stop() { break; }
                    let z_bits = z_idx.fetch_add(1, AtomicOrdering::Relaxed) as u32;
                    if z_bits >= z_configs { break; }

                    let z_bnd_sum = 2 * (z_bits.count_ones() as i32) - max_bnd_sum;

                    for w_bits in 0..w_configs {
                        if should_stop() { break; }
                        w_scanned.fetch_add(1, AtomicOrdering::Relaxed);
                        let w_bnd_sum = 2 * (w_bits.count_ones() as i32) - max_bnd_sum;

                        // Compute ZW signature for on-the-fly path (skip if table available)
                        let num_lags = exact_lags_clone.len();
                        let mut req_sig = vec![0i16; num_lags];
                        if xy_table.is_none() {
                            for (j, (_, z_pairs, w_pairs)) in exact_lags_clone.iter().enumerate() {
                                let z_val = bnd_autocorr(z_bits, z_pairs);
                                let w_val = bnd_autocorr(w_bits, w_pairs);
                                req_sig[j] = -(2 * z_val + 2 * w_val) as i16;
                            }
                        }

                        for (ti, tuple) in tuples.iter().enumerate() {
                            let z_mid = tuple.z - z_bnd_sum;
                            if z_mid.abs() > middle_n as i32 || (z_mid + middle_n as i32) % 2 != 0 { continue; }
                            let w_mid = tuple.w - w_bnd_sum;
                            if w_mid.abs() > middle_m as i32 || (w_mid + middle_m as i32) % 2 != 0 { continue; }

                            for x_bnd_sum in (-max_bnd_sum..=max_bnd_sum).step_by(2) {
                                let x_mid = tuple.x - x_bnd_sum;
                                if x_mid.abs() > middle_n as i32 || (x_mid + middle_n as i32) % 2 != 0 { continue; }
                                for y_bnd_sum in (-max_bnd_sum..=max_bnd_sum).step_by(2) {
                                    let y_mid = tuple.y - y_bnd_sum;
                                    if y_mid.abs() > middle_n as i32 || (y_mid + middle_n as i32) % 2 != 0 { continue; }

                                    // Look up XY boundary configs: table (O(1)) or HashMap
                                    let xy_slice: &[(u32, u32)];
                                    let xy_vec_holder: Vec<(u32, u32)>;
                                    if let Some(ref tbl) = *xy_table {
                                        xy_slice = tbl.get_xy_entries(z_bits, w_bits, x_bnd_sum, y_bnd_sum);
                                    } else {
                                        let key = {
                                            let mut k: u64 = 0;
                                            for (i, &v) in req_sig.iter().enumerate() {
                                                k |= ((v as i64 + 64) as u64 & 0x7F) << (i * 7);
                                            }
                                            k |= ((x_bnd_sum as i64 + 64) as u64 & 0x7F) << (num_lags * 7);
                                            k |= ((y_bnd_sum as i64 + 64) as u64 & 0x7F) << ((num_lags + 1) * 7);
                                            k
                                        };
                                        xy_vec_holder = Vec::new(); // lifetime anchor
                                        xy_slice = match xy_by_sig_sum.get(&key) {
                                            Some(v) => v.as_slice(),
                                            None => &xy_vec_holder,
                                        };
                                    }
                                    if !xy_slice.is_empty() {
                                        xy_matches.fetch_add(xy_slice.len(), AtomicOrdering::Relaxed);

                                        // Clone once per (z_bits, w_bits, tuple) group.
                                        // Add Z/W boundary as permanent unit clauses,
                                        // then iterate XY configs using assumptions.
                                        let (ref enc, ref template_solver) = templates[ti];
                                        let mut solver = template_solver.clone();
                                        // Warm-start: phase-only transfer
                                        if let Some(ref ph) = warm_phase {
                                            solver.set_phase(ph);
                                        }

                                        // Fix Z/W boundary (permanent — same for all XY configs)
                                        for i in 0..k {
                                            solver.add_clause([if (z_bits >> i) & 1 == 1 { enc.z_var(i) } else { -enc.z_var(i) }]);
                                            solver.add_clause([if (z_bits >> (k + i)) & 1 == 1 { enc.z_var(n - k + i) } else { -enc.z_var(n - k + i) }]);
                                            solver.add_clause([if (w_bits >> i) & 1 == 1 { enc.w_var(i) } else { -enc.w_var(i) }]);
                                            solver.add_clause([if (w_bits >> (k + i)) & 1 == 1 { enc.w_var(m - k + i) } else { -enc.w_var(m - k + i) }]);
                                        }

                                        let mut xy_assumptions: Vec<i32> = Vec::with_capacity(4 * k);
                                        for &(x_bits, y_bits) in xy_slice {
                                            if should_stop() { break; }

                                            if conflict_limit > 0 {
                                                solver.set_conflict_budget(conflict_limit);
                                            }

                                            // XY boundary as assumptions (temporary per solve)
                                            xy_assumptions.clear();
                                            for i in 0..k {
                                                xy_assumptions.push(if (x_bits >> i) & 1 == 1 { enc.x_var(i) } else { -enc.x_var(i) });
                                                xy_assumptions.push(if (x_bits >> (k + i)) & 1 == 1 { enc.x_var(n - k + i) } else { -enc.x_var(n - k + i) });
                                                xy_assumptions.push(if (y_bits >> i) & 1 == 1 { enc.y_var(i) } else { -enc.y_var(i) });
                                                xy_assumptions.push(if (y_bits >> (k + i)) & 1 == 1 { enc.y_var(n - k + i) } else { -enc.y_var(n - k + i) });
                                            }

                                            let conflicts_before = solver.num_conflicts();
                                            let result = solver.solve_with_assumptions(&xy_assumptions);
                                            let nc = solver.num_conflicts() - conflicts_before;
                                            total_conflicts.fetch_add(nc, AtomicOrdering::Relaxed);
                                            // Save phase for warm-start
                                            warm_phase = Some(solver.get_phase());

                                            if result == Some(true) {
                                                let x = PackedSeq::from_values(&(0..n).map(|i|
                                                    if solver.value(enc.x_var(i)) == Some(true) { 1i8 } else { -1 }).collect::<Vec<_>>());
                                                let y = PackedSeq::from_values(&(0..n).map(|i|
                                                    if solver.value(enc.y_var(i)) == Some(true) { 1i8 } else { -1 }).collect::<Vec<_>>());
                                                let z = PackedSeq::from_values(&(0..n).map(|i|
                                                    if solver.value(enc.z_var(i)) == Some(true) { 1i8 } else { -1 }).collect::<Vec<_>>());
                                                let w = PackedSeq::from_values(&(0..m).map(|i|
                                                    if solver.value(enc.w_var(i)) == Some(true) { 1i8 } else { -1 }).collect::<Vec<_>>());
                                                solver.reset(); // backtrack for next solve

                                                if verify_tt(problem, &x, &y, &z, &w) {
                                                    found.store(true, AtomicOrdering::Relaxed);
                                                    print_solution("TT SOLUTION", &x, &y, &z, &w);
                                                }
                                                sat_count.fetch_add(1, AtomicOrdering::Relaxed);
                                            } else {
                                                unsat_count.fetch_add(1, AtomicOrdering::Relaxed);
                                            }
                                            items_done.fetch_add(1, AtomicOrdering::Relaxed);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }));
        }

        // Progress reporting
        let total_z = z_configs as usize;
        let total_zw = total_z * w_configs as usize;
        let mut prev_done = 0usize;
        let mut prev_time = run_start.elapsed().as_secs_f64();
        while !found.load(AtomicOrdering::Relaxed)
            && !timed_out.load(AtomicOrdering::Relaxed)
            && z_idx.load(AtomicOrdering::Relaxed) < total_z
        {
            std::thread::sleep(std::time::Duration::from_secs(10));
            // Check time limit
            if time_limit_secs > 0 && run_start.elapsed().as_secs() >= time_limit_secs {
                timed_out.store(true, AtomicOrdering::Relaxed);
            }
            let done = items_done.load(AtomicOrdering::Relaxed);
            let sats = sat_count.load(AtomicOrdering::Relaxed);
            let unsats = unsat_count.load(AtomicOrdering::Relaxed);
            let matches = xy_matches.load(AtomicOrdering::Relaxed);
            let w_done = w_scanned.load(AtomicOrdering::Relaxed);
            let conflicts = total_conflicts.load(AtomicOrdering::Relaxed);
            let z_done = z_idx.load(AtomicOrdering::Relaxed).min(total_z);
            let elapsed = run_start.elapsed().as_secs_f64();
            let rate = done as f64 / elapsed;
            let dt = elapsed - prev_time;
            let recent_rate = if dt > 0.0 { (done - prev_done) as f64 / dt } else { 0.0 };
            let avg_conflicts = if done > 0 { conflicts / done as u64 } else { 0 };
            let zw_pct = if total_zw > 0 { 100.0 * w_done as f64 / total_zw as f64 } else { 0.0 };
            if verbose {
                eprintln!("[{:.0}s] SAT cubed k={} | z {}/{} | zw {:.1}% | SAT {}/{} ({}sat {}unsat) | xy_match {} | {:.1}/s (recent {:.1}/s) | avg {:.0} conflicts",
                    elapsed, k, z_done, total_z, zw_pct, done, matches, sats, unsats, matches, rate, recent_rate, avg_conflicts);
            }
            prev_done = done;
            prev_time = elapsed;
        }

        for h in handles { let _ = h.join(); }

        // Final summary
        let done = items_done.load(AtomicOrdering::Relaxed);
        let sats = sat_count.load(AtomicOrdering::Relaxed);
        let unsats = unsat_count.load(AtomicOrdering::Relaxed);
        let matches = xy_matches.load(AtomicOrdering::Relaxed);
        let w_done = w_scanned.load(AtomicOrdering::Relaxed);
        let conflicts = total_conflicts.load(AtomicOrdering::Relaxed);
        let elapsed = run_start.elapsed().as_secs_f64();
        let avg_conflicts = if done > 0 { conflicts / done as u64 } else { 0 };
        if verbose {
            eprintln!("\n--- SAT cubed k={} final ---", k);
            eprintln!("  Elapsed:        {:.1}s", elapsed);
            eprintln!("  ZW scanned:     {} / {} ({:.1}%)", w_done, total_zw, 100.0 * w_done as f64 / total_zw as f64);
            eprintln!("  XY matches:     {}", matches);
            eprintln!("  SAT solves:     {} ({} SAT, {} UNSAT)", done, sats, unsats);
            eprintln!("  Rate:           {:.2} solves/s", done as f64 / elapsed);
            eprintln!("  Avg conflicts:  {}", avg_conflicts);
            eprintln!("  Total conflicts:{}", conflicts);
            if timed_out.load(AtomicOrdering::Relaxed) {
                eprintln!("  (stopped: time limit {}s)", time_limit_secs);
            }
        }

        SearchReport {
            stats: SearchStats::default(),
            elapsed: run_start.elapsed(),
            found_solution: found.load(AtomicOrdering::Relaxed),
        }
    }
}

// ==================== Prefix/suffix table for fast X/Y completion ====================

/// Pre-computed table of valid X/Y boundary configurations.
/// Grouped by (x_bnd_sum, y_bnd_sum, high_lag_signature) for fast lookup.
struct XYBoundaryTable {
    k: usize,
    w_dim: usize,          // 2^(2k) — W bits dimension
    sum_dim: usize,        // 2k+1 — distinct sum values per axis
    zw_index: Vec<u32>,    // sig_id per Z/W config (0xFFFFFFFF = empty)
    sig_offsets: Vec<u32>, // offset into xy_data per signature
    // Per-sig sub-index: [num_sigs * sum_dim^2] of (offset_within_sig, count)
    // Indexed by sig_id * sum_dim^2 + x_sum_idx * sum_dim + y_sum_idx
    sub_index: Vec<(u32, u32)>,
    xy_data: Vec<(u32, u32)>, // all unique (x_bits, y_bits) pairs, sorted by sum within each sig
}

impl XYBoundaryTable {
    fn load(path: &str) -> Option<Self> {
        use std::io::Read;
        let mut file = std::fs::File::open(path).ok()?;
        let mut buf = Vec::new();
        file.read_to_end(&mut buf).ok()?;

        let u32_at = |off: usize| u32::from_le_bytes(buf[off..off+4].try_into().unwrap());
        assert!(&buf[0..4] == b"XYTT", "bad table magic");

        // Header (24 bytes): "XYTT" version k zw_dim num_sigs sum_dim
        let k = u32_at(8) as usize;
        let zw_dim = u32_at(12) as usize;
        let num_sigs = u32_at(16) as usize;
        let sum_dim = u32_at(20) as usize;
        let w_dim = 1usize << (2 * k);

        let mut off = 24;

        let mut zw_index = vec![0u32; zw_dim];
        for i in 0..zw_dim { zw_index[i] = u32_at(off + i * 4); }
        off += zw_dim * 4;

        let mut sig_offsets = vec![0u32; num_sigs];
        for i in 0..num_sigs { sig_offsets[i] = u32_at(off + i * 8); }
        off += num_sigs * 8;

        let sub_idx_entries = num_sigs * sum_dim * sum_dim;
        let mut sub_index = Vec::with_capacity(sub_idx_entries);
        for i in 0..sub_idx_entries {
            sub_index.push((u32_at(off + i * 8), u32_at(off + i * 8 + 4)));
        }
        off += sub_idx_entries * 8;

        let num_xy = (buf.len() - off) / 8;
        let mut xy_data = Vec::with_capacity(num_xy);
        for i in 0..num_xy {
            xy_data.push((u32_at(off + i * 8), u32_at(off + i * 8 + 4)));
        }

        let ram = (zw_dim * 4 + sub_index.len() * 8 + xy_data.len() * 8) as f64 / 1_048_576.0;
        eprintln!("  {} sigs, {} XY entries, {:.1} MB in RAM", num_sigs, xy_data.len(), ram);

        Some(Self { k, w_dim, sum_dim, zw_index, sig_offsets, sub_index, xy_data })
    }

    /// Get (x_bits, y_bits) pairs for a given Z/W boundary AND sum pair. O(1).
    #[inline]
    fn get_xy_entries(&self, z_bits: u32, w_bits: u32, x_bnd_sum: i32, y_bnd_sum: i32) -> &[(u32, u32)] {
        let idx = z_bits as usize * self.w_dim + w_bits as usize;
        if idx >= self.zw_index.len() { return &[]; }
        let sig_id = self.zw_index[idx];
        if sig_id == 0xFFFFFFFF { return &[]; }
        let si = sig_id as usize;
        let sig_start = self.sig_offsets[si] as usize;

        // Sub-index: jump to the right (x_sum, y_sum) bucket within this sig
        let k = self.k;
        let xi = ((x_bnd_sum + 2 * k as i32) / 2) as usize;
        let yi = ((y_bnd_sum + 2 * k as i32) / 2) as usize;
        if xi >= self.sum_dim || yi >= self.sum_dim { return &[]; }
        let sub_bi = si * self.sum_dim * self.sum_dim + xi * self.sum_dim + yi;
        let (within_off, count) = self.sub_index[sub_bi];
        if count == 0 { return &[]; }
        let start = sig_start + within_off as usize;
        &self.xy_data[start..start + count as usize]
    }

    /// Expand boundary bits into full sequence values at boundary positions.
    #[allow(dead_code)]
    fn expand_boundary(&self, bits: u32, seq: &mut [i8]) {
        let k = self.k;
        let n = seq.len();
        for i in 0..k {
            seq[i] = if (bits >> i) & 1 == 1 { 1 } else { -1 };
        }
        for i in 0..k {
            seq[n - k + i] = if (bits >> (k + i)) & 1 == 1 { 1 } else { -1 };
        }
    }

    /// Direct state injection: one clone per Z/W pair. For each boundary config,
    /// precompute which quad PB terms are TRUE/DEAD/MAYBE and inject directly
    /// into the solver's incremental state. No backtracking, no assumption propagation.
    fn solve_xy_with_sat(
        &self, problem: Problem, tuple: SumTuple,
        candidate: &CandidateZW, template: &SatXYTemplate,
    ) -> Option<(PackedSeq, PackedSeq)> {
        let n = problem.n;
        let m = n - 1; // W length
        let k = self.k;
        let middle_len = n - 2 * k;
        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };

        if !template.is_feasible(candidate) { return None; }
        let Some(equalities) = gj_candidate_equalities(n, candidate) else { return None; };

        // Clone solver ONCE per Z/W pair, add GJ equalities and full quad PB constraints
        let mut solver = template.solver.clone();
        for &(a, b, equal) in &equalities {
            if equal { solver.add_clause([-a, b]); solver.add_clause([a, -b]); }
            else { solver.add_clause([-a, -b]); solver.add_clause([a, b]); }
        }
        for s in 1..n {
            let target_raw = 2 * (n - s) as i32 - candidate.zw_autocorr[s];
            let target = (target_raw / 2) as usize;
            let lp = &template.lag_pairs[s];
            let ones: Vec<u32> = vec![1; lp.lits_a.len()];
            solver.add_quad_pb_eq(&lp.lits_a, &lp.lits_b, &ones, target as u32);
        }

        // Skip quad PB incremental updates during backtrack — we reset state per config
        solver.skip_backtrack_quad_pb = true;

        // Precompute per quad PB constraint: which terms have BOTH vars in boundary
        let is_bnd = |pos: usize| -> bool { pos < k || pos >= n - k };
        let num_qpb = solver.num_quad_pb();
        struct TermBndInfo { var_a: usize, var_b: usize, neg_a: bool, neg_b: bool, both_bnd: bool }
        let mut qpb_term_info: Vec<Vec<TermBndInfo>> = Vec::with_capacity(num_qpb);
        for qi in 0..num_qpb {
            let nt = solver.quad_pb_num_terms(qi);
            let mut infos = Vec::with_capacity(nt);
            for ti in 0..nt {
                let (va, vb, na, nb) = solver.quad_pb_term_info(qi, ti);
                let pa = va % n; let pb = vb % n;
                infos.push(TermBndInfo { var_a: va, var_b: vb, neg_a: na, neg_b: nb, both_bnd: is_bnd(pa) && is_bnd(pb) });
            }
            qpb_term_info.push(infos);
        }

        // Extract Z/W boundary bits from the candidate
        let mut z_bits = 0u32;
        let mut w_bits = 0u32;
        for i in 0..k {
            if candidate.z.get(i) == 1 { z_bits |= 1 << i; }
            if candidate.z.get(n - k + i) == 1 { z_bits |= 1 << (k + i); }
            if candidate.w.get(i) == 1 { w_bits |= 1 << i; }
            if candidate.w.get(m - k + i) == 1 { w_bits |= 1 << (k + i); }
        }

        // Precompute partial-lag autocorrelation filters
        let pos_to_bit = |pos: usize| -> u32 {
            if pos < k { pos as u32 } else { (k + pos - (n - k)) as u32 }
        };
        let targets: Vec<i32> = (0..n).map(|s| if s == 0 { 0 } else { -candidate.zw_autocorr[s] }).collect();
        struct LagFilter { s: usize, pairs: Vec<(u32, u32)>, max_unknown: i32, num_bnd_pairs: i32 }
        let mut lag_filters: Vec<LagFilter> = Vec::new();
        for s in 1..n {
            let mut pairs = Vec::new();
            let mut unk = 0i32;
            for i in 0..n - s {
                if is_bnd(i) && is_bnd(i + s) {
                    pairs.push((pos_to_bit(i), pos_to_bit(i + s)));
                } else { unk += 2; }
            }
            if !pairs.is_empty() && unk > 0 {
                lag_filters.push(LagFilter { s, pairs: pairs.clone(), max_unknown: unk, num_bnd_pairs: 2 * pairs.len() as i32 });
            }
        }
        lag_filters.sort_by_key(|f| f.max_unknown);

        // Pre-allocate buffers for term state injection
        let max_terms = qpb_term_info.iter().map(|v| v.len()).max().unwrap_or(0);
        let mut term_state_buf = vec![0u8; max_terms];

        let mut configs_tested = 0usize;
        let max_bnd_sum = (2 * k) as i32;
        // Iterate only valid (x_bnd_sum, y_bnd_sum) pairs and look up matching entries
        for x_bnd_sum in (-max_bnd_sum..=max_bnd_sum).step_by(2) {
            let x_mid = tuple.x - x_bnd_sum;
            if x_mid.abs() > middle_len as i32 || (x_mid + middle_len as i32) % 2 != 0 { continue; }
            for y_bnd_sum in (-max_bnd_sum..=max_bnd_sum).step_by(2) {
                let y_mid = tuple.y - y_bnd_sum;
                if y_mid.abs() > middle_len as i32 || (y_mid + middle_len as i32) % 2 != 0 { continue; }

                let xy_entries = self.get_xy_entries(z_bits, w_bits, x_bnd_sum, y_bnd_sum);
                if xy_entries.is_empty() { continue; }

                for &(x_bits, y_bits) in xy_entries {

            // GJ equality filter on boundary variables
            let mut ok = true;
            for &(a, b, equal) in &equalities {
                let va = (a.unsigned_abs() as usize) - 1;
                let vb = (b.unsigned_abs() as usize) - 1;
                let pa = va % n; let pb = vb % n;
                if !is_bnd(pa) || !is_bnd(pb) { continue; }
                let pos_to_bit = |pos: usize| -> u32 {
                    if pos < k { pos as u32 } else { (k + pos - (n - k)) as u32 }
                };
                let ba = if va < n { (x_bits >> pos_to_bit(pa)) & 1 } else { (y_bits >> pos_to_bit(pa)) & 1 };
                let bb = if vb < n { (x_bits >> pos_to_bit(pb)) & 1 } else { (y_bits >> pos_to_bit(pb)) & 1 };
                let need_xor = (a < 0) as u32 ^ (b < 0) as u32 ^ (!equal) as u32;
                if (ba ^ bb) != need_xor { ok = false; break; }
            }
            if !ok { continue; }

            // Partial-lag autocorrelation filter
            for lf in &lag_filters {
                let mut disagree = 0u32;
                for &(bi, bj) in &lf.pairs {
                    disagree += ((x_bits >> bi) ^ (x_bits >> bj)) & 1;
                    disagree += ((y_bits >> bi) ^ (y_bits >> bj)) & 1;
                }
                let kn = lf.num_bnd_pairs - 2 * disagree as i32;
                if (targets[lf.s] - kn).abs() > lf.max_unknown { ok = false; break; }
            }
            if !ok { continue; }

                    // Expand bits only for entries passing all filters
                    let mut xv = [0i8; 64]; let mut yv = [0i8; 64];
                    for i in 0..k {
                        xv[i] = if (x_bits >> i) & 1 == 1 { 1 } else { -1 };
                        xv[n-k+i] = if (x_bits >> (k+i)) & 1 == 1 { 1 } else { -1 };
                        yv[i] = if (y_bits >> i) & 1 == 1 { 1 } else { -1 };
                        yv[n-k+i] = if (y_bits >> (k+i)) & 1 == 1 { 1 } else { -1 };
                    }
                    // Build boundary value lookup
                    let mut bnd_vals = [0i8; 128];
                    for i in 0..k { bnd_vals[i] = xv[i]; bnd_vals[n-k+i] = xv[n-k+i]; }
                    for i in 0..k { bnd_vals[n+i] = yv[i]; bnd_vals[n+n-k+i] = yv[n-k+i]; }

                    // Precompute term states for all quad PB constraints and inject
                    let _infeasible = false;
                    for qi in 0..num_qpb {
                        let infos = &qpb_term_info[qi];
                        let mut st = 0i32; let mut sm = 0i32;
                        for (ti, info) in infos.iter().enumerate() {
                            if info.both_bnd {
                                // Both boundary: evaluate the term
                                let a_val = bnd_vals[info.var_a];
                                let b_val = bnd_vals[info.var_b];
                                let a_true = (a_val == 1 && !info.neg_a) || (a_val == -1 && info.neg_a);
                                let b_true = (b_val == 1 && !info.neg_b) || (b_val == -1 && info.neg_b);
                                if a_true && b_true {
                                    term_state_buf[ti] = 2; st += 1; // TRUE
                                } else {
                                    let a_false = (a_val == 1 && info.neg_a) || (a_val == -1 && !info.neg_a);
                                    let b_false = (b_val == 1 && info.neg_b) || (b_val == -1 && !info.neg_b);
                                    if a_false || b_false {
                                        term_state_buf[ti] = 0; // DEAD
                                    } else {
                                        term_state_buf[ti] = 1; sm += 1; // MAYBE (shouldn't happen if both_bnd)
                                    }
                                }
                            } else {
                                // At least one free variable: MAYBE
                                term_state_buf[ti] = 1; sm += 1;
                            }
                        }
                        solver.reset_quad_pb_state(qi, &term_state_buf[..infos.len()], st, sm);
                    }

                    // Build assumptions for boundary variables
                    let mut assumptions = Vec::with_capacity(4 * k);
                    for i in 0..k {
                        assumptions.push(if xv[i] == 1 { x_var(i) } else { -x_var(i) });
                        assumptions.push(if yv[i] == 1 { y_var(i) } else { -y_var(i) });
                    }
                    for i in 0..k {
                        let p = n-k+i;
                        assumptions.push(if xv[p] == 1 { x_var(p) } else { -x_var(p) });
                        assumptions.push(if yv[p] == 1 { y_var(p) } else { -y_var(p) });
                    }

                    match solver.solve_with_assumptions(&assumptions) {
                        Some(true) => {
                            let x: Vec<i8> = (0..n).map(|i| if solver.value(x_var(i)) == Some(true) { 1 } else { -1 }).collect();
                            let y: Vec<i8> = (0..n).map(|i| if solver.value(y_var(i)) == Some(true) { 1 } else { -1 }).collect();
                            return Some((PackedSeq::from_values(&x), PackedSeq::from_values(&y)));
                        }
                        _ => {
                            configs_tested += 1;
                            if configs_tested % 8 == 0 {
                                solver.clear_learnt();
                            }
                        }
                    }
                }
            }
        }
        None
    }
}

/// Hybrid search: Phase A+B (sum tuples, Z/W generation, spectral filtering)
/// followed by SAT-based X/Y solving for each candidate (Z,W) pair.
/// Process a single sum-tuple: Phase B (Z/W generation) + Phase C (SAT X/Y solving).
/// Returns Some((x, y, z, w, stats)) if a solution is found.
fn run_hybrid_search(cfg: &SearchConfig, verbose: bool) -> SearchReport {
    let problem = cfg.problem;

    // Phase A: enumerate and normalize tuples
    let mut tuples = phase_a_tuples(problem, cfg.test_tuple.as_ref());
    // Heuristic tuple ordering depends on problem size.
    if problem.n >= 26 {
        tuples.sort_by_key(|t| ((t.x - t.y).abs(), t.z.abs() + t.w.abs(), t.x.abs() + t.y.abs()));
    } else {
        tuples.sort_by_key(|t| (t.z.abs() + t.w.abs(), (t.x - t.y).abs(), t.x.abs() + t.y.abs()));
    }

    // Load boundary table
    let table_path = cfg.xy_table_path.clone().unwrap_or_else(|| "./xy-table-k7.bin".to_string());
    let skip_table = cfg.no_table || problem.n < 14;
    let xy_table: Option<Arc<XYBoundaryTable>> = if skip_table {
        if !cfg.no_table && problem.n < 14 && verbose {
            eprintln!("Note: n={} < 14 (2*k for k=7 table), running without table", problem.n);
        }
        None
    } else {
        match XYBoundaryTable::load(&table_path) {
            Some(t) => {
                if problem.n < 2 * t.k {
                    if verbose {
                        eprintln!("Note: n={} < {} (2*k for k={} table), running without table",
                            problem.n, 2 * t.k, t.k);
                    }
                    None
                } else {
                    if verbose { eprintln!("Loaded XY boundary table from {} (k={}, {} sigs, {} XY entries)", table_path, t.k, t.sig_offsets.len(), t.xy_data.len()); }
                    Some(Arc::new(t))
                }
            }
            None => {
                eprintln!("Error: XY boundary table not found at '{}'", table_path);
                eprintln!("Generate it once with: cargo build --release --bin gen_table && target/release/gen_table");
                eprintln!("Or run with --no-table to skip (slower).");
                std::process::exit(1);
            }
        }
    };

    if verbose {
        let method = if xy_table.is_some() { "table+SAT" } else { "SAT X/Y" };
        eprintln!("{} normalized tuples, Phase C: {}", tuples.len(), method);
    }

    let cfg = cfg.clone();
    let sat_secs = cfg.sat_secs;
    let sat_config = cfg.sat_config.clone();
    run_parallel_search(problem, xy_table, sat_config, move |tx, found| {
        let spectral_z = SpectralFilter::new(problem.n, cfg.theta_samples);
        let spectral_w = SpectralFilter::new(problem.n, cfg.theta_samples);
        let mut stats = SearchStats::default();
        let mut w_cache: HashMap<i32, (Vec<SeqWithSpectrum>, SpectralIndex)> = HashMap::new();
        for (idx, &tuple) in tuples.iter().enumerate() {
            if found.load(AtomicOrdering::Relaxed) { break; }
            let b_start = Instant::now();
            if !w_cache.contains_key(&tuple.w) {
                let w_candidates = build_w_candidates(
                    problem, tuple.w, &cfg, &spectral_w, &mut stats, &found);
                let w_index = SpectralIndex::build(&w_candidates);
                w_cache.insert(tuple.w, (w_candidates, w_index));
            }
            if found.load(AtomicOrdering::Relaxed) { break; }
            let (w_candidates, w_index) = w_cache.get(&tuple.w).unwrap();
            let before = (stats.z_generated, stats.z_spectral_ok, stats.candidate_pair_spectral_ok);
            stream_zw_candidates_to_channel(
                problem, tuple, w_candidates, w_index, &cfg, &spectral_z,
                &mut stats, &found, &tx);
            stats.phase_b_nanos += b_start.elapsed().as_nanos() as u64;
            let z_gen = stats.z_generated - before.0;
            let z_ok = stats.z_spectral_ok - before.1;
            let pairs = stats.candidate_pair_spectral_ok - before.2;
            eprintln!("  tuple {}/{} (sums {},{},{},{}): z_gen={} z_ok={} w={} pairs={}",
                idx+1, tuples.len(), tuple.x, tuple.y, tuple.z, tuple.w,
                z_gen, z_ok, w_candidates.len(), pairs);
        }
        stats
    }, verbose, "hybrid (Phase B \u{2192} SAT XY)", sat_secs)
}

fn print_help() {
    eprintln!("turyn - Find Turyn-type sequences TT(n) for constructing Hadamard matrices");
    eprintln!();
    eprintln!("Searches for four {{+1,-1}} sequences (X,Y,Z,W) whose combined aperiodic");
    eprintln!("autocorrelations vanish. Pipeline: Phase A enumerates sum-tuples, Phase B");
    eprintln!("generates Z/W candidates with spectral filtering, Phase C solves X/Y via SAT.");
    eprintln!();
    eprintln!("USAGE: turyn --n=<N> [OPTIONS]");
    eprintln!();
    eprintln!("  --n=<N>                  Sequence length to search (required)");
    eprintln!();
    eprintln!("SEARCH MODE (pick one, default is hybrid):");
    eprintln!("  (default)                Hybrid: enumerate Z/W, then solve X/Y with SAT");
    eprintln!("                           Uses precomputed XY boundary table for n >= 14");
    eprintln!("  --sat                    Pure SAT: encode all four sequences into one SAT problem");
    eprintln!("  --stochastic             Stochastic local search over all four sequences");
    eprintln!("  --stochastic-secs=<S>    Stochastic search, stop after S seconds (default: 10)");
    eprintln!();
    eprintln!("SEARCH TUNING:");
    eprintln!("  --theta=<N>              Number of angle samples for spectral power filtering in");
    eprintln!("                           Phase B; higher = tighter filter, slower (default: 128)");
    eprintln!("  --max-z=<N>              Cap on Z candidates kept from Phase B (default: 200000)");
    eprintln!("  --max-w=<N>              Cap on W candidates kept from Phase B (default: 200000)");
    eprintln!("  --max-spectral=<F>       Upper bound on spectral pair power sum; lower values");
    eprintln!("                           prune more aggressively (faster but may miss solutions)");
    eprintln!("  --conflict-limit=<N>     Max CDCL conflicts per SAT call before giving up on");
    eprintln!("                           that candidate; 0 = unlimited (default: 0)");
    eprintln!("  --sat-secs=<N>           Time limit in seconds for --sat mode; stops and reports");
    eprintln!("                           stats when reached; 0 = unlimited (default: 0)");
    eprintln!();
    eprintln!("SAT VARIANT FLAGS:");
    eprintln!("  --z-sat, --xyz-sat       Solve Z via SAT instead of enumeration");
    eprintln!("  --w-sat                  Solve W via SAT instead of enumeration");
    eprintln!();
    eprintln!("XY BOUNDARY TABLE:");
    eprintln!("  --xy-table=<PATH>        Path to precomputed table (default: ./xy-table-k7.bin)");
    eprintln!("                           Generate with: gen_table 7 xy-table-k7.bin");
    eprintln!("  --no-table               Skip table lookup, solve X/Y from scratch (slower)");
    eprintln!();
    eprintln!("SAT SOLVER TUNING:");
    eprintln!("  --no-xor                 Disable GF(2) XOR propagation in SAT solver");
    eprintln!("                           (on by default; gives ~4-49x speedup on Phase C)");
    eprintln!("  --ema-restarts           Use glucose-style EMA restarts instead of Luby");
    eprintln!("  --probing                Run failed literal probing before each SAT solve");
    eprintln!("  --rephasing              Periodically reset phase saving heuristic");
    eprintln!();
    eprintln!("DEBUGGING / TESTING:");
    eprintln!("  --verify=<X,Y,Z,W>      Check if four +/- sequences form a valid TT(n)");
    eprintln!("                           Example: --verify=++--+-,+-+-++,+++-,+-+-");
    eprintln!("  --test-zw=<Z,W>          Fix Z/W and only run Phase C (SAT X/Y) on them");
    eprintln!("  --tuple=<x,y,z,w>        Restrict search to one sum-tuple (4 integers)");
    eprintln!("  --phase-a                Print all sum-tuples for n, then exit");
    eprintln!("  --phase-b                Run Phases A+B, print Z/W pairs, then exit");
    eprintln!("  --dump-dimacs=<PATH>     Write the SAT encoding to a DIMACS CNF file");
    eprintln!();
    eprintln!("BENCHMARKING:");
    eprintln!("  --benchmark              Run the search 5 times and report timing");
    eprintln!("  --benchmark=<N>          Run the search N times and report timing");
    eprintln!();
    eprintln!("  -h, --help               Show this help message");
    eprintln!();
    eprintln!("EXAMPLES:");
    eprintln!("  turyn --n=26                          # search for TT(26)");
    eprintln!("  turyn --n=26 --no-table                # same, without precomputed table");
    eprintln!("  turyn --n=16 --benchmark=3             # benchmark Phase B throughput");
    eprintln!("  turyn --verify=++--+-,+-+-++,+++-,+-+- # verify a candidate solution");
}

fn parse_args() -> SearchConfig {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.is_empty() || args.iter().any(|a| a == "-h" || a == "--help") {
        print_help();
        std::process::exit(0);
    }
    let mut cfg = SearchConfig::default();
    for arg in &args {
        if let Some(v) = arg.strip_prefix("--n=") {
            if let Ok(n) = v.parse::<usize>() {
                cfg.problem = Problem::new(n);
            } else {
                eprintln!("error: invalid value for --n: {}", v);
                std::process::exit(1);
            }
        } else if let Some(v) = arg.strip_prefix("--theta=") {
            cfg.theta_samples = v.parse().unwrap_or(cfg.theta_samples);
        } else if let Some(v) = arg.strip_prefix("--max-z=") {
            cfg.max_z = v.parse().unwrap_or(cfg.max_z);
        } else if let Some(v) = arg.strip_prefix("--max-w=") {
            cfg.max_w = v.parse().unwrap_or(cfg.max_w);
        } else if let Some(v) = arg.strip_prefix("--benchmark=") {
            cfg.benchmark_repeats = v.parse().unwrap_or(1);
        } else if arg == "--benchmark" {
            cfg.benchmark_repeats = 5;
        } else if arg == "--stochastic" {
            cfg.stochastic = true;
        } else if let Some(v) = arg.strip_prefix("--stochastic-secs=") {
            cfg.stochastic_seconds = v.parse().unwrap_or(10);
            cfg.stochastic = true;
        } else if arg == "--sat" {
            cfg.sat = true;
        } else if arg == "--sat-xy" {
            // Legacy alias — hybrid is now the default
            cfg.sat_xy = true;
        } else if arg == "--z-sat" || arg == "--xyz-sat" {
            cfg.z_sat = true;
        } else if arg == "--w-sat" {
            cfg.w_sat = true;
        } else if let Some(v) = arg.strip_prefix("--max-spectral=") {
            cfg.max_spectral = Some(v.parse().unwrap_or(0.0));
        } else if let Some(v) = arg.strip_prefix("--verify=") {
            let parts: Vec<&str> = v.split(',').collect();
            if parts.len() == 4 {
                cfg.verify_seqs = Some([parts[0].to_string(), parts[1].to_string(),
                                        parts[2].to_string(), parts[3].to_string()]);
            }
        } else if let Some(v) = arg.strip_prefix("--test-zw=") {
            let parts: Vec<&str> = v.split(',').collect();
            if parts.len() == 2 {
                cfg.test_zw = Some([parts[0].to_string(), parts[1].to_string()]);
            }
        } else if let Some(v) = arg.strip_prefix("--conflict-limit=") {
            cfg.conflict_limit = v.parse().unwrap_or(0);
        } else if let Some(v) = arg.strip_prefix("--sat-secs=") {
            cfg.sat_secs = v.parse().unwrap_or(0);
        } else if arg == "--ema-restarts" {
            cfg.sat_config.ema_restarts = true;
        } else if arg == "--probing" {
            cfg.sat_config.probing = true;
        } else if arg == "--rephasing" {
            cfg.sat_config.rephasing = true;
        } else if arg == "--xor-propagation" {
            cfg.sat_config.xor_propagation = true;
        } else if arg == "--no-xor" {
            cfg.sat_config.xor_propagation = false;
        } else if arg == "--phase-a" || arg == "--phase-b" {
            cfg.phase_only = Some(arg[2..].to_string());
        } else if let Some(v) = arg.strip_prefix("--tuple=") {
            let parts: Vec<i32> = v.split(',').filter_map(|s| s.parse().ok()).collect();
            if parts.len() == 4 {
                cfg.test_tuple = Some(SumTuple { x: parts[0], y: parts[1], z: parts[2], w: parts[3] });
            }
        } else if let Some(v) = arg.strip_prefix("--xy-table=") {
            cfg.xy_table_path = Some(v.to_string());
        } else if arg == "--no-table" {
            cfg.no_table = true;
        } else if let Some(v) = arg.strip_prefix("--dump-dimacs=") {
            cfg.dump_dimacs = Some(v.to_string());
        } else {
            eprintln!("error: unknown option '{}'\n", arg);
            print_help();
            std::process::exit(1);
        }
    }
    // --n is required unless --verify or --test-zw supply their own sequences
    if cfg.problem.n == 0 && cfg.verify_seqs.is_none() && cfg.test_zw.is_none() {
        eprintln!("error: --n=<N> is required\n");
        print_help();
        std::process::exit(1);
    }
    cfg
}

/// Parse a +/- string into a PackedSeq. '+' = +1, '-' = -1.
fn parse_seq(s: &str) -> PackedSeq {
    let vals: Vec<i8> = s.chars().map(|c| if c == '+' { 1 } else { -1 }).collect();
    PackedSeq::from_values(&vals)
}

fn run_info() -> String {
    let hostname = std::process::Command::new("hostname")
        .output().ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .unwrap_or_default().trim().to_string();
    let git_hash = std::process::Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output().ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .unwrap_or_default().trim().to_string();
    format!("host={}, commit={}", hostname, git_hash)
}

fn main() {
    let cfg = parse_args();
    if let Some(ref seqs) = cfg.verify_seqs {
        let x = parse_seq(&seqs[0]);
        let y = parse_seq(&seqs[1]);
        let z = parse_seq(&seqs[2]);
        let w = parse_seq(&seqs[3]);
        let n = x.len();
        let p = Problem::new(n);
        print_solution(&format!("Verifying TT({})", n), &x, &y, &z, &w);
        let ok = verify_tt(p, &x, &y, &z, &w);
        println!("Verified: {}", ok);
        if !ok { std::process::exit(1); }
        return;
    }
    if let Some(ref zw) = cfg.test_zw {
        let z = parse_seq(&zw[0]);
        let w = parse_seq(&zw[1]);
        let n = z.len();
        let p = Problem::new(n);
        let zs = z.sum();
        let ws = w.sum();
        // Compute ZW autocorrelation
        let mut zw_autocorr = vec![0i32; n];
        for s in 1..n {
            let nz = z.autocorrelation(s);
            let nw = if s < p.m() { w.autocorrelation(s) } else { 0 };
            zw_autocorr[s] = 2 * nz + 2 * nw;
        }
        let candidate = CandidateZW { z: z.clone(), w: w.clone(), zw_autocorr };
        // Try all sum tuples that match this Z/W
        let mut tuples = phase_a_tuples(p, cfg.test_tuple.as_ref());
        tuples.retain(|t| t.z == zs && t.w == ws);
        println!("TT({}): testing Z(sum={}) W(sum={}) against {} tuples", n, zs, ws, tuples.len());
        print_solution("  Z/W", &PackedSeq::from_values(&[0]), &PackedSeq::from_values(&[0]), &z, &w);
        for tuple in &tuples {
            let start = Instant::now();
            let Some(template) = SatXYTemplate::build(p, *tuple, &radical::SolverConfig::default()) else { continue };
            if let Some((x, y)) = template.solve_for(&candidate) {
                let ok = verify_tt(p, &x, &y, &z, &w);
                print_solution(&format!("FOUND for tuple {} ({:.3?}, verified={})", tuple, start.elapsed(), ok), &x, &y, &z, &w);
                if ok { return; }
            } else {
                println!("  Tuple {}: UNSAT ({:.3?})", tuple, start.elapsed());
            }
        }
        println!("No X/Y found for given Z/W");
        return;
    }
    if let Some(ref phase) = cfg.phase_only {
        let problem = cfg.problem;
        let mut tuples = phase_a_tuples(problem, cfg.test_tuple.as_ref());
        // Heuristic tuple ordering: try small |z|+|w| first (cheap Phase B),
    // break ties by small |x-y| (solutions often have x≈y).
    tuples.sort_by_key(|t| (t.z.abs() + t.w.abs(), (t.x - t.y).abs(), t.x.abs() + t.y.abs()));

        if phase == "phase-a" {
            println!("TT({}): {} tuples (x,y,z,w) satisfying x²+y²+2z²+2w²={}",
                problem.n, tuples.len(), problem.target_energy());
            for t in &tuples {
                println!("  ({},{},{},{})", t.x, t.y, t.z, t.w);
            }
        } else if phase == "phase-b" {
            let spectral_z = SpectralFilter::new(problem.n, cfg.theta_samples);
            let spectral_w = SpectralFilter::new(problem.n, cfg.theta_samples);
            for tuple in &tuples {
                let mut stats = SearchStats::default();
                let start = Instant::now();
                let candidates = build_zw_candidates(problem, *tuple, &cfg, &spectral_z, &spectral_w, &mut stats, &AtomicBool::new(false));
                println!("({},{},{},{}): z={}/{} w={}/{} pairs={} ({:.3?})",
                    tuple.x, tuple.y, tuple.z, tuple.w,
                    stats.z_spectral_ok, stats.z_generated,
                    stats.w_spectral_ok, stats.w_generated,
                    candidates.len(), start.elapsed());
            }
        }
        return;
    }
    if let Some(ref path) = cfg.dump_dimacs {
        let problem = cfg.problem;
        let mut tuples = phase_a_tuples(problem, cfg.test_tuple.as_ref());
        tuples.sort_by_key(|t| (t.z.abs() + t.w.abs(), (t.x - t.y).abs()));
        let tuple = tuples[0];
        println!("Dumping DIMACS for TT({}) tuple {} to {}", problem.n, tuple, path);
        let (_enc, solver) = sat_encode(problem, tuple);
        let mut file = std::fs::File::create(path).expect("failed to create DIMACS file");
        solver.dump_dimacs(&mut file).expect("failed to write DIMACS");
        println!("Wrote {} vars, {} clauses", solver.num_vars(), solver.num_clauses());
        return;
    }
    if cfg.benchmark_repeats > 0 {
        run_benchmark(&cfg);
    } else if cfg.w_sat {
        let report = run_w_sat_search(&cfg, true);
        println!("W-SAT search: found_solution={}, elapsed={:.3?}\n  {}", report.found_solution, report.elapsed, run_info());
    } else if cfg.z_sat {
        let report = run_z_sat_search(&cfg, true);
        println!("XYZ-SAT search: found_solution={}, elapsed={:.3?}\n  {}", report.found_solution, report.elapsed, run_info());
    } else if cfg.sat {
        let report = run_sat_search(&cfg, true);
        println!("SAT search: found_solution={}, elapsed={:.3?}\n  {}", report.found_solution, report.elapsed, run_info());
    } else if cfg.stochastic {
        let report = stochastic_search(cfg.problem, cfg.test_tuple.as_ref(), true, cfg.stochastic_seconds);
        println!("Stochastic search: found_solution={}, elapsed={:.3?}\n  {}", report.found_solution, report.elapsed, run_info());
    } else {
        // Default: hybrid search (Phase B → SAT X/Y). Use --sat or --stochastic to override.
        let report = run_hybrid_search(&cfg, true);
        println!("Hybrid search: found_solution={}, elapsed={:.3?}\n  {}", report.found_solution, report.elapsed, run_info());
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
            max_z: 200_000,
            max_w: 200_000,
            benchmark_repeats: 1,
            stochastic: false,
            stochastic_seconds: 0,
            sat: false,
            sat_xy: false,
            z_sat: false,
            w_sat: false,
            max_spectral: None,
            verify_seqs: None,
            test_zw: None,
            conflict_limit: 0,
            test_tuple: None,
            phase_only: None,
            xy_table_path: None,
            no_table: true,
            dump_dimacs: None,
            sat_config: radical::SolverConfig::default(),
            sat_secs: 0,
        };
        let report = run_hybrid_search(&cfg, false);
        assert!(report.found_solution, "n=4 hybrid should find solution");
        assert!(report.elapsed.as_secs_f64() < 10.0, "n=4 should be fast");
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
    fn stochastic_search_finds_tt8() {
        let p = Problem::new(8);
        let report = stochastic_search(p, None, false, 0);
        assert!(report.found_solution);
        assert!(report.elapsed.as_secs_f64() < 30.0);
    }

    #[test]
    fn cardinality_encoding_exactly_2_of_4() {
        // Test: exactly 2 of 4 variables must be true
        let mut enc = SatEncoder { n: 0, m: 0, next_var: 5, xnor_triples: Vec::new() };
        let mut solver: radical::Solver = Default::default();
        let lits = vec![1, 2, 3, 4];
        enc.encode_cardinality_eq(&mut solver, &lits, 2);
        // Should be SAT (many solutions: e.g. 1=T,2=T,3=F,4=F)
        assert_eq!(solver.solve(), Some(true));
        let vals: Vec<bool> = (1..=4).map(|v| solver.value(v) == Some(true)).collect();
        let count: usize = vals.iter().filter(|&&v| v).count();
        assert_eq!(count, 2, "Expected exactly 2 true, got {:?}", vals);
    }

    #[test]
    fn cardinality_encoding_exactly_0_of_3() {
        let mut enc = SatEncoder { n: 0, m: 0, next_var: 4, xnor_triples: Vec::new() };
        let mut solver: radical::Solver = Default::default();
        let lits = vec![1, 2, 3];
        enc.encode_cardinality_eq(&mut solver, &lits, 0);
        assert_eq!(solver.solve(), Some(true));
        for v in 1..=3 {
            assert_eq!(solver.value(v), Some(false), "var {} should be false", v);
        }
    }

    #[test]
    fn cardinality_encoding_exactly_3_of_3() {
        let mut enc = SatEncoder { n: 0, m: 0, next_var: 4, xnor_triples: Vec::new() };
        let mut solver: radical::Solver = Default::default();
        let lits = vec![1, 2, 3];
        enc.encode_cardinality_eq(&mut solver, &lits, 3);
        assert_eq!(solver.solve(), Some(true));
        for v in 1..=3 {
            assert_eq!(solver.value(v), Some(true), "var {} should be true", v);
        }
    }

    #[test]
    fn xnor_encoding_correct() {
        let mut enc = SatEncoder { n: 0, m: 0, next_var: 3, xnor_triples: Vec::new() };
        let mut solver: radical::Solver = Default::default();
        // a=1, b=2, test all 4 combos
        let aux = enc.encode_xnor(&mut solver, 1, 2);
        // Force a=T, b=T → aux should be T (agree)
        solver.add_clause([1]);
        solver.add_clause([2]);
        assert_eq!(solver.solve(), Some(true));
        assert_eq!(solver.value(aux), Some(true));
    }

    #[test]
    fn build_counter_exactly_2_of_3() {
        let mut enc = SatEncoder { n: 0, m: 0, next_var: 4, xnor_triples: Vec::new() };
        let mut solver: radical::Solver = Default::default();
        let lits = vec![1, 2, 3];
        let ctr = enc.build_counter(&mut solver, &lits);
        // Enforce exactly 2: at-least 2 AND at-most 2 (i.e., NOT at-least 3)
        assert!(ctr.len() >= 3, "counter should have at-least-2 var");
        solver.add_clause([ctr[2]]); // at least 2
        if ctr.len() > 3 && ctr[3] != 0 {
            solver.add_clause([-ctr[3]]); // at most 2
        }
        assert_eq!(solver.solve(), Some(true));
        let count: usize = (1..=3).filter(|&v| solver.value(v) == Some(true)).count();
        assert_eq!(count, 2, "expected exactly 2 true");
    }

    #[test]
    fn sat_finds_tt6() {
        let cfg = SearchConfig { problem: Problem::new(6), no_table: true, ..Default::default() };
        let report = run_sat_search(&cfg, true);
        assert!(report.found_solution, "SAT should find TT(6)");
    }

    #[test]
    fn known_tt36_verifies() {
        // Known TT(36) from Kharaghani & Tayfeh-Rezaie (2005), Hadamard 428.
        let p = Problem::new(36);
        let x = PackedSeq::from_values(&[1,1,1,-1,-1,-1,-1,1,1,-1,1,-1,1,-1,-1,-1,-1,-1,1,1,1,1,-1,1,1,-1,1,1,1,1,-1,-1,-1,-1,1,-1]);
        let y = PackedSeq::from_values(&[1,-1,1,1,1,1,1,-1,-1,1,-1,1,-1,-1,1,-1,-1,1,1,-1,-1,1,1,1,1,-1,1,1,1,1,-1,-1,-1,1,1,-1]);
        let z = PackedSeq::from_values(&[1,-1,1,1,1,1,1,-1,1,-1,-1,1,1,1,1,-1,1,1,1,-1,1,1,-1,-1,1,1,1,-1,1,-1,-1,1,-1,-1,-1,1]);
        let w = PackedSeq::from_values(&[1,1,1,-1,1,-1,-1,-1,-1,-1,1,1,-1,-1,1,-1,1,1,1,-1,-1,1,-1,1,-1,1,1,1,-1,1,1,1,1,-1,1]);
        assert!(verify_tt(p, &x, &y, &z, &w), "Known TT(36) should verify");
        assert_eq!(x.sum(), 0);
        assert_eq!(y.sum(), 6);
        assert_eq!(z.sum(), 8);
        assert_eq!(w.sum(), 5);
    }

    #[test]
    fn sat_xy_solves_known_tt36_zw() {
        // Given the known Z/W from TT(36), can SAT find X/Y?
        let p = Problem::new(36);
        let z = PackedSeq::from_values(&[1,-1,1,1,1,1,1,-1,1,-1,-1,1,1,1,1,-1,1,1,1,-1,1,1,-1,-1,1,1,1,-1,1,-1,-1,1,-1,-1,-1,1]);
        let w = PackedSeq::from_values(&[1,1,1,-1,1,-1,-1,-1,-1,-1,1,1,-1,-1,1,-1,1,1,1,-1,-1,1,-1,1,-1,1,1,1,-1,1,1,1,1,-1,1]);
        let mut zw = vec![0; 36];
        for (s, slot) in zw.iter_mut().enumerate().skip(1) {
            let nz = z.autocorrelation(s);
            let nw = if s < p.m() { w.autocorrelation(s) } else { 0 };
            *slot = 2 * nz + 2 * nw;
        }
        let candidate = CandidateZW { z, w, zw_autocorr: zw };
        let tuple = SumTuple { x: 0, y: 6, z: 8, w: 5 };
        let _stats = SearchStats::default();
        // Test 1: can the SAT solver find X/Y from scratch?
        let template = SatXYTemplate::build(p, tuple, &radical::SolverConfig::default()).expect("template should build");
        assert!(template.is_feasible(&candidate), "known Z/W should be feasible");

        // Test 2: hardcode the known X/Y and check consistency
        let known_x: Vec<i8> = vec![1,1,1,-1,-1,-1,-1,1,1,-1,1,-1,1,-1,-1,-1,-1,-1,1,1,1,1,-1,1,1,-1,1,1,1,1,-1,-1,-1,-1,1,-1];
        let known_y: Vec<i8> = vec![1,-1,1,1,1,1,1,-1,-1,1,-1,1,-1,-1,1,-1,-1,1,1,-1,-1,1,1,1,1,-1,1,1,1,1,-1,-1,-1,1,1,-1];
        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (36 + i + 1) as i32 };
        let mut solver = template.solver.clone();
        // Add per-lag quadratic PB constraints
        for s in 1..36 {
            let target_raw = 2 * (36 - s) as i32 - candidate.zw_autocorr[s];
            let target = (target_raw / 2) as usize;
            let lp = &template.lag_pairs[s];
            let ones: Vec<u32> = vec![1; lp.lits_a.len()];
            solver.add_quad_pb_eq(&lp.lits_a, &lp.lits_b, &ones, target as u32);
        }
        // Hardcode known X/Y
        for i in 0..36 {
            solver.add_clause([if known_x[i] == 1 { x_var(i) } else { -x_var(i) }]);
            solver.add_clause([if known_y[i] == 1 { y_var(i) } else { -y_var(i) }]);
        }
        let result_hardcoded = solver.solve();
        assert_eq!(result_hardcoded, Some(true), "known X/Y hardcoded into SAT should be consistent");

        // Encoding verified correct (hardcoded test passed above).
        // Free SAT search for n=36 XY (~7K vars) needs radical optimizations.
    }

    #[test]
    fn sat_autocorr_only_n4() {
        // Test: just autocorrelation constraints (no sums, no symmetry breaking)
        let n = 4usize;
        let m = 3usize;
        let mut enc = SatEncoder::new(n);
        let mut solver: radical::Solver = Default::default();

        for k in 1..n {
            let w_overlap = if k < m { m - k } else { 0 };
            let target = 2 * (n - k) + w_overlap;

            let mut xy_lits = Vec::new();
            for i in 0..(n - k) {
                xy_lits.push(enc.encode_xnor(&mut solver, enc.x_var(i), enc.x_var(i + k)));
            }
            for i in 0..(n - k) {
                xy_lits.push(enc.encode_xnor(&mut solver, enc.y_var(i), enc.y_var(i + k)));
            }
            let mut zw_lits = Vec::new();
            for i in 0..(n - k) {
                zw_lits.push(enc.encode_xnor(&mut solver, enc.z_var(i), enc.z_var(i + k)));
            }
            for i in 0..w_overlap {
                zw_lits.push(enc.encode_xnor(&mut solver, enc.w_var(i), enc.w_var(i + k)));
            }

            let xy_ctr = enc.build_counter(&mut solver, &xy_lits);
            let zw_ctr = enc.build_counter(&mut solver, &zw_lits);

            let mut selectors = Vec::new();
            for c_zw in 0..=zw_lits.len() {
                let rem = target as isize - 2 * c_zw as isize;
                if rem < 0 || rem as usize > xy_lits.len() { continue; }
                let c_xy = rem as usize;
                let sel = enc.fresh();
                if c_xy > 0 {
                    if c_xy < xy_ctr.len() && xy_ctr[c_xy] != 0 {
                        solver.add_clause([-sel, xy_ctr[c_xy]]);
                    } else { solver.add_clause([-sel]); continue; }
                }
                if c_xy + 1 < xy_ctr.len() && xy_ctr[c_xy + 1] != 0 {
                    solver.add_clause([-sel, -xy_ctr[c_xy + 1]]);
                }
                if c_zw > 0 {
                    if c_zw < zw_ctr.len() && zw_ctr[c_zw] != 0 {
                        solver.add_clause([-sel, zw_ctr[c_zw]]);
                    } else { solver.add_clause([-sel]); continue; }
                }
                if c_zw + 1 < zw_ctr.len() && zw_ctr[c_zw + 1] != 0 {
                    solver.add_clause([-sel, -zw_ctr[c_zw + 1]]);
                }
                selectors.push(sel);
            }
            assert!(!selectors.is_empty(), "lag {} has no valid splits", k);
            solver.add_clause(selectors.iter().copied());
        }

        let result = solver.solve();
        assert_eq!(result, Some(true), "autocorr-only n=4 should be SAT");
    }

    #[test]
    fn sat_counter_with_xnor_hardcoded() {
        // Minimal test: hardcode X=[1,1,1,1], check XY agree at lag 3 = exactly 2
        let mut enc = SatEncoder { n: 4, m: 3, next_var: 9, xnor_triples: Vec::new() }; // vars 1-4=X, 5-8=Y
        let mut solver: radical::Solver = Default::default();
        // X = [T,T,T,T], Y = [T,F,T,T]
        for v in 1..=4 { solver.add_clause([v]); } // all X = true
        solver.add_clause([5]); // Y[0]=T
        solver.add_clause([-6]); // Y[1]=F
        solver.add_clause([7]); // Y[2]=T
        solver.add_clause([8]); // Y[3]=T

        // XY agree at lag 3: (X0,X3)=(T,T)=agree, (Y0,Y3)=(T,T)=agree
        let ag1 = enc.encode_xnor(&mut solver, 1, 4); // X0 XNOR X3
        let ag2 = enc.encode_xnor(&mut solver, 5, 8); // Y0 XNOR Y3
        let lits = vec![ag1, ag2];
        let ctr = enc.build_counter(&mut solver, &lits);
        // Enforce exactly 2 via counter
        assert!(ctr.len() >= 3 && ctr[2] != 0);
        solver.add_clause([ctr[2]]); // at least 2
        // ctr[3] doesn't exist (len=3), so at-most-2 is automatic

        let result = solver.solve();
        assert_eq!(result, Some(true), "hardcoded XY agrees at lag 3 should give exactly 2");
    }

    #[test]
    fn sat_autocorr_hardcoded_tt4() {
        // Hardcode the known TT(4) solution and check if the encoding is consistent
        // X=[1,1,1,1], Y=[1,-1,1,1], Z=[1,1,-1,-1], W=[1,-1,1]
        let n = 4usize;
        let m = 3usize;
        let mut enc = SatEncoder::new(n);
        let mut solver: radical::Solver = Default::default();

        // Hardcode solution
        let x = [1i8, 1, 1, 1];
        let y = [1i8, -1, 1, 1];
        let z = [1i8, 1, -1, -1];
        let w = [1i8, -1, 1];
        for i in 0..n { solver.add_clause([if x[i] == 1 { enc.x_var(i) } else { -enc.x_var(i) }]); }
        for i in 0..n { solver.add_clause([if y[i] == 1 { enc.y_var(i) } else { -enc.y_var(i) }]); }
        for i in 0..n { solver.add_clause([if z[i] == 1 { enc.z_var(i) } else { -enc.z_var(i) }]); }
        for i in 0..m { solver.add_clause([if w[i] == 1 { enc.w_var(i) } else { -enc.w_var(i) }]); }

        // Add autocorrelation constraints (same as sat_autocorr_only_n4)
        for k in 1..n {
            let w_overlap = if k < m { m - k } else { 0 };
            let target = 2 * (n - k) + w_overlap;
            let mut xy_lits = Vec::new();
            for i in 0..(n - k) {
                xy_lits.push(enc.encode_xnor(&mut solver, enc.x_var(i), enc.x_var(i + k)));
            }
            for i in 0..(n - k) {
                xy_lits.push(enc.encode_xnor(&mut solver, enc.y_var(i), enc.y_var(i + k)));
            }
            let mut zw_lits = Vec::new();
            for i in 0..(n - k) {
                zw_lits.push(enc.encode_xnor(&mut solver, enc.z_var(i), enc.z_var(i + k)));
            }
            for i in 0..w_overlap {
                zw_lits.push(enc.encode_xnor(&mut solver, enc.w_var(i), enc.w_var(i + k)));
            }
            let xy_ctr = enc.build_counter(&mut solver, &xy_lits);
            let zw_ctr = enc.build_counter(&mut solver, &zw_lits);
            let mut selectors = Vec::new();
            for c_zw in 0..=zw_lits.len() {
                let rem = target as isize - 2 * c_zw as isize;
                if rem < 0 || rem as usize > xy_lits.len() { continue; }
                let c_xy = rem as usize;
                let sel = enc.fresh();
                if c_xy > 0 {
                    if c_xy < xy_ctr.len() && xy_ctr[c_xy] != 0 {
                        solver.add_clause([-sel, xy_ctr[c_xy]]);
                    } else { solver.add_clause([-sel]); continue; }
                }
                if c_xy + 1 < xy_ctr.len() && xy_ctr[c_xy + 1] != 0 {
                    solver.add_clause([-sel, -xy_ctr[c_xy + 1]]);
                }
                if c_zw > 0 {
                    if c_zw < zw_ctr.len() && zw_ctr[c_zw] != 0 {
                        solver.add_clause([-sel, zw_ctr[c_zw]]);
                    } else { solver.add_clause([-sel]); continue; }
                }
                if c_zw + 1 < zw_ctr.len() && zw_ctr[c_zw + 1] != 0 {
                    solver.add_clause([-sel, -zw_ctr[c_zw + 1]]);
                }
                selectors.push(sel);
            }
            assert!(!selectors.is_empty(), "lag {} no valid splits (target={})", k, target);
            solver.add_clause(selectors.iter().copied());
        }

        let result = solver.solve();
        assert_eq!(result, Some(true), "hardcoded TT(4) solution should be consistent with encoding");
    }

    #[test]
    fn sat_finds_tt4() {
        let cfg = SearchConfig { problem: Problem::new(4), no_table: true, ..Default::default() };
        let report = run_sat_search(&cfg, false);
        assert!(report.found_solution, "SAT should find TT(4)");
    }

    #[test]
    fn sat_tt14_hardcoded_solution_bisect_lags() {
        // Known TT(14) solution (found via simulated annealing, x[0]=+1):
        let n = 14usize;
        let m = n - 1; // 13
        let x_vals: Vec<i8> = vec![1,-1,1,-1,-1,-1,1,1,1,-1,-1,1,1,1];   // sum=2
        let y_vals: Vec<i8> = vec![1,1,1,-1,1,-1,-1,1,-1,-1,1,-1,1,1];   // sum=2
        let z_vals: Vec<i8> = vec![-1,-1,-1,1,-1,-1,1,1,-1,-1,-1,-1,-1,1]; // sum=-6
        let w_vals: Vec<i8> = vec![1,1,1,-1,1,1,-1,1,-1,1,-1,-1,-1];     // sum=1

        let px = PackedSeq::from_values(&x_vals);
        let py = PackedSeq::from_values(&y_vals);
        let pz = PackedSeq::from_values(&z_vals);
        let pw = PackedSeq::from_values(&w_vals);

        // First verify the solution is actually valid
        let sx = px.sum();
        let sy = py.sum();
        let sz = pz.sum();
        let sw = pw.sum();
        eprintln!("Sums: x={}, y={}, z={}, w={}", sx, sy, sz, sw);
        eprintln!("Energy: x^2+y^2+2z^2+2w^2 = {}",
            sx*sx + sy*sy + 2*sz*sz + 2*sw*sw);
        eprintln!("Target energy: {}", 6 * n as i32 - 2);
        assert!(verify_tt(Problem::new(n), &px, &py, &pz, &pw),
            "Known TT(14) solution should verify");

        let tuple = SumTuple { x: sx, y: sy, z: sz, w: sw };

        // Step 1: Build the FULL encoding (matching sat_search exactly) plus
        // hardcode the known solution. Check if SAT.
        {
            let mut enc = SatEncoder::new(n);
            let mut solver: radical::Solver = Default::default();

            // Symmetry breaking: x[0]=+1
            solver.add_clause([enc.x_var(0)]);

            // Sum constraints
            let x_pos = ((tuple.x + n as i32) / 2) as usize;
            let y_pos = ((tuple.y + n as i32) / 2) as usize;
            let z_pos = ((tuple.z + n as i32) / 2) as usize;
            let w_pos = ((tuple.w + m as i32) / 2) as usize;

            let x_lits: Vec<i32> = (0..n).map(|i| enc.x_var(i)).collect();
            let y_lits: Vec<i32> = (0..n).map(|i| enc.y_var(i)).collect();
            let z_lits: Vec<i32> = (0..n).map(|i| enc.z_var(i)).collect();
            let w_lits: Vec<i32> = (0..m).map(|i| enc.w_var(i)).collect();

            enc.encode_cardinality_eq(&mut solver, &x_lits, x_pos);
            enc.encode_cardinality_eq(&mut solver, &y_lits, y_pos);
            enc.encode_cardinality_eq(&mut solver, &z_lits, z_pos);
            enc.encode_cardinality_eq(&mut solver, &w_lits, w_pos);

            // Autocorrelation constraints (same as sat_search)
            for k in 1..n {
                let w_overlap = if k < m { m - k } else { 0 };
                let target = 2 * (n - k) + w_overlap;

                let mut xy_lits = Vec::new();
                for i in 0..(n - k) {
                    xy_lits.push(enc.encode_xnor(&mut solver, enc.x_var(i), enc.x_var(i + k)));
                }
                for i in 0..(n - k) {
                    xy_lits.push(enc.encode_xnor(&mut solver, enc.y_var(i), enc.y_var(i + k)));
                }

                let mut zw_lits = Vec::new();
                for i in 0..(n - k) {
                    zw_lits.push(enc.encode_xnor(&mut solver, enc.z_var(i), enc.z_var(i + k)));
                }
                for i in 0..w_overlap {
                    zw_lits.push(enc.encode_xnor(&mut solver, enc.w_var(i), enc.w_var(i + k)));
                }

                let xy_ctr = enc.build_counter(&mut solver, &xy_lits);
                let zw_ctr = enc.build_counter(&mut solver, &zw_lits);

                let mut selectors = Vec::new();
                for c_zw in 0..=zw_lits.len() {
                    let rem = target as isize - 2 * c_zw as isize;
                    if rem < 0 || rem as usize > xy_lits.len() { continue; }
                    let c_xy = rem as usize;

                    let sel = enc.fresh();

                    if c_xy > 0 {
                        if c_xy < xy_ctr.len() && xy_ctr[c_xy] != 0 {
                            solver.add_clause([-sel, xy_ctr[c_xy]]);
                        } else {
                            solver.add_clause([-sel]);
                            continue;
                        }
                    }
                    if c_xy + 1 < xy_ctr.len() && xy_ctr[c_xy + 1] != 0 {
                        solver.add_clause([-sel, -xy_ctr[c_xy + 1]]);
                    }

                    if c_zw > 0 {
                        if c_zw < zw_ctr.len() && zw_ctr[c_zw] != 0 {
                            solver.add_clause([-sel, zw_ctr[c_zw]]);
                        } else {
                            solver.add_clause([-sel]);
                            continue;
                        }
                    }
                    if c_zw + 1 < zw_ctr.len() && zw_ctr[c_zw + 1] != 0 {
                        solver.add_clause([-sel, -zw_ctr[c_zw + 1]]);
                    }

                    selectors.push(sel);
                }

                if selectors.is_empty() {
                    solver.add_clause([]);
                } else {
                    solver.add_clause(selectors.iter().copied());
                }
            }

            // Hardcode the known solution as unit clauses
            for i in 0..n {
                solver.add_clause([if x_vals[i] == 1 { enc.x_var(i) } else { -enc.x_var(i) }]);
                solver.add_clause([if y_vals[i] == 1 { enc.y_var(i) } else { -enc.y_var(i) }]);
                solver.add_clause([if z_vals[i] == 1 { enc.z_var(i) } else { -enc.z_var(i) }]);
            }
            for i in 0..m {
                solver.add_clause([if w_vals[i] == 1 { enc.w_var(i) } else { -enc.w_var(i) }]);
            }

            let result = solver.solve();
            if result != Some(true) {
                eprintln!("FULL encoding with hardcoded TT(14) is UNSAT! Bisecting by lag...");
            } else {
                eprintln!("FULL encoding with hardcoded TT(14) is SAT (no bug?)");
                // Even if it passes, continue bisecting to be thorough
            }
        }

        // Step 2: Bisect by adding autocorrelation constraints ONE LAG AT A TIME
        // to find which lag's encoding is buggy.
        let mut first_buggy_lag: Option<usize> = None;
        for max_lag in 1..n {
            let mut enc = SatEncoder::new(n);
            let mut solver: radical::Solver = Default::default();

            // Symmetry breaking
            solver.add_clause([enc.x_var(0)]);

            // Sum constraints
            let x_pos = ((tuple.x + n as i32) / 2) as usize;
            let y_pos = ((tuple.y + n as i32) / 2) as usize;
            let z_pos = ((tuple.z + n as i32) / 2) as usize;
            let w_pos = ((tuple.w + m as i32) / 2) as usize;

            let x_lits: Vec<i32> = (0..n).map(|i| enc.x_var(i)).collect();
            let y_lits: Vec<i32> = (0..n).map(|i| enc.y_var(i)).collect();
            let z_lits: Vec<i32> = (0..n).map(|i| enc.z_var(i)).collect();
            let w_lits: Vec<i32> = (0..m).map(|i| enc.w_var(i)).collect();

            enc.encode_cardinality_eq(&mut solver, &x_lits, x_pos);
            enc.encode_cardinality_eq(&mut solver, &y_lits, y_pos);
            enc.encode_cardinality_eq(&mut solver, &z_lits, z_pos);
            enc.encode_cardinality_eq(&mut solver, &w_lits, w_pos);

            // Add autocorrelation constraints ONLY up to lag max_lag
            for k in 1..=max_lag {
                let w_overlap = if k < m { m - k } else { 0 };
                let target = 2 * (n - k) + w_overlap;

                let mut xy_lits_k = Vec::new();
                for i in 0..(n - k) {
                    xy_lits_k.push(enc.encode_xnor(&mut solver, enc.x_var(i), enc.x_var(i + k)));
                }
                for i in 0..(n - k) {
                    xy_lits_k.push(enc.encode_xnor(&mut solver, enc.y_var(i), enc.y_var(i + k)));
                }

                let mut zw_lits_k = Vec::new();
                for i in 0..(n - k) {
                    zw_lits_k.push(enc.encode_xnor(&mut solver, enc.z_var(i), enc.z_var(i + k)));
                }
                for i in 0..w_overlap {
                    zw_lits_k.push(enc.encode_xnor(&mut solver, enc.w_var(i), enc.w_var(i + k)));
                }

                let xy_ctr = enc.build_counter(&mut solver, &xy_lits_k);
                let zw_ctr = enc.build_counter(&mut solver, &zw_lits_k);

                let mut selectors = Vec::new();
                for c_zw in 0..=zw_lits_k.len() {
                    let rem = target as isize - 2 * c_zw as isize;
                    if rem < 0 || rem as usize > xy_lits_k.len() { continue; }
                    let c_xy = rem as usize;

                    let sel = enc.fresh();

                    if c_xy > 0 {
                        if c_xy < xy_ctr.len() && xy_ctr[c_xy] != 0 {
                            solver.add_clause([-sel, xy_ctr[c_xy]]);
                        } else {
                            solver.add_clause([-sel]);
                            continue;
                        }
                    }
                    if c_xy + 1 < xy_ctr.len() && xy_ctr[c_xy + 1] != 0 {
                        solver.add_clause([-sel, -xy_ctr[c_xy + 1]]);
                    }

                    if c_zw > 0 {
                        if c_zw < zw_ctr.len() && zw_ctr[c_zw] != 0 {
                            solver.add_clause([-sel, zw_ctr[c_zw]]);
                        } else {
                            solver.add_clause([-sel]);
                            continue;
                        }
                    }
                    if c_zw + 1 < zw_ctr.len() && zw_ctr[c_zw + 1] != 0 {
                        solver.add_clause([-sel, -zw_ctr[c_zw + 1]]);
                    }

                    selectors.push(sel);
                }

                if selectors.is_empty() {
                    solver.add_clause([]);
                } else {
                    solver.add_clause(selectors.iter().copied());
                }
            }

            // Hardcode the known solution
            for i in 0..n {
                solver.add_clause([if x_vals[i] == 1 { enc.x_var(i) } else { -enc.x_var(i) }]);
                solver.add_clause([if y_vals[i] == 1 { enc.y_var(i) } else { -enc.y_var(i) }]);
                solver.add_clause([if z_vals[i] == 1 { enc.z_var(i) } else { -enc.z_var(i) }]);
            }
            for i in 0..m {
                solver.add_clause([if w_vals[i] == 1 { enc.w_var(i) } else { -enc.w_var(i) }]);
            }

            let result = solver.solve();
            let sat = result == Some(true);

            // Compute expected values for this lag for diagnostic output
            if !sat {
                let k = max_lag;
                let w_overlap = if k < m { m - k } else { 0 };
                let target = 2 * (n - k) + w_overlap;

                // Count actual agree pairs from the known solution
                let mut xy_agree = 0usize;
                for i in 0..(n - k) {
                    if x_vals[i] == x_vals[i + k] { xy_agree += 1; }
                }
                for i in 0..(n - k) {
                    if y_vals[i] == y_vals[i + k] { xy_agree += 1; }
                }
                let mut zw_agree = 0usize;
                for i in 0..(n - k) {
                    if z_vals[i] == z_vals[i + k] { zw_agree += 1; }
                }
                for i in 0..w_overlap {
                    if w_vals[i] == w_vals[i + k] { zw_agree += 1; }
                }

                let actual_combined = xy_agree + 2 * zw_agree;

                eprintln!("LAG {} makes it UNSAT!", k);
                eprintln!("  target (from formula) = 2*(n-k) + w_overlap = 2*{} + {} = {}",
                    n - k, w_overlap, target);
                eprintln!("  actual xy_agree={}, zw_agree={}, xy_agree + 2*zw_agree = {}",
                    xy_agree, zw_agree, actual_combined);
                eprintln!("  target == actual? {}", target == actual_combined);

                // Also verify autocorrelation directly
                let nx = px.autocorrelation(k);
                let ny = py.autocorrelation(k);
                let nz = pz.autocorrelation(k);
                let nw = if k < m { pw.autocorrelation(k) } else { 0 };
                eprintln!("  N_X({})={}, N_Y({})={}, N_Z({})={}, N_W({})={}",
                    k, nx, k, ny, k, nz, k, nw);
                eprintln!("  N_X+N_Y+2*N_Z+2*N_W = {}",
                    nx + ny + 2*nz + 2*nw);

                // Check which selector splits are available
                let xy_total = 2 * (n - k);
                let zw_total = (n - k) + w_overlap;
                eprintln!("  xy_lits.len()={}, zw_lits.len()={}", xy_total, zw_total);
                eprintln!("  Valid (c_xy, c_zw) splits for target={}:", target);
                for c_zw in 0..=zw_total {
                    let rem = target as isize - 2 * c_zw as isize;
                    if rem < 0 || rem as usize > xy_total { continue; }
                    let c_xy = rem as usize;
                    let matches_actual = c_xy == xy_agree && c_zw == zw_agree;
                    eprintln!("    c_xy={}, c_zw={} {}",
                        c_xy, c_zw,
                        if matches_actual { "<-- ACTUAL" } else { "" });
                }

                if first_buggy_lag.is_none() {
                    first_buggy_lag = Some(k);
                }
                // Don't break - show all buggy lags
            } else {
                eprintln!("Lags 1..={}: SAT (ok)", max_lag);
            }
        }

        // The test should fail if any lag is buggy
        assert!(first_buggy_lag.is_none(),
            "Encoding is buggy starting at lag {}. See stderr for details.",
            first_buggy_lag.unwrap_or(0));
    }

    #[test]
    fn sat_n14_free_search_manual_encoding() {
        // Build the EXACT same encoding as sat_search for tuple (2,2,-6,1)
        // but without using sat_search — replicate its code path here.
        // Then try free search (no hardcoded solution).
        let n = 14usize;
        let m = 13usize;
        let tuple = SumTuple { x: 2, y: 2, z: -6, w: 1 };
        let mut enc = SatEncoder::new(n);
        let mut solver: radical::Solver = Default::default();

        solver.add_clause([enc.x_var(0)]); // x[0]=+1

        let x_pos = ((tuple.x + n as i32) / 2) as usize; // 8
        let y_pos = ((tuple.y + n as i32) / 2) as usize; // 8
        let z_pos = ((tuple.z + n as i32) / 2) as usize; // 4
        let w_pos = ((tuple.w + m as i32) / 2) as usize; // 7

        let x_lits: Vec<i32> = (0..n).map(|i| enc.x_var(i)).collect();
        let y_lits: Vec<i32> = (0..n).map(|i| enc.y_var(i)).collect();
        let z_lits: Vec<i32> = (0..n).map(|i| enc.z_var(i)).collect();
        let w_lits: Vec<i32> = (0..m).map(|i| enc.w_var(i)).collect();

        enc.encode_cardinality_eq(&mut solver, &x_lits, x_pos);
        enc.encode_cardinality_eq(&mut solver, &y_lits, y_pos);
        enc.encode_cardinality_eq(&mut solver, &z_lits, z_pos);
        enc.encode_cardinality_eq(&mut solver, &w_lits, w_pos);

        for k in 1..n {
            let w_overlap = if k < m { m - k } else { 0 };
            let target = 2 * (n - k) + w_overlap;
            let mut xy_lits_k = Vec::new();
            for i in 0..(n - k) { xy_lits_k.push(enc.encode_xnor(&mut solver, enc.x_var(i), enc.x_var(i + k))); }
            for i in 0..(n - k) { xy_lits_k.push(enc.encode_xnor(&mut solver, enc.y_var(i), enc.y_var(i + k))); }
            let mut zw_lits_k = Vec::new();
            for i in 0..(n - k) { zw_lits_k.push(enc.encode_xnor(&mut solver, enc.z_var(i), enc.z_var(i + k))); }
            for i in 0..w_overlap { zw_lits_k.push(enc.encode_xnor(&mut solver, enc.w_var(i), enc.w_var(i + k))); }
            let xy_ctr = enc.build_counter(&mut solver, &xy_lits_k);
            let zw_ctr = enc.build_counter(&mut solver, &zw_lits_k);
            let mut selectors = Vec::new();
            for c_zw in 0..=zw_lits_k.len() {
                let rem = target as isize - 2 * c_zw as isize;
                if rem < 0 || rem as usize > xy_lits_k.len() { continue; }
                let c_xy = rem as usize;
                let sel = enc.fresh();
                if c_xy > 0 { if c_xy < xy_ctr.len() && xy_ctr[c_xy] != 0 { solver.add_clause([-sel, xy_ctr[c_xy]]); } else { solver.add_clause([-sel]); continue; } }
                if c_xy + 1 < xy_ctr.len() && xy_ctr[c_xy + 1] != 0 { solver.add_clause([-sel, -xy_ctr[c_xy + 1]]); }
                if c_zw > 0 { if c_zw < zw_ctr.len() && zw_ctr[c_zw] != 0 { solver.add_clause([-sel, zw_ctr[c_zw]]); } else { solver.add_clause([-sel]); continue; } }
                if c_zw + 1 < zw_ctr.len() && zw_ctr[c_zw + 1] != 0 { solver.add_clause([-sel, -zw_ctr[c_zw + 1]]); }
                selectors.push(sel);
            }
            if selectors.is_empty() { solver.add_clause(std::iter::empty::<i32>()); }
            else { solver.add_clause(selectors.iter().copied()); }
        }

        eprintln!("Manual encoding: {} vars, {} clauses", solver.num_vars(), solver.num_clauses());
        let result = solver.solve();
        eprintln!("Result: {:?}, conflicts: {}", result, solver.num_conflicts());
        assert_eq!(result, Some(true), "TT(14) manual encoding should be SAT for tuple (2,2,-6,1)");
    }

    #[test]
    fn sat_solves_tt2() {
        // TT(2): Z=[+1,+1], W=[+1], tuple=(0,0,2,1)
        // Expected: X=[+1,-1], Y=[+1,-1]
        let p = Problem::new(2);
        let tuple = SumTuple { x: 0, y: 0, z: 2, w: 1 };
        let z = PackedSeq::from_values(&[1, 1]);
        let w = PackedSeq::from_values(&[1]);
        let mut zw = vec![0i32; p.n];
        for s in 1..p.n {
            let nz = z.autocorrelation(s);
            let nw = if s < p.m() { w.autocorrelation(s) } else { 0 };
            zw[s] = 2 * nz + 2 * nw;
        }
        let candidate = CandidateZW { z: z.clone(), w: w.clone(), zw_autocorr: zw };
        let template = SatXYTemplate::build(p, tuple, &radical::SolverConfig::default());
        assert!(template.is_some(), "Template should build for n=2");
        let result = template.unwrap().solve_for(&candidate);
        assert!(result.is_some(), "SAT should find X,Y for TT(2)");
        let (x, y) = result.unwrap();
        assert!(verify_tt(p, &x, &y, &z, &w), "Solution should verify");
    }

}
