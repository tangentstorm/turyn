//! Framework adapter for `--wz=cross`.
//!
//! Unlike `MddStagesAdapter` (which enumerates live MDD boundary
//! paths and dispatches them through Boundary → SolveW → SolveZ),
//! the cross path is a **brute-force Z × W producer**: for each
//! sum tuple we enumerate every full Z sequence and every full W
//! sequence that passes its spectral filter, bucket the W sides
//! by frequency via `SpectralIndex`, and cross-match to yield
//! `(Z, W)` pairs that pass the combined spectral pair bound.
//! Each surviving pair is handed to the shared XY SAT fast path
//! (`walk_xy_sub_mdd` + `SolveXyPerCandidate`).
//!
//! The heavy lifting lives in `crate::enumerate::build_w_candidates`
//! and `crate::enumerate::for_each_zw_pair`; this adapter plugs
//! them into a single `CrossEnumerateStage` that runs
//! synchronously (one handler call per run) and reports the
//! solution back through a channel, matching the shape of
//! `SyncAdapter`.
//!
//! This adapter does **not** require a pre-built `mdd-<k>.bin`
//! file — the shared `build_phase_b_context` falls back to an
//! on-the-fly BFS MDD. The MDD is still used by the XY sub-walk
//! inside `SolveXyPerCandidate`, but cross-mode users no longer
//! have to generate one up front for the search to run.

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use crate::config::SearchConfig;
use crate::enumerate::{CandidateZW, build_w_candidates, for_each_zw_pair};
use crate::legacy_search::SearchStats;
use crate::search_framework::engine::{AdapterInit, SearchModeAdapter};
use crate::search_framework::mass::{CoverageQuality, MassValue, SearchMassModel};
use crate::search_framework::stage::{
    StageContext, StageHandler, StageId, StageOutcome, WorkItem, WorkItemMeta,
};
use crate::spectrum::{SeqWithSpectrum, SpectralFilter, SpectralIndex};
use crate::types::{PackedSeq, Problem, SumTuple, verify_tt};
use crate::xy_sat::{SatXYTemplate, SolveXyPerCandidate, XyTryResult};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

/// BDKR rule (iv): least 1-indexed `i` with `Z[i]==Z[n+1-i]` must
/// have `Z[i]=+1`. In 0-indexed terms: scan pairs `(j, n-1-j)` for
/// `j = 0..(n-1)/2`; the first pair with `Z[j]==Z[n-1-j]` must have
/// `Z[j]=+1`. If no such pair exists, the rule is vacuously satisfied.
fn z_passes_rule_iv(z: &PackedSeq) -> bool {
    let n = z.len();
    let last_j = (n - 1) / 2;
    for j in 0..=last_j {
        if z.get(j) == z.get(n - 1 - j) {
            return z.get(j) == 1;
        }
    }
    true
}

/// BDKR rule (v): least 1-indexed `i` with `W[i]·W[m-i] ≠ W[m-1]`
/// must have `W[i]=+1`. In 0-indexed terms (length-m W): scan pairs
/// `(p, m-1-p)` for `p = 0..(m-1)/2`; the first pair where the
/// product disagrees with `W[m-1]` must have `W[p]=+1`.
fn w_passes_rule_v(w: &PackedSeq) -> bool {
    let m = w.len();
    if m < 3 {
        return true;
    }
    let tail = w.get(m - 1) as i32;
    let last_p = (m - 1) / 2;
    for p in 0..=last_p {
        let prod = (w.get(p) as i32) * (w.get(m - 1 - p) as i32);
        if prod != tail {
            return w.get(p) == 1;
        }
    }
    true
}

pub const STAGE_CROSS: StageId = "cross.enumerate";

#[derive(Clone, Debug, Default)]
pub struct CrossPayload;

pub struct CrossEnumerateStage {
    problem: Problem,
    cfg: Arc<SearchConfig>,
    tuples: Vec<SumTuple>,
    verbose: bool,
    k: usize,
    /// Count of completed tuples. Diagnostic only now — mass credit
    /// goes through `covered_weight_micro`, because tuples are very
    /// far from equal in size (at n=26 the 17 shells span 3.4e26 to
    /// 9.9e27 configurations, and the largest single shell is half
    /// the space).
    tuples_done: Arc<AtomicUsize>,
    /// Per-tuple share of the whole search space, normalized to sum
    /// to 1.0. Index-aligned with `tuples`.
    tuple_weights: Arc<Vec<f64>>,
    /// Covered mass in units of 1e-12, accumulated as
    /// `tuple_weight * fraction_of_that_tuple_actually_enumerated`.
    covered_weight_micro: Arc<AtomicU64>,
    /// Set when `cfg.max_z` / `cfg.max_w` truncated any shell, so the
    /// run can be reported as a sample rather than an enumeration.
    truncated: Arc<AtomicBool>,
    /// Sum of `XyStats::cover_micro` across *in-flight* XY timeouts
    /// within the tuple currently being enumerated. Reset to zero
    /// when that tuple's enumeration completes (because
    /// `tuples_done += 1` then credits the whole tuple exactly).
    /// Read by `CrossMassModel::covered_partial_mass`. Satisfies
    /// `docs/TTC.md` §7.1: "if cross mode contains timeout-capable
    /// internal sub-solves that can report eliminated search mass,
    /// it MUST surface that mass as `covered_partial`".
    in_flight_cov_micro: Arc<AtomicU64>,
    found: Arc<AtomicBool>,
    result_tx: std::sync::mpsc::Sender<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>,
}

impl StageHandler<CrossPayload> for CrossEnumerateStage {
    fn id(&self) -> StageId {
        STAGE_CROSS
    }
    fn handle(
        &self,
        _item: WorkItem<CrossPayload>,
        ctx: &StageContext<'_>,
    ) -> StageOutcome<CrossPayload> {
        let problem = self.problem;
        let cfg = &*self.cfg;
        let tuples = &self.tuples;
        let found = &*self.found;
        let continue_after_sat = cfg.continue_after_sat || cfg.bench_cover_log2.is_some();
        let spectral_z = SpectralFilter::new(problem.n, cfg.theta_samples);
        let spectral_w = SpectralFilter::new(problem.n, cfg.theta_samples);
        let mut stats = SearchStats::default();
        // Accumulates `(level, feature, count)` triples from every
        // per-(Z,W) XY SAT solver this stage spins up, so the
        // coordinator's `forcings.stage_level` / `stage_feature`
        // rollups include cross-mode propagation work. Returned
        // as `StageOutcome::forcings` below.
        let mut stage_forcings: Vec<(u16, u8, u32)> = Vec::new();
        // Per-|σ_W| cache: W candidate arrays + `SpectralIndex`
        // reused across tuples that share a `|σ_W|`.
        // (candidates, spectral index, W-shell visited, W-shell total)
        let mut w_cache: HashMap<i32, (Vec<SeqWithSpectrum>, SpectralIndex, u128, u128)> =
            HashMap::new();
        // Dedup (Z, W) within a single tuple iteration: distinct
        // sum-tuples may legitimately reach the same (Z, W) pair
        // and need separate XY-SAT calls (different (σ_X, σ_Y)
        // constraints), so the set is cleared per tuple.
        let mut seen_zw: std::collections::HashSet<(PackedSeq, PackedSeq)> =
            std::collections::HashSet::new();

        // XY stage state. Each surviving (Z, W) pair clones a
        // template matching its tuple and brute-forces the
        // `(x_bits, y_bits)` boundary combinations.
        //
        // Cap `k` so `2 * k` fits inside a `u32` shift (x_bits and
        // y_bits are `u32` at the SAT boundary). Without this,
        // `--wz=cross --mdd-k=9` panicked at `1u32 << (2 * 2 * 9) =
        // 1u32 << 36`. The brute-force producer isn't meant for
        // large `k` in the first place — users who need larger
        // boundary widths should switch to `--wz=apart|together`.
        const MAX_BOUNDARY_BITS: usize = 16; // k ≤ 8; 2^32 XY codes per (Z,W)
        let raw_k = self.k.min((problem.n - 1) / 2).min(problem.m() / 2);
        let k = raw_k.min(MAX_BOUNDARY_BITS / 2);
        if k < raw_k {
            eprintln!(
                "cross: mdd_k={} caps the brute-force XY enumeration at 2^{} per (Z,W); \
                 reducing to mdd_k={} (boundary_bits={}). Use --wz=apart|together for k>{}.",
                raw_k,
                4 * raw_k,
                k,
                2 * k,
                MAX_BOUNDARY_BITS / 2,
            );
        }
        let mut template_cache: HashMap<Vec<(i32, i32, i32, i32)>, SatXYTemplate> = HashMap::new();

        for (tuple_idx, tuple) in tuples.iter().copied().enumerate() {
            if (!continue_after_sat && found.load(Ordering::Relaxed)) || ctx.is_cancelled() {
                break;
            }
            // Phase A normalizes tuples to abs values (σ_W ≥ 0,
            // σ_Z ≥ 0). The canonical orbit can have either sign of
            // any individual σ — the MDD-backed paths walk both
            // signs of W and Z (see SolveWZ's signs loop in
            // mdd_pipeline.rs). Cross must do the same: enumerate
            // W candidates for ±tuple.w and Z sequences for
            // ±tuple.z, otherwise canonical solutions whose σ_W or
            // σ_Z is negative are silently missed.
            let abs_w = tuple.w.abs();
            if !w_cache.contains_key(&abs_w) {
                let mut w_candidates: Vec<SeqWithSpectrum> = Vec::new();
                let w_signs: &[i32] = if abs_w == 0 { &[0] } else { &[1, -1] };
                // Track how much of the W sum-shell was actually
                // enumerated. `cfg.max_w` truncates it once
                // `C(m-1, r) > max_w` (from n=22 up at the default
                // 200 000), and a truncated shell must not be
                // credited as fully searched.
                let mut w_visited: u128 = 0;
                let mut w_total: u128 = 0;
                for &sg in w_signs {
                    let (mut part, vis, tot) = build_w_candidates(
                        problem,
                        sg * abs_w,
                        cfg,
                        &spectral_w,
                        &mut stats,
                        found,
                        ctx.cancelled,
                    );
                    w_visited += vis;
                    w_total += tot;
                    w_candidates.append(&mut part);
                }
                let w_index = SpectralIndex::build(&w_candidates);
                w_cache.insert(abs_w, (w_candidates, w_index, w_visited, w_total));
            }
            let (w_candidates, w_index, w_visited, w_total) = w_cache.get(&abs_w).unwrap();
            let (w_visited, w_total) = (*w_visited, *w_total);
            if (!continue_after_sat && found.load(Ordering::Relaxed)) || ctx.is_cancelled() {
                break;
            }
            // Tuple about to be processed. `tuples_done` reports
            // the number of *completed* tuples; publish the count
            // only after this tuple's `for_each_zw_pair` returns
            // below so the live fraction isn't one tuple behind.
            seen_zw.clear();
            let abs_z = tuple.z.abs();
            let z_signs: &[i32] = if abs_z == 0 { &[0] } else { &[1, -1] };
            let mut z_visited: u128 = 0;
            let mut z_total: u128 = 0;
            for &z_sign in z_signs {
                let z_sum = z_sign * abs_z;
                let (zv, zt) = for_each_zw_pair(
                    problem,
                    z_sum,
                    w_candidates,
                    w_index,
                    cfg,
                    &spectral_z,
                    &mut stats,
                    found,
                    ctx.cancelled,
                    |z_seq, w_seq, zw, _z_spec, _w_spec| {
                        if (!continue_after_sat && found.load(Ordering::Relaxed))
                            || ctx.is_cancelled()
                        {
                            return false;
                        }
                        // BDKR rule (iv) on Z and rule (v) on W: cross's
                        // brute-force producer doesn't pre-filter these
                        // (the MDD-backed paths get them via the MDD's
                        // canonical encoding), and XY SAT only enforces
                        // rules (i,ii,iii,vi). Without this filter cross
                        // emits non-canonical (X,Y,Z,W) tuples that
                        // verify_tt accepts but inflate the canonical
                        // count above the BDKR target.
                        if !z_passes_rule_iv(z_seq) {
                            return true;
                        }
                        if !w_passes_rule_v(w_seq) {
                            return true;
                        }
                        if !seen_zw.insert((z_seq.clone(), w_seq.clone())) {
                            return true;
                        }
                        // Brute-force XY: iterate every `(x_bits, y_bits)`
                        // combination and try the XY SAT. Cross mode does
                        // NOT attempt to reuse the MDD's XY sub-tree
                        // pruning here because the MDD's live-path set
                        // was built from the Turyn-identity producer,
                        // not from brute-force `Z × W` enumeration — the
                        // two live sets don't intersect in general, so
                        // requiring an MDD-valid boundary would reject
                        // every pair the cross producer generates. At
                        // small `k` the `2^(4k)` enumeration is the
                        // honest brute-force behaviour the docstring
                        // promises; at larger `k` it's expensive but
                        // bounded.
                        let tuple_key: Vec<(i32, i32, i32, i32)> =
                            vec![(tuple.x, tuple.y, tuple.z, tuple.w)];
                        let template = template_cache.entry(tuple_key).or_insert_with(|| {
                            SatXYTemplate::build_multi_opts(
                                problem,
                                std::slice::from_ref(&tuple),
                                &cfg.sat_config,
                                cfg.xy_product_law,
                            )
                            .unwrap()
                        });
                        let candidate = CandidateZW { zw_autocorr: zw };
                        let z_seq_clone = z_seq.clone();
                        let w_seq_clone = w_seq.clone();
                        if let Some(mut state) =
                            SolveXyPerCandidate::new(problem, &candidate, template, k)
                        {
                            if problem.n > 30 {
                                state.solver.set_conflict_limit(5000);
                            }
                            // Snapshot so only the try_candidate
                            // loop's own forcings are attributed. The
                            // constructor has already propagated its
                            // setup clauses; those are stage-setup
                            // work and are excluded from the drain
                            // below, matching the `docs/TELEMETRY.md`
                            // §4 attribution rule (stage's own
                            // action, not cumulative history).
                            let xy_plk0: Vec<[u64; radical::PropKind::COUNT]> =
                                state.solver.propagations_by_kind_level().to_vec();
                            let boundary_bits = 2 * k;
                            // Widen to u64 before shifting: the old `1u32 <<
                            // (2 * boundary_bits)` overflowed once
                            // boundary_bits exceeded 15 (k≥8). `k` is now
                            // capped to `MAX_BOUNDARY_BITS / 2 = 8` up
                            // above so this shift stays ≤ `1u64 << 32`,
                            // but the u64 widening is the defensive fix.
                            let total_xy: u64 = 1u64 << (2 * boundary_bits);
                            for code in 0..total_xy {
                                // Poll both found (a peer signalled
                                // success) and the engine's live cancel
                                // flag every iteration — the brute-force
                                // loop can span billions of XY attempts
                                // and must be interruptible without a
                                // dispatch-time snapshot.
                                if (!continue_after_sat && found.load(Ordering::Relaxed))
                                    || ctx.is_cancelled()
                                {
                                    break;
                                }
                                let x_bits = (code & ((1u64 << boundary_bits) - 1)) as u32;
                                let y_bits = (code >> boundary_bits) as u32;
                                let (result, stats) = state.try_candidate(x_bits, y_bits);
                                // XY timeout partial credit: each
                                // timeout's `cover_micro ∈ [0, 1_000_000]`
                                // is the fraction of this one XY
                                // sub-cube the SAT solver actually
                                // eliminated before the conflict
                                // budget fired. Accumulate for the
                                // current tuple; reset to 0 when the
                                // tuple completes so finished tuples
                                // are credited only by `tuples_done`.
                                if matches!(result, XyTryResult::Timeout) {
                                    self.in_flight_cov_micro
                                        .fetch_add(stats.cover_micro, Ordering::Relaxed);
                                }
                                if let XyTryResult::Sat(x, y) = result {
                                    if verify_tt(problem, &x, &y, &z_seq_clone, &w_seq_clone) {
                                        if !continue_after_sat {
                                            found.store(true, Ordering::Relaxed);
                                        }
                                        let _ = self.result_tx.send((
                                            x,
                                            y,
                                            z_seq_clone.clone(),
                                            w_seq_clone.clone(),
                                        ));
                                        if !continue_after_sat {
                                            break;
                                        }
                                    }
                                }
                            }
                            // Drain the per-(Z,W) XY solver's
                            // propagation delta into the stage's
                            // forcing sink. Summed across every (Z,W)
                            // pair across every tuple, this gives
                            // cross a populated
                            // `StageOutcome::forcings` just like the
                            // MDD adapter stages.
                            stage_forcings.extend(crate::mdd_pipeline::forcing_delta_triples(
                                &state.solver,
                                &xy_plk0,
                            ));
                        }
                        continue_after_sat || !found.load(Ordering::Relaxed)
                    },
                );
                z_visited += zv;
                z_total += zt;
            }
            // Tuple (tuple_idx) fully processed. Publish
            // `tuple_idx + 1` tuples done, but reset the
            // in-flight cov_micro FIRST. If we did the stores
            // in the opposite order, a poll between the two
            // would see `new_tuples_done + old_in_flight_cov_micro`
            // — the same sub-cube credited to both exact (via
            // the tuple bump) and partial (via the un-zeroed
            // accumulator). The reverse order only yields
            // `old_tuples_done + 0` transiently, which
            // under-reports monotonically. The engine's
            // `poll_mass` monotone envelope then absorbs the
            // under-report safely.
            self.in_flight_cov_micro.store(0, Ordering::Relaxed);
            // Credit this tuple by its share of the search space
            // (`tuple_weights[tuple_idx]`, from the binomial product)
            // scaled by the fraction of the (Z x W) product actually
            // enumerated. `cfg.max_z` / `cfg.max_w` turn the shell
            // enumeration into a sample once `C(n-1, r)` exceeds them,
            // and the unvisited remainder was never searched, so
            // crediting the whole tuple there would be the same
            // over-report `docs/TTC-AUDIT.md` §5 documents.
            let frac = |vis: u128, tot: u128| -> f64 {
                if tot == 0 {
                    1.0
                } else {
                    (vis as f64 / tot as f64).clamp(0.0, 1.0)
                }
            };
            let searched = frac(z_visited, z_total) * frac(w_visited, w_total);
            if searched < 1.0 {
                self.truncated.store(true, Ordering::Relaxed);
            }
            let credit = self.tuple_weights[tuple_idx] * searched;
            self.covered_weight_micro
                .fetch_add((credit * 1e12).round().max(0.0) as u64, Ordering::Relaxed);
            self.tuples_done.store(tuple_idx + 1, Ordering::Relaxed);
        }
        // Do NOT force `tuples_done = tuples.len()` here, and do
        // NOT emit a terminal `mass_delta = 1.0`. Either of those
        // would falsely report `covered=1.000/1.000` on an early
        // exit (solution found mid-enumeration, engine cancelled,
        // `--sat-secs` wall-clock, etc.). The in-loop store above
        // already records exactly the number of tuples that
        // actually completed; the engine polls `CrossMassModel::
        // covered_mass()` per progress tick and at Finished so
        // the published fraction matches reality.
        // SPEC.md forbids silently removing valid solutions. If a shell
        // enumeration was reduced to a sample, say so: the coverage
        // number already reflects it, but a reader comparing this run
        // against the catalogue needs to know it was never an
        // exhaustive search.
        if self.truncated.load(Ordering::Relaxed) {
            eprintln!(
                "[framework:cross] WARNING: --max-z={} / --max-w={} truncated at least one \
sum-shell enumeration; this run is a SAMPLE, not an exhaustive search. Coverage is \
credited pro-rata, so `covered` will not reach 1.000. Raise --max-z/--max-w to enumerate \
in full.",
                cfg.max_z, cfg.max_w
            );
        }
        let mut out = StageOutcome::default();
        out.forcings = crate::search_framework::stage::ForcingDelta {
            by_level_feature: stage_forcings,
        };
        out
    }
}

/// Cross-mode mass model. `covered_mass = tuples_done /
/// tuples_total` treats every tuple shell as weighing the same
/// fraction of the search space, which isn't quite right — tuple
/// shells have different `(Z, W)` pair counts and XY-candidate
/// depths — so the published fraction is a uniform-weight
/// approximation, not a true XY-work fraction. Marked
/// `Hybrid` to reflect the blend: the tuple count is direct,
/// but mapping tuples to a fraction of the XY search space is
/// projected.
///
/// Partial coverage (`docs/TTC.md` §7.1, §4.2 bundled-stage
/// rule): each XY-SAT timeout inside the enumerate loop reports
/// a `cover_micro` — the fraction of that single XY sub-cube the
/// solver actually ruled out before the conflict budget fired.
/// We sum those micros across the currently in-flight tuple and
/// divide by the total XY sub-cube weight
/// (`tuples_total * total_xy_per_tuple * 1_000_000`) to get the
/// covered-partial fraction in the same unit as
/// `tuples_done / tuples_total`. Completed tuples zero the
/// in-flight accumulator so per-attempt timeouts are never
/// double-credited alongside the tuple's exact weight.
pub struct CrossMassModel {
    problem_n: usize,
    tuples_done: Arc<AtomicUsize>,
    tuples_total: usize,
    /// See `CrossEnumerateStage::covered_weight_micro`.
    covered_weight_micro: Arc<AtomicU64>,
    /// Shared with the stage; sum of `cover_micro` for XY
    /// timeouts in the current tuple. Cleared when the tuple
    /// completes.
    in_flight_cov_micro: Arc<AtomicU64>,
    /// `2^(4k)` — number of XY `(x_bits, y_bits)` combinations
    /// per tuple in the brute-force enumeration. Used as part of
    /// the partial-coverage denominator.
    xy_per_tuple: u64,
}

impl SearchMassModel for CrossMassModel {
    fn covered_mass(&self) -> MassValue {
        if self.tuples_total == 0 {
            return MassValue::ZERO;
        }
        // Space-weighted, truncation-adjusted. Uniform
        // `tuples_done / tuples_total` was wrong twice over: it
        // treated a shell worth 50 % of the n=26 space the same as
        // one worth 1.7 %, and it credited a shell in full even when
        // `cfg.max_z` / `cfg.max_w` had reduced its enumeration to a
        // sample (`docs/TTC-AUDIT.md` §5).
        let micro = self.covered_weight_micro.load(Ordering::Relaxed);
        MassValue((micro as f64 / 1e12).clamp(0.0, 1.0))
    }
    fn covered_partial_mass(&self) -> MassValue {
        if self.tuples_total == 0 || self.xy_per_tuple == 0 {
            return MassValue::ZERO;
        }
        let micros = self.in_flight_cov_micro.load(Ordering::Relaxed) as f64;
        let denom = self.tuples_total as f64 * self.xy_per_tuple as f64 * 1_000_000.0;
        MassValue((micros / denom).clamp(0.0, 1.0))
    }
    fn total_log2_work(&self) -> Option<f64> {
        Some(crate::search_framework::mass::raw_log2_work(self.problem_n))
    }
    /// Hybrid: tuple-count numerator is direct but the mapping
    /// to XY-search fraction is projected (uniform tuple
    /// weighting). Per `docs/TTC.md` §7.1 this MUST remain
    /// non-`Direct` until both tuple weighting and timeout
    /// credits become direct search-mass fractions.
    fn quality(&self) -> CoverageQuality {
        CoverageQuality::Hybrid
    }
}

/// Share of the whole search space belonging to each sum-tuple shell,
/// normalized to sum to 1.
///
/// The shell for `(σ_X, σ_Y, σ_Z, σ_W)` holds
/// `C(n, ·) · C(n, ·) · C(n, ·) · C(n-1, ·)` sign assignments, and the
/// shells are wildly unequal: at n=26 the 17 shells span 3.4e26 to
/// 9.9e27, with the largest alone worth half the space. Crediting
/// `1 / tuples_total` per completed shell therefore mis-states coverage
/// by up to ~8.5x at n=26 (`docs/TTC-AUDIT.md` §5).
///
/// Falls back to uniform weights if the sizes cannot be computed.
fn tuple_space_weights(problem: Problem, tuples: &[SumTuple]) -> Vec<f64> {
    let n = problem.n;
    let m = problem.m();
    let shell = |len: usize, sigma: i32| -> f64 {
        // #(+1) = (len + sigma) / 2, must be an integer in [0, len].
        let num = len as i32 + sigma;
        if num < 0 || num % 2 != 0 {
            return 0.0;
        }
        let ones = (num / 2) as usize;
        if ones > len {
            return 0.0;
        }
        crate::enumerate::binom(len, ones) as f64
    };
    let sizes: Vec<f64> = tuples
        .iter()
        .map(|t| {
            shell(n, t.x.abs()) * shell(n, t.y.abs()) * shell(n, t.z.abs()) * shell(m, t.w.abs())
        })
        .collect();
    let total: f64 = sizes.iter().sum();
    if !(total > 0.0) || !total.is_finite() {
        let uniform = if tuples.is_empty() {
            0.0
        } else {
            1.0 / tuples.len() as f64
        };
        return vec![uniform; tuples.len()];
    }
    sizes.iter().map(|s| s / total).collect()
}

pub struct CrossAdapter {
    pub problem: Problem,
    pub tuples: Vec<SumTuple>,
    pub cfg: Arc<SearchConfig>,
    pub verbose: bool,
    pub k: usize,
    pub tuples_done: Arc<AtomicUsize>,
    /// Per-tuple share of the search space, normalized to sum to 1.
    pub tuple_weights: Arc<Vec<f64>>,
    /// Weighted covered mass in units of 1e-12.
    pub covered_weight_micro: Arc<AtomicU64>,
    /// Any shell truncated by `cfg.max_z` / `cfg.max_w`.
    pub truncated: Arc<AtomicBool>,
    /// Shared in-flight XY-timeout `cover_micro` counter. Stage
    /// writes; mass model reads.
    pub in_flight_cov_micro: Arc<AtomicU64>,
    pub found: Arc<AtomicBool>,
    pub result_tx: std::sync::mpsc::Sender<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>,
}

impl CrossAdapter {
    pub fn build(
        problem: Problem,
        tuples: Vec<SumTuple>,
        cfg: SearchConfig,
        verbose: bool,
        k: usize,
    ) -> (
        Self,
        std::sync::mpsc::Receiver<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>,
    ) {
        let (result_tx, result_rx) = std::sync::mpsc::channel();
        let tuples_done = Arc::new(AtomicUsize::new(0));
        let in_flight_cov_micro = Arc::new(AtomicU64::new(0));
        let found = Arc::new(AtomicBool::new(false));
        let tuple_weights = Arc::new(tuple_space_weights(problem, &tuples));
        (
            CrossAdapter {
                problem,
                tuples,
                cfg: Arc::new(cfg),
                verbose,
                k,
                tuples_done,
                tuple_weights,
                covered_weight_micro: Arc::new(AtomicU64::new(0)),
                truncated: Arc::new(AtomicBool::new(false)),
                in_flight_cov_micro,
                found,
                result_tx,
            },
            result_rx,
        )
    }

    /// Same `k`-clamp the stage applies inside `handle`. Cross
    /// caps `k` so `2^(4k)` fits inside the brute-force XY loop's
    /// `u32` shift, which decides the XY-per-tuple denominator
    /// used for partial-coverage scaling.
    fn effective_k(&self) -> usize {
        const MAX_BOUNDARY_BITS: usize = 16;
        let raw_k = self
            .k
            .min((self.problem.n - 1) / 2)
            .min(self.problem.m() / 2);
        raw_k.min(MAX_BOUNDARY_BITS / 2)
    }
}

impl SearchModeAdapter<CrossPayload> for CrossAdapter {
    fn name(&self) -> &'static str {
        "cross"
    }
    fn init(&self) -> AdapterInit<CrossPayload> {
        AdapterInit {
            seed_items: vec![WorkItem {
                stage_id: STAGE_CROSS,
                priority: 0,
                gold: false,
                cost_hint: 1,
                replay_key: 0,
                mass_hint: Some(1.0),
                meta: WorkItemMeta {
                    item_id: 0,
                    parent_item_id: None,
                    fanout_root_id: 0,
                    depth_from_root: 0,
                    spawn_seq: 0,
                },
                payload: CrossPayload,
            }],
        }
    }
    fn stages(&self) -> BTreeMap<StageId, Box<dyn StageHandler<CrossPayload>>> {
        let mut m: BTreeMap<StageId, Box<dyn StageHandler<CrossPayload>>> = BTreeMap::new();
        m.insert(
            STAGE_CROSS,
            Box::new(CrossEnumerateStage {
                problem: self.problem,
                cfg: Arc::clone(&self.cfg),
                tuples: self.tuples.clone(),
                verbose: self.verbose,
                k: self.k,
                tuples_done: Arc::clone(&self.tuples_done),
                tuple_weights: Arc::clone(&self.tuple_weights),
                covered_weight_micro: Arc::clone(&self.covered_weight_micro),
                truncated: Arc::clone(&self.truncated),
                in_flight_cov_micro: Arc::clone(&self.in_flight_cov_micro),
                found: Arc::clone(&self.found),
                result_tx: self.result_tx.clone(),
            }),
        );
        m
    }
    fn mass_model(&self) -> Box<dyn SearchMassModel> {
        let k_eff = self.effective_k();
        // `xy_per_tuple = 2^(4 * k_eff)`. `k_eff <= 8`, so the
        // shift is ≤ 32 and stays inside a `u64`.
        let xy_per_tuple: u64 = if k_eff == 0 { 1 } else { 1u64 << (4 * k_eff) };
        Box::new(CrossMassModel {
            problem_n: self.problem.n,
            tuples_done: Arc::clone(&self.tuples_done),
            tuples_total: self.tuples.len(),
            covered_weight_micro: Arc::clone(&self.covered_weight_micro),
            in_flight_cov_micro: Arc::clone(&self.in_flight_cov_micro),
            xy_per_tuple,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// TTC §7.1 + §10 item 7: cross's tuple weights are exact
    /// binomial shell sizes now, but the XY-timeout partial credit is
    /// still an estimate, so the label MUST remain non-`Direct`.
    #[test]
    fn cross_mass_model_is_non_direct() {
        let model = CrossMassModel {
            covered_weight_micro: Arc::new(AtomicU64::new(0)),
            problem_n: 26,
            tuples_done: Arc::new(AtomicUsize::new(0)),
            tuples_total: 3,
            in_flight_cov_micro: Arc::new(AtomicU64::new(0)),
            xy_per_tuple: 16,
        };
        assert_ne!(
            model.quality(),
            CoverageQuality::Direct,
            "cross mode uses uniform tuple weighting; label MUST stay non-Direct per TTC §7.1"
        );
        assert_eq!(model.quality(), CoverageQuality::Hybrid);
    }

    /// TTC §7.1: "every timeout-capable XY attempt ... MUST
    /// contribute its partial credit". The cross adapter writes
    /// `in_flight_cov_micro` on every XY timeout; the mass model
    /// must surface that as `covered_partial` in the same
    /// fraction unit as `tuples_done / tuples_total`.
    #[test]
    fn cross_partial_mass_reflects_in_flight_xy_timeouts() {
        let cov = Arc::new(AtomicU64::new(0));
        let model = CrossMassModel {
            covered_weight_micro: Arc::new(AtomicU64::new(0)),
            problem_n: 26,
            tuples_done: Arc::new(AtomicUsize::new(0)),
            tuples_total: 4,
            in_flight_cov_micro: Arc::clone(&cov),
            xy_per_tuple: 16, // denom = 4 * 16 * 1e6 = 64_000_000
        };
        assert_eq!(model.covered_partial_mass().0, 0.0);
        cov.store(32_000_000, Ordering::Relaxed); // half the denom
        assert!((model.covered_partial_mass().0 - 0.5).abs() < 1e-9);
    }

    /// Tuple shells are wildly unequal, so weights must be the
    /// binomial shell sizes normalized to 1 -- not `1 / tuples_total`.
    /// Uniform weighting mis-stated coverage by up to ~8.5x at n=26
    /// (`docs/TTC-AUDIT.md` §5).
    #[test]
    fn tuple_weights_are_proportional_to_shell_size_and_sum_to_one() {
        let problem = Problem::new(14);
        let tuples = vec![
            SumTuple {
                x: 2,
                y: 2,
                z: 6,
                w: 1,
            },
            SumTuple {
                x: 4,
                y: 8,
                z: 0,
                w: 1,
            },
        ];
        let w = tuple_space_weights(problem, &tuples);
        assert_eq!(w.len(), 2);
        let sum: f64 = w.iter().sum();
        assert!(
            (sum - 1.0).abs() < 1e-12,
            "weights must sum to 1, got {sum}"
        );
        // Ratio must match the binomial products, not be 1:1.
        let size = |t: &SumTuple| -> f64 {
            let shell = |len: usize, sigma: i32| -> f64 {
                crate::enumerate::binom(len, ((len as i32 + sigma) / 2) as usize) as f64
            };
            shell(14, t.x.abs())
                * shell(14, t.y.abs())
                * shell(14, t.z.abs())
                * shell(13, t.w.abs())
        };
        let expect = size(&tuples[0]) / (size(&tuples[0]) + size(&tuples[1]));
        assert!(
            (w[0] - expect).abs() < 1e-12,
            "weight {} should equal shell fraction {expect}",
            w[0]
        );
        assert!(
            (w[0] - 0.5).abs() > 1e-6,
            "these two shells are not the same size; uniform weighting would be wrong"
        );
    }

    /// `covered_mass` must read the weighted accumulator, so a partly
    /// enumerated run cannot report full coverage.
    #[test]
    fn covered_mass_tracks_weighted_credit_not_tuple_count() {
        let credit = Arc::new(AtomicU64::new(0));
        let model = CrossMassModel {
            covered_weight_micro: Arc::clone(&credit),
            problem_n: 26,
            // All four tuples "done", but only a third of the space
            // actually enumerated -- the old model would have said 1.0.
            tuples_done: Arc::new(AtomicUsize::new(4)),
            tuples_total: 4,
            in_flight_cov_micro: Arc::new(AtomicU64::new(0)),
            xy_per_tuple: 16,
        };
        credit.store((0.333_f64 * 1e12) as u64, Ordering::Relaxed);
        assert!(
            (model.covered_mass().0 - 0.333).abs() < 1e-6,
            "covered_mass MUST reflect weighted credit, got {}",
            model.covered_mass().0
        );
    }

    /// TTC §3 clamp: even if `in_flight_cov_micro` somehow
    /// overflows the denominator, the published partial fraction
    /// MUST stay in `[0, 1]`.
    #[test]
    fn cross_partial_mass_clamps_to_one() {
        let cov = Arc::new(AtomicU64::new(u64::MAX));
        let model = CrossMassModel {
            covered_weight_micro: Arc::new(AtomicU64::new(0)),
            problem_n: 26,
            tuples_done: Arc::new(AtomicUsize::new(0)),
            tuples_total: 4,
            in_flight_cov_micro: cov,
            xy_per_tuple: 16,
        };
        assert!(model.covered_partial_mass().0 <= 1.0);
    }
}
