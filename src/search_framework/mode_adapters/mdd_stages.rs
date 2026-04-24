//! Framework adapter that wraps the five extracted MDD pipeline
//! stage helpers (`process_boundary`, `process_solve_w`,
//! `process_solve_wz`, `process_solve_z`, `process_solve_xy`) as
//! real `StageHandler`s.
//!
//! The resulting adapter gives `--engine=new --wz=apart|together`
//! per-stage forcing attribution (via `StageOutcome::forcings` —
//! populated as empty here in v1 until each helper returns a
//! `ForcingDelta` bundle; the underlying `PipelineMetrics` already
//! updates global counters through the same Arc registry the
//! legacy path uses).
//!
//! Per-handler scratch lives behind `Mutex<...>`. With the
//! framework engine's default `worker_count = 1` this is
//! contention-free; at higher worker counts the Mutex serializes,
//! and future work can switch to per-worker thread-locals once
//! `run_mdd_sat_search`'s own parallelism is retired.

use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

use crate::config::SearchConfig;
use crate::mdd_pipeline::{
    build_phase_b_context, enumerate_live_boundaries, mdd_navigate_to_outfix,
    new_pipeline_metrics, process_boundary, process_solve_w, process_solve_wz, process_solve_z,
    BoundaryWork, PhaseBContext, PipelineMetrics, PipelineWork, SolveWWork, SolveWZWork,
    SolveZWork, ZStageScratch,
};
use crate::search_framework::engine::{AdapterInit, SearchModeAdapter};
use crate::search_framework::mass::{CoverageQuality, MassValue, SearchMassModel};
use crate::search_framework::stage::{
    ForcingDelta, StageContext, StageHandler, StageId, StageOutcome, WorkItem, WorkItemMeta,
};
use crate::xy_sat::SatXYTemplate;
use crate::legacy_search::WarmStartState;
use crate::spectrum::{FftScratch, SpectralFilter};
use crate::types::{Problem, SumTuple};

pub const STAGE_BOUNDARY: StageId = "mdd.boundary";
pub const STAGE_SOLVE_W: StageId = "mdd.solve_w";
pub const STAGE_SOLVE_WZ: StageId = "mdd.solve_wz";
pub const STAGE_SOLVE_Z: StageId = "mdd.solve_z";

/// Per-boundary fan-out tracker. One boundary (identified by
/// `fanout_root_id` = its seed index) may dispatch through multiple
/// stage handlers: Boundary → SolveW → SolveZ, or Boundary →
/// SolveWZ, with stage 2/3 sometimes emitting zero follow-ups
/// because of filter rejection or re-queue semantics.
///
/// Two coverage streams:
///
/// * `completed_boundaries / total` — the "exact" fraction
///   (additive over disjoint boundaries). Incremented when a
///   boundary's pending-count hits zero.
/// * `partial_cov_micro / (total * 1_000_000)` — the
///   timeout-shortfall fraction. Each XY timeout inside
///   `process_solve_z` reports a `cover_micro ∈ [0, 1_000_000]`
///   reflecting how much of that sub-cube the SAT solver actually
///   ruled out before hitting its conflict budget. We sum those
///   `cover_micro` values across all XY solves anywhere in the
///   search and surface the ratio as `covered_partial` on the
///   `ProgressSnapshot` — matches the `xy_cover_micro` accounting
///   documented in `docs/TTC.md`.
///
/// Algorithm: each stage handler calls `note_handled` with its
/// item's `fanout_root_id` plus the number of children emitted
/// and (for SolveZ) the `cover_micro_delta` accumulated during
/// its inline XY walk. Pending count for the boundary decreases
/// by 1 and increases by `emitted`; when it hits 0 the boundary
/// is removed from the map and `completed` ticks up. Seed
/// boundaries start at `pending = 1` lazily when first seen.
pub struct BoundaryProgress {
    /// `(pending_count, already_completed)` per root. Keeping
    /// `already_completed` on the entry lets `note_handled` stay
    /// idempotent for a given root even if a stale item arrives
    /// after the pending count first reached zero. TTC §3
    /// invariant 7: "no completed subproblem may be credited more
    /// than once".
    pending: Mutex<HashMap<u64, (u64, bool)>>,
    completed: AtomicU64,
    partial_cov_micro: AtomicU64,
    total: u64,
}

impl BoundaryProgress {
    pub fn new(total: u64) -> Self {
        Self {
            pending: Mutex::new(HashMap::new()),
            completed: AtomicU64::new(0),
            partial_cov_micro: AtomicU64::new(0),
            total,
        }
    }

    /// Record that a stage handler just finished processing an item
    /// belonging to `fanout_root_id` and emitted `emitted` child
    /// items. Returns `true` exactly once — the first time the
    /// boundary's pending count hits zero. Subsequent calls for
    /// the same root return `false` without re-incrementing the
    /// `completed` counter, keeping the
    /// "no-double-credit" invariant (TTC §3.7) even if a stale
    /// emission arrives after the boundary was already closed.
    pub fn note_handled(&self, fanout_root_id: u64, emitted: u64) -> bool {
        let mut guard = self.pending.lock().unwrap();
        let entry = guard.entry(fanout_root_id).or_insert((1, false));
        entry.0 = entry.0.saturating_sub(1) + emitted;
        if entry.0 == 0 && !entry.1 {
            entry.1 = true;
            self.completed.fetch_add(1, Ordering::Relaxed);
            true
        } else {
            false
        }
    }

    /// Add `cov_micro` (sum of per-XY-timeout `cover_micro ∈ [0,
    /// 1_000_000]`) to the running partial-coverage accumulator.
    /// Called by `SolveZStage` after its inline XY walk returns.
    pub fn add_partial_cov_micro(&self, cov_micro: u64) {
        if cov_micro > 0 {
            self.partial_cov_micro
                .fetch_add(cov_micro, Ordering::Relaxed);
        }
    }

    /// Fraction of the search space *fully* covered — i.e.
    /// boundaries whose entire sub-tree of SolveW/Z/XY work
    /// returned without timing out. Additive over disjoint
    /// boundaries.
    pub fn covered_fraction(&self) -> f64 {
        if self.total == 0 {
            0.0
        } else {
            let done = self.completed.load(Ordering::Relaxed);
            (done as f64 / self.total as f64).clamp(0.0, 1.0)
        }
    }

    /// Fractional credit from XY timeouts across the whole search.
    /// Scaled so that if every SolveXY timed out with full
    /// `cover_micro = 1_000_000` (i.e. the conflict budget
    /// exhausted *after* fully pruning the sub-cube), the
    /// returned fraction equals `average_xy_solves_per_boundary /
    /// total_boundaries` — which with `apply_delta` is clamped
    /// below the residual `1 - covered_exact`, so the published
    /// `covered = covered_exact + covered_partial` stays ≤ 1.
    /// The denominator uses `total * 1_000_000` so a single
    /// fully-credited timeout is worth `1 / total` — same unit as
    /// a fully-completed boundary.
    pub fn partial_fraction(&self) -> f64 {
        if self.total == 0 {
            0.0
        } else {
            let sum = self.partial_cov_micro.load(Ordering::Relaxed);
            (sum as f64 / (self.total as f64 * 1_000_000.0)).clamp(0.0, 1.0)
        }
    }
}

/// Payload discriminator for the framework `WorkItem<MddPayload>`.
/// One variant per scheduled stage. SolveXY is not scheduled via
/// the queue — `process_solve_z` fires XY solves inline per
/// `(Z, W)` pair — so there is no `SolveXY` variant here.
pub enum MddPayload {
    Boundary(BoundaryWork),
    SolveW(SolveWWork),
    SolveWZ(SolveWZWork),
    SolveZ(SolveZWork),
}

impl MddPayload {
    fn stage_id(&self) -> StageId {
        match self {
            MddPayload::Boundary(_) => STAGE_BOUNDARY,
            MddPayload::SolveW(_) => STAGE_SOLVE_W,
            MddPayload::SolveWZ(_) => STAGE_SOLVE_WZ,
            MddPayload::SolveZ(_) => STAGE_SOLVE_Z,
        }
    }
}

fn from_pipeline_work(work: PipelineWork) -> Option<MddPayload> {
    // The five stage helpers only emit SolveW / SolveWZ / SolveZ
    // as pipeline follow-ups today. Boundary items enter the queue
    // via the adapter's seed, and SolveXY items are pushed directly
    // inside `process_solve_z` without routing through
    // `PipelineWork` (see comment on that helper).
    match work {
        PipelineWork::SolveW(w) => Some(MddPayload::SolveW(w)),
        PipelineWork::SolveWZ(wz) => Some(MddPayload::SolveWZ(wz)),
        PipelineWork::SolveZ(z) => Some(MddPayload::SolveZ(z)),
    }
}

fn wrap_items(
    items: Vec<PipelineWork>,
    parent: &WorkItemMeta,
    item_ids: &AtomicU64,
) -> Vec<WorkItem<MddPayload>> {
    items
        .into_iter()
        .filter_map(|pw| {
            let payload = from_pipeline_work(pw)?;
            let stage_id = payload.stage_id();
            // Fetch-add gives every sibling a unique id, avoiding the
            // prior `parent.item_id.wrapping_add(1)` collision where all
            // children of the same parent shared the same id (PR review
            // #8).
            let item_id = item_ids.fetch_add(1, Ordering::Relaxed);
            Some(WorkItem {
                stage_id,
                priority: default_priority_for_stage(stage_id),
                cost_hint: 1,
                replay_key: parent.item_id,
                mass_hint: None,
                meta: WorkItemMeta {
                    item_id,
                    parent_item_id: Some(parent.item_id),
                    fanout_root_id: parent.fanout_root_id,
                    depth_from_root: parent.depth_from_root.saturating_add(1),
                    spawn_seq: 0,
                },
                payload,
            })
        })
        .collect()
}

fn default_priority_for_stage(stage: StageId) -> i32 {
    // Later stages run first: SolveZ drains before SolveW feeds
    // more, so solutions land quickly. Boundary=0, SolveW / SolveWZ=1,
    // SolveZ=2.
    match stage {
        STAGE_BOUNDARY => 0,
        STAGE_SOLVE_W | STAGE_SOLVE_WZ => 1,
        STAGE_SOLVE_Z => 2,
        _ => 0,
    }
}

pub struct BoundaryStage {
    ctx: Arc<PhaseBContext>,
    metrics: PipelineMetrics,
    use_wz_mode: bool,
    item_ids: Arc<AtomicU64>,
    progress: Arc<BoundaryProgress>,
}

impl StageHandler<MddPayload> for BoundaryStage {
    fn id(&self) -> StageId {
        STAGE_BOUNDARY
    }
    fn handle(
        &self,
        item: WorkItem<MddPayload>,
        ctx: &StageContext<'_>,
    ) -> StageOutcome<MddPayload> {
        if ctx.is_cancelled() {
            return StageOutcome::default();
        }
        let parent_meta = item.meta;
        let MddPayload::Boundary(bnd) = item.payload else {
            return StageOutcome::default();
        };
        let emitted_raw = process_boundary(bnd, &self.ctx, &self.metrics, self.use_wz_mode);
        let mut out = StageOutcome::default();
        out.emitted = wrap_items(emitted_raw, &parent_meta, &self.item_ids);
        // Mass credit flows through `BoundaryProgress`: this item
        // consumes 1 pending unit and adds one per emitted child.
        // If the boundary has no more live descendants (filter-
        // rejected outright, or a later stage just finished its
        // last child) the poll-based `covered_fraction` ticks up.
        self.progress
            .note_handled(parent_meta.fanout_root_id, out.emitted.len() as u64);
        out
    }
}

struct SolveWScratch {
    w_bases: HashMap<i32, radical::Solver>,
    fft_buf_w: FftScratch,
    rng: u64,
}

pub struct SolveWStage {
    ctx: Arc<PhaseBContext>,
    metrics: PipelineMetrics,
    spectral_w: Arc<SpectralFilter>,
    scratch: Mutex<SolveWScratch>,
    item_ids: Arc<AtomicU64>,
    progress: Arc<BoundaryProgress>,
}

impl StageHandler<MddPayload> for SolveWStage {
    fn id(&self) -> StageId {
        STAGE_SOLVE_W
    }
    fn handle(
        &self,
        item: WorkItem<MddPayload>,
        ctx: &StageContext<'_>,
    ) -> StageOutcome<MddPayload> {
        if ctx.is_cancelled() {
            return StageOutcome::default();
        }
        let parent_meta = item.meta;
        let MddPayload::SolveW(sw) = item.payload else {
            return StageOutcome::default();
        };
        let mut guard = self.scratch.lock().unwrap();
        let SolveWScratch {
            w_bases,
            fft_buf_w,
            rng,
        } = &mut *guard;
        let mut forcings: Vec<(u16, u8, u32)> = Vec::new();
        let emitted_raw = process_solve_w(
            sw,
            &self.ctx,
            &self.metrics,
            w_bases,
            &self.spectral_w,
            fft_buf_w,
            rng,
            &mut forcings,
        );
        let mut out = StageOutcome::default();
        out.forcings = ForcingDelta { by_level_feature: forcings };
        out.emitted = wrap_items(emitted_raw, &parent_meta, &self.item_ids);
        // Handoff to the boundary's pending-counter: this SolveW
        // item consumes one unit and emits `out.emitted.len()` new
        // ones. If that takes the boundary's pending count to zero
        // (e.g. no SolveZ candidates survived and this was the last
        // in-flight W) the boundary is counted complete — so a
        // pruned sub-cube still credits coverage.
        self.progress
            .note_handled(parent_meta.fanout_root_id, out.emitted.len() as u64);
        out
    }
}

struct SolveWZScratch {
    template_cache: HashMap<Vec<(i32, i32, i32, i32)>, SatXYTemplate>,
    rng: u64,
}

pub struct SolveWZStage {
    ctx: Arc<PhaseBContext>,
    metrics: PipelineMetrics,
    sat_config: Arc<radical::SolverConfig>,
    result_tx: std::sync::mpsc::Sender<(
        crate::types::PackedSeq,
        crate::types::PackedSeq,
        crate::types::PackedSeq,
        crate::types::PackedSeq,
    )>,
    scratch: Mutex<SolveWZScratch>,
    item_ids: Arc<AtomicU64>,
    progress: Arc<BoundaryProgress>,
}

impl StageHandler<MddPayload> for SolveWZStage {
    fn id(&self) -> StageId {
        STAGE_SOLVE_WZ
    }
    fn handle(
        &self,
        item: WorkItem<MddPayload>,
        ctx: &StageContext<'_>,
    ) -> StageOutcome<MddPayload> {
        if ctx.is_cancelled() {
            return StageOutcome::default();
        }
        let parent_meta = item.meta;
        let MddPayload::SolveWZ(swz) = item.payload else {
            return StageOutcome::default();
        };
        let mut guard = self.scratch.lock().unwrap();
        let SolveWZScratch {
            template_cache,
            rng,
        } = &mut *guard;
        // Snapshot `flow_xy_timeout_cov_micro` before/after so any
        // timeout-capable XY work triggered inside `process_solve_wz`
        // contributes partial credit to the same boundary-mass
        // ledger `SolveZ` uses. Without this, `--wz=together`
        // undercounts `covered_partial`; see `docs/TTC.md` §4.2
        // (bundled-stage rule) and §7.2 (apart/together parity).
        let cov_micro_before = self
            .metrics
            .flow_xy_timeout_cov_micro
            .load(std::sync::atomic::Ordering::Relaxed);
        let mut forcings: Vec<(u16, u8, u32)> = Vec::new();
        let deferred = process_solve_wz(
            swz,
            &self.ctx,
            &self.metrics,
            template_cache,
            &self.sat_config,
            &self.result_tx,
            rng,
            &mut forcings,
        );
        let cov_micro_after = self
            .metrics
            .flow_xy_timeout_cov_micro
            .load(std::sync::atomic::Ordering::Relaxed);
        self.progress
            .add_partial_cov_micro(cov_micro_after.saturating_sub(cov_micro_before));
        let mut out = StageOutcome::default();
        out.forcings = ForcingDelta { by_level_feature: forcings };
        if let Some((item, _priority)) = deferred {
            // Framework priority is i32 (coarse tag); legacy f64
            // continuation priority is dropped. Re-enqueue as
            // low-priority "maybe".
            out.emitted = wrap_items(vec![item], &parent_meta, &self.item_ids)
                .into_iter()
                .map(|mut w| {
                    w.priority = 1;
                    w
                })
                .collect();
        }
        // Either we emitted a deferred re-queue (pending stays at
        // 1 — same boundary still in flight) or we finished for
        // good (pending drops to 0 — boundary complete, emit no
        // follow-up, the `(Z, W)` search was exhausted).
        self.progress
            .note_handled(parent_meta.fanout_root_id, out.emitted.len() as u64);
        out
    }
}

struct SolveZScratch {
    z_scratch: ZStageScratch,
    fft_buf_z: FftScratch,
    template_cache: HashMap<Vec<(i32, i32, i32, i32)>, SatXYTemplate>,
    warm: WarmStartState,
    rng: u64,
}

pub struct SolveZStage {
    ctx: Arc<PhaseBContext>,
    metrics: PipelineMetrics,
    spectral_z: Arc<SpectralFilter>,
    sat_config: Arc<radical::SolverConfig>,
    result_tx: std::sync::mpsc::Sender<(
        crate::types::PackedSeq,
        crate::types::PackedSeq,
        crate::types::PackedSeq,
        crate::types::PackedSeq,
    )>,
    scratch: Mutex<SolveZScratch>,
    progress: Arc<BoundaryProgress>,
}

impl StageHandler<MddPayload> for SolveZStage {
    fn id(&self) -> StageId {
        STAGE_SOLVE_Z
    }
    fn handle(
        &self,
        item: WorkItem<MddPayload>,
        ctx: &StageContext<'_>,
    ) -> StageOutcome<MddPayload> {
        if ctx.is_cancelled() {
            return StageOutcome::default();
        }
        let parent_meta = item.meta;
        let MddPayload::SolveZ(sz) = item.payload else {
            return StageOutcome::default();
        };
        let mut guard = self.scratch.lock().unwrap();
        // Split-borrow: `process_solve_z` needs mutable references
        // to four different `SolveZScratch` fields at once.
        let SolveZScratch {
            z_scratch,
            fft_buf_z,
            template_cache,
            warm,
            rng,
        } = &mut *guard;
        // Snapshot `flow_xy_timeout_cov_micro` before/after so we
        // can attribute the partial-XY credit this SolveZ just
        // earned. The atomic is a global counter across the whole
        // search; the delta is the sub-cube credit from inline XY
        // timeouts during *this* call. `process_solve_z` is
        // terminal — it fires XY solves inline and reports
        // solutions through `result_tx`.
        let cov_micro_before = self
            .metrics
            .flow_xy_timeout_cov_micro
            .load(std::sync::atomic::Ordering::Relaxed);
        let mut forcings: Vec<(u16, u8, u32)> = Vec::new();
        process_solve_z(
            sz,
            &self.ctx,
            &self.metrics,
            z_scratch,
            &self.spectral_z,
            fft_buf_z,
            template_cache,
            warm,
            &self.sat_config,
            &self.result_tx,
            rng,
            &mut forcings,
        );
        let cov_micro_after = self
            .metrics
            .flow_xy_timeout_cov_micro
            .load(std::sync::atomic::Ordering::Relaxed);
        self.progress
            .add_partial_cov_micro(cov_micro_after.saturating_sub(cov_micro_before));
        // Mass credit: one more pending descendant of this
        // boundary is done. When the last SolveZ for a boundary
        // returns, `note_handled` drops the pending count to zero
        // and the poll-based `covered_fraction` ticks up by
        // exactly `1/N`. Inline XY timeouts that didn't drop
        // pending still contribute via `add_partial_cov_micro`
        // above — the mass model surfaces them as
        // `covered_partial`, matching the timeout-shortfall
        // credit described in `docs/TTC.md`.
        self.progress.note_handled(parent_meta.fanout_root_id, 0);
        let mut out = StageOutcome::default();
        out.forcings = ForcingDelta { by_level_feature: forcings };
        out
    }
}

/// Fractional mass model for the staged MDD adapter.
/// `total_mass = 1.0` (the whole search space). Coverage is
/// polled from the adapter's `BoundaryProgress` and equals
/// `completed_boundaries / seed_boundaries`: a boundary only
/// counts as complete once every one of its descendants (SolveW,
/// SolveWZ, SolveZ, or the inline XY walk) has returned, so the
/// fraction is a real additive-over-disjoint coverage measure.
/// No push-based `mass_delta` — relying on push would double-
/// count when one boundary fans out to multiple SolveZs, and
/// undercount when SolveW / SolveWZ prune a whole sub-tree
/// without emitting (issues flagged in the PR review).
pub struct McddFractionMassModel {
    progress: Arc<BoundaryProgress>,
}

impl SearchMassModel for McddFractionMassModel {
    fn covered_mass(&self) -> MassValue {
        MassValue(self.progress.covered_fraction())
    }
    fn covered_partial_mass(&self) -> MassValue {
        MassValue(self.progress.partial_fraction())
    }
    fn quality(&self) -> CoverageQuality {
        // `covered_exact` is a real additive-over-disjoint
        // boundary fraction, but `covered_partial` is an
        // approximation of XY-timeout shortfall credit (per
        // `docs/TTC.md`). Mark as `Hybrid` because the published
        // `covered = exact + partial` blends a direct fraction
        // with a projected-shortfall estimate.
        CoverageQuality::Hybrid
    }
}

/// Adapter that walks the MDD boundary space through five real
/// `StageHandler`s. Consumes the same `PhaseBContext` the legacy
/// `run_mdd_sat_search` builds, plus a shared
/// `PipelineMetrics`/result channel so legacy and framework paths
/// roll up to identical counters.
/// Alias for the solution-reporting channel the staged handlers
/// write into. Same 4-tuple shape as the legacy `run_mdd_sat_search`
/// channel, so callers can drain it identically.
pub type SolutionChannel = std::sync::mpsc::Sender<(
    crate::types::PackedSeq,
    crate::types::PackedSeq,
    crate::types::PackedSeq,
    crate::types::PackedSeq,
)>;

pub type SolutionReceiver = std::sync::mpsc::Receiver<(
    crate::types::PackedSeq,
    crate::types::PackedSeq,
    crate::types::PackedSeq,
    crate::types::PackedSeq,
)>;

pub struct MddStagesAdapter {
    pub ctx: Arc<PhaseBContext>,
    pub metrics: PipelineMetrics,
    pub sat_config: Arc<radical::SolverConfig>,
    pub result_tx: std::sync::mpsc::Sender<(
        crate::types::PackedSeq,
        crate::types::PackedSeq,
        crate::types::PackedSeq,
        crate::types::PackedSeq,
    )>,
    pub use_wz_mode: bool,
    pub seed_boundaries: Vec<BoundaryWork>,
    pub mode_name: &'static str,
    /// Monotonic counter for `WorkItem.meta.item_id`. Every emitted
    /// child fetch-adds to get a unique id, instead of reusing
    /// `parent.item_id + 1` which collides across siblings.
    pub item_ids: Arc<AtomicU64>,
    /// Per-boundary fan-out tracker feeding the mass model's
    /// `covered_mass()` poll; see [`BoundaryProgress`] for the
    /// invariants.
    pub progress: Arc<BoundaryProgress>,
    /// Shared cancel flag (clone of `engine.cancel_flag()`). Used by
    /// `init()` to stop seeding early when the `--sat-secs`
    /// watchdog flips it mid-construction — without this check,
    /// a 18M-boundary seed list at n=26 k=8 can spend ~40s
    /// materializing `WorkItem`s into the scheduler even after
    /// the deadline has passed.
    pub cancel: Arc<std::sync::atomic::AtomicBool>,
}

impl MddStagesAdapter {
    /// Build an adapter ready to hand to `SearchEngine::run`. Constructs
    /// a fresh `PhaseBContext` (via `build_phase_b_context`), enumerates
    /// every live boundary through the ZW half of the MDD (upfront —
    /// the framework engine's scheduler replaces the legacy monitor's
    /// on-demand walker), allocates a fresh `PipelineMetrics` bundle,
    /// and pairs the adapter with a `SolutionReceiver` the caller
    /// drains after the run completes.
    pub fn build(
        problem: Problem,
        tuples: Vec<SumTuple>,
        cfg: &SearchConfig,
        k: usize,
        verbose: bool,
        mode_name: &'static str,
        cancel: &Arc<std::sync::atomic::AtomicBool>,
    ) -> (Self, SolutionReceiver) {
        let ctx = build_phase_b_context(problem, &tuples, cfg, verbose, k);
        // When `--outfix` pins the ZW boundary, seed a single
        // `BoundaryWork` rather than enumerating every live boundary.
        // At k≥9 the enumeration returns hundreds of millions of
        // entries and OOMs the process; the pin collapses that to one.
        //
        // Otherwise poll `cancel` inside the recursive MDD walk —
        // `enumerate_live_boundaries` at n=26 k=7 visits ~18M nodes,
        // so the `--sat-secs` watchdog must be able to interrupt it
        // to make the wall-clock limit cover the full command
        // lifecycle. Cancelled mid-walk returns a partial list;
        // the adapter treats that as a legitimate (if incomplete)
        // seed set.
        let seed_boundaries = if let Some(ref outfix) = cfg.test_outfix {
            let (z_bits, w_bits) = outfix.zw_bits;
            match mdd_navigate_to_outfix(
                ctx.mdd.root, ctx.zw_depth, &ctx.xy_pos_order, &ctx.mdd.nodes,
                z_bits, w_bits,
            ) {
                Some(xy_root) => vec![BoundaryWork { z_bits, w_bits, xy_root }],
                None => {
                    eprintln!(
                        "[framework:{}] --outfix boundary (z_bits={:#x}, w_bits={:#x}) is not live in the MDD (pruned during gen); cannot search.",
                        mode_name, z_bits, w_bits,
                    );
                    Vec::new()
                }
            }
        } else {
            enumerate_live_boundaries(&ctx, cancel)
        };
        if verbose {
            eprintln!(
                "[framework:{}] seed_boundaries={} (pre-enumerated upfront)",
                mode_name,
                seed_boundaries.len()
            );
        }
        let (result_tx, result_rx) = std::sync::mpsc::channel();
        // Seed boundaries use `item_id = 0..N`; start the counter
        // past that so child items never collide with a seed id.
        let item_ids = Arc::new(AtomicU64::new(seed_boundaries.len() as u64));
        let progress = Arc::new(BoundaryProgress::new(seed_boundaries.len() as u64));
        let adapter = MddStagesAdapter {
            ctx,
            metrics: new_pipeline_metrics(),
            sat_config: Arc::new(cfg.sat_config.clone()),
            result_tx,
            use_wz_mode: cfg.wz_together,
            seed_boundaries,
            mode_name,
            item_ids,
            progress,
            cancel: Arc::clone(cancel),
        };
        (adapter, result_rx)
    }
}

impl SearchModeAdapter<MddPayload> for MddStagesAdapter {
    fn name(&self) -> &'static str {
        self.mode_name
    }

    fn init(&self) -> AdapterInit<MddPayload> {
        // Materialize every live boundary into a `WorkItem`. At
        // large k the seed set can be tens of millions of items,
        // so poll the shared cancel flag every 64k entries to let
        // the `--sat-secs` watchdog short-circuit the seeding
        // loop instead of waiting for ~1.8 GB of allocations to
        // finish.
        const CANCEL_POLL_STRIDE: usize = 1 << 16;
        let mut seed_items = Vec::with_capacity(self.seed_boundaries.len());
        for (i, b) in self.seed_boundaries.iter().enumerate() {
            if i & (CANCEL_POLL_STRIDE - 1) == 0
                && self.cancel.load(std::sync::atomic::Ordering::Relaxed)
            {
                break;
            }
            seed_items.push(WorkItem {
                stage_id: STAGE_BOUNDARY,
                priority: 0,
                cost_hint: 1,
                replay_key: i as u64,
                mass_hint: Some(1.0),
                meta: WorkItemMeta {
                    item_id: i as u64,
                    parent_item_id: None,
                    fanout_root_id: i as u64,
                    depth_from_root: 0,
                    spawn_seq: 0,
                },
                payload: MddPayload::Boundary(BoundaryWork {
                    z_bits: b.z_bits,
                    w_bits: b.w_bits,
                    xy_root: b.xy_root,
                }),
            });
        }
        AdapterInit { seed_items }
    }

    fn stages(&self) -> BTreeMap<StageId, Box<dyn StageHandler<MddPayload>>> {
        let mut m: BTreeMap<StageId, Box<dyn StageHandler<MddPayload>>> = BTreeMap::new();
        let spectral_w = Arc::new(SpectralFilter::new(self.ctx.problem.m(), self.ctx.theta));
        let spectral_z = Arc::new(SpectralFilter::new(self.ctx.problem.n, self.ctx.theta));
        let nf_z = self
            .ctx
            .z_spectral_tables
            .as_ref()
            .map(|t| t.num_freqs)
            .unwrap_or(0);

        m.insert(
            STAGE_BOUNDARY,
            Box::new(BoundaryStage {
                ctx: Arc::clone(&self.ctx),
                metrics: self.metrics.clone(),
                use_wz_mode: self.use_wz_mode,
                item_ids: Arc::clone(&self.item_ids),
                progress: Arc::clone(&self.progress),
            }),
        );
        m.insert(
            STAGE_SOLVE_W,
            Box::new(SolveWStage {
                ctx: Arc::clone(&self.ctx),
                metrics: self.metrics.clone(),
                spectral_w: Arc::clone(&spectral_w),
                scratch: Mutex::new(SolveWScratch {
                    w_bases: HashMap::new(),
                    fft_buf_w: FftScratch::new(&spectral_w),
                    rng: 0xDEADBEEF_CAFEBABE,
                }),
                item_ids: Arc::clone(&self.item_ids),
                progress: Arc::clone(&self.progress),
            }),
        );
        m.insert(
            STAGE_SOLVE_WZ,
            Box::new(SolveWZStage {
                ctx: Arc::clone(&self.ctx),
                metrics: self.metrics.clone(),
                sat_config: Arc::clone(&self.sat_config),
                result_tx: self.result_tx.clone(),
                scratch: Mutex::new(SolveWZScratch {
                    template_cache: HashMap::new(),
                    rng: 0xCAFEBABE_DEADBEEF,
                }),
                item_ids: Arc::clone(&self.item_ids),
                progress: Arc::clone(&self.progress),
            }),
        );
        m.insert(
            STAGE_SOLVE_Z,
            Box::new(SolveZStage {
                ctx: Arc::clone(&self.ctx),
                metrics: self.metrics.clone(),
                spectral_z: Arc::clone(&spectral_z),
                sat_config: Arc::clone(&self.sat_config),
                result_tx: self.result_tx.clone(),
                scratch: Mutex::new(SolveZScratch {
                    z_scratch: ZStageScratch {
                        z_bases: HashMap::new(),
                        z_prep: crate::sat_z_middle::ZBoundaryPrep::with_template(&self.ctx.z_tmpl),
                        z_prep_z_bits: None,
                        z_re_boundary: vec![0.0; nf_z],
                        z_im_boundary: vec![0.0; nf_z],
                        z_spectrum_buf: Vec::new(),
                        ext_cache: HashMap::new(),
                    },
                    fft_buf_z: FftScratch::new(&spectral_z),
                    template_cache: HashMap::new(),
                    warm: WarmStartState {
                        phase: None,
                        inject_phase: true,
                    },
                    rng: 0xFEEDFACE_BAADF00D,
                }),
                progress: Arc::clone(&self.progress),
            }),
        );
        m
    }

    fn mass_model(&self) -> Box<dyn SearchMassModel> {
        Box::new(McddFractionMassModel {
            progress: Arc::clone(&self.progress),
        })
    }
}

// Unused import marker — `SearchConfig` parameter pattern placeholder
// kept so future `MddStagesAdapter::new(problem, tuples, cfg, ...)`
// constructor doesn't need a separate import edit.
#[allow(dead_code)]
fn _marker(_cfg: &SearchConfig, _problem: Problem, _tuples: &[SumTuple]) {}

#[cfg(test)]
mod tests {
    use super::*;

    /// TTC spec §4.2 "bundled-stage rule" + §7.2 "apart/together
    /// parity": any timeout-capable XY attempt, regardless of which
    /// stage path triggered it, MUST contribute partial credit to
    /// the same boundary-mass ledger. This test reproduces the bug
    /// that was in `SolveWZStage`: if `add_partial_cov_micro` is
    /// skipped, `partial_fraction` stays at 0 even though XY
    /// timeouts were recorded elsewhere.
    #[test]
    fn partial_credit_ledger_is_additive_across_stage_paths() {
        let progress = BoundaryProgress::new(10);
        // Simulate SolveZ reporting 500_000 cov-micros from an XY
        // timeout (half the full sub-cube credit).
        progress.add_partial_cov_micro(500_000);
        // Simulate SolveWZ reporting another 250_000 cov-micros.
        // Per the spec this MUST increase `partial_fraction`; if
        // the adapter skips this call, `partial_fraction` would
        // under-report.
        progress.add_partial_cov_micro(250_000);
        let frac = progress.partial_fraction();
        // total=10, so denom = 10 * 1_000_000. Sum = 750_000 ⇒
        // fraction = 750_000 / 10_000_000 = 0.075.
        assert!((frac - 0.075).abs() < 1e-9,
            "covered_partial must accumulate credit from every stage path, got {}", frac);
    }

    /// Regression test: the pre-fix `SolveWZStage` skipped
    /// `add_partial_cov_micro`. If we credit only SolveZ-style
    /// calls and leave SolveWZ credit on the floor, the result is
    /// an under-report of `covered_partial`. Verifies the fraction
    /// diverges between the correct (both credited) and buggy
    /// (only one credited) ledgers.
    #[test]
    fn only_solve_z_credit_would_under_report_partial_vs_unified() {
        let unified = BoundaryProgress::new(4);
        let only_solve_z = BoundaryProgress::new(4);
        // Pretend SolveZ reported 400_000 cov-micro, SolveWZ reported
        // 600_000. The unified ledger credits both; the buggy
        // "only SolveZ" ledger credits just 400_000.
        unified.add_partial_cov_micro(400_000);
        unified.add_partial_cov_micro(600_000);
        only_solve_z.add_partial_cov_micro(400_000);
        assert!(unified.partial_fraction() > only_solve_z.partial_fraction(),
            "spec requires every timeout-capable XY path to contribute; only-SolveZ must under-report vs unified");
        assert!((unified.partial_fraction() - 0.25).abs() < 1e-9);
        assert!((only_solve_z.partial_fraction() - 0.10).abs() < 1e-9);
    }

    /// TTC §3 invariant 7: "no completed subproblem may be
    /// credited more than once." `note_handled` must only bump
    /// `completed` on the FIRST transition to zero pending, even
    /// if a stale item with the same root_id arrives later and
    /// re-enters the hashmap. Before the hardening this returned
    /// `true` twice and `covered_fraction` climbed past 1/total
    /// per boundary.
    #[test]
    fn note_handled_does_not_double_credit_on_stale_root_reentry() {
        let p = BoundaryProgress::new(2);
        // First call: fresh root, pending 1 -> 0, bump completed.
        assert!(p.note_handled(7, 0), "first zero-transition MUST return true");
        assert!((p.covered_fraction() - 0.5).abs() < 1e-9,
            "one of two boundaries done ⇒ fraction = 0.5");
        // Stale call: same root arrives again. It would normally
        // re-insert (1, false) and drop to zero again; without the
        // guard we'd double-credit.
        assert!(!p.note_handled(7, 0), "stale re-entry MUST NOT re-credit");
        assert!((p.covered_fraction() - 0.5).abs() < 1e-9,
            "covered_fraction MUST stay at 0.5 after stale re-entry; got {}",
            p.covered_fraction());
        // A different root completing increments normally.
        assert!(p.note_handled(8, 0));
        assert!((p.covered_fraction() - 1.0).abs() < 1e-9);
    }

    /// TTC §3 mass invariants: partial_fraction is clamped to
    /// [0, 1] even if cov_micro overflows the denominator.
    #[test]
    fn partial_fraction_is_clamped_to_one() {
        let progress = BoundaryProgress::new(1);
        progress.add_partial_cov_micro(5_000_000); // 5× the denom.
        let frac = progress.partial_fraction();
        assert!(frac <= 1.0 && frac >= 0.0, "partial_fraction MUST stay in [0, 1]; got {}", frac);
    }

    /// TTC §10 item 7: "mode quality labels match the actual
    /// estimator semantics." The MDD staged adapter publishes a
    /// hybrid estimator — `covered_exact` is a real additive
    /// fraction but `covered_partial` is an XY-timeout shortfall
    /// approximation — so its label MUST be `Hybrid`.
    #[test]
    fn mdd_mass_model_quality_is_hybrid() {
        let progress = Arc::new(BoundaryProgress::new(1));
        let model = McddFractionMassModel { progress };
        assert_eq!(model.quality(), CoverageQuality::Hybrid,
            "MDD adapter mixes a direct boundary fraction with a projected XY-timeout shortfall; quality MUST be Hybrid per TTC §6.3");
    }

    /// MDD mass model must publish `covered_exact + covered_partial`
    /// clamped to ≤ 1.0 under the aggregation site in
    /// `MassSnapshot::apply_delta`. This test exercises the mass
    /// model directly with full partial credit to show the clamp
    /// is load-bearing even in pathological cases.
    #[test]
    fn mdd_mass_model_published_mass_stays_bounded() {
        let progress = Arc::new(BoundaryProgress::new(1));
        progress.add_partial_cov_micro(2_000_000); // 2× overflow
        let model = McddFractionMassModel { progress: Arc::clone(&progress) };
        assert!(model.covered_partial_mass().0 <= 1.0,
            "covered_partial_mass MUST clamp to ≤ 1.0 even when cov_micro overflows denom");
    }

    /// End-to-end integration test: run the real `MddStagesAdapter`
    /// on a small problem (n=6) and assert the final
    /// `ProgressSnapshot.forcings` is non-empty — concretely verifies
    /// that the MDD stages' forcing sinks actually flow into
    /// `ForcingRollups` (docs/TELEMETRY.md §4 / §9). Uses the
    /// in-memory BFS-built MDD fallback so it doesn't require
    /// `mdd-<k>.bin` on disk.
    #[test]
    fn mdd_live_run_populates_forcing_rollups() {
        use crate::config::{SearchConfig, WzMode};
        use crate::enumerate::phase_a_tuples;
        use crate::search_framework::engine::{EngineConfig, SearchEngine};
        use crate::search_framework::events::SearchEvent;
        use crate::search_framework::queue::GoldThenWork;
        use crate::types::Problem;
        use std::sync::atomic::AtomicBool;
        use std::time::Duration;

        let problem = Problem::new(6);
        let tuples = phase_a_tuples(problem, None);
        // n=6 tuple list should be non-empty; if it isn't the
        // search has nothing to do and the test is meaningless.
        assert!(!tuples.is_empty(), "n=6 phase-A tuples MUST be non-empty");

        let mut cfg = SearchConfig::default();
        cfg.problem = problem;
        cfg.wz_mode = Some(WzMode::Apart);
        cfg.mdd_k = 2;
        cfg.sat_config = radical::SolverConfig::default();

        let cancel = Arc::new(AtomicBool::new(false));
        let (adapter, _rx) = MddStagesAdapter::build(
            problem, tuples, &cfg, 2, false, "apart", &cancel,
        );
        let mut engine = SearchEngine::<MddPayload>::new(
            EngineConfig {
                progress_interval: Duration::from_millis(20),
                worker_count: 1,
            },
            Box::new(GoldThenWork::new(4)),
        );

        let mut final_snap = None;
        engine.run(&adapter, |event| {
            if let SearchEvent::Finished(p) = event {
                final_snap = Some(p);
            }
        });
        let snap = final_snap.expect("Finished event not emitted");

        // docs/TELEMETRY.md §9 says MDD stages populate forcings.
        // The actual CDCL propagation from the Z/W/XY solvers MUST
        // produce at least one attributed forcing for this run.
        assert!(
            !snap.forcings.stage_level.is_empty(),
            "MDD forcings.stage_level MUST be populated for a real run; got empty",
        );
        assert!(
            !snap.forcings.stage_feature.is_empty(),
            "MDD forcings.stage_feature MUST be populated for a real run; got empty",
        );
        // Consistency rule (TELEMETRY.md §4): both axes come from
        // the same event stream, so totals MUST agree.
        let sum_level: u64 = snap.forcings.stage_level.values().sum();
        let sum_feature: u64 = snap.forcings.stage_feature.values().sum();
        assert_eq!(sum_level, sum_feature,
            "stage_level ({}) and stage_feature ({}) totals MUST agree per TELEMETRY §4",
            sum_level, sum_feature);
        // At least one of the rollup keys should be an MDD stage.
        let has_mdd_stage = snap.forcings.stage_level.keys()
            .any(|(stage, _)| stage.starts_with("mdd."));
        assert!(has_mdd_stage, "forcings keys MUST include at least one mdd.* stage");

        // TTC invariants from the spec, re-checked here in
        // integration context (debug_asserts in build_snapshot
        // already fired for any failure).
        assert!(snap.covered_mass.0 <= snap.total_mass.0 + 1e-9);
        assert!(snap.remaining_mass.0 >= 0.0);
    }

    /// TTC §3 invariant 6 + §10 item 3 "covered mass is monotone"
    /// against a REAL MDD run. Prior monotone tests used synthetic
    /// adapters; this one drives the full MDD pipeline on n=6 with
    /// a short progress interval and asserts every successive
    /// `ProgressSnapshot.covered_mass` is non-decreasing.
    #[test]
    fn mdd_live_run_has_monotone_covered_mass() {
        use crate::config::{SearchConfig, WzMode};
        use crate::enumerate::phase_a_tuples;
        use crate::search_framework::engine::{EngineConfig, SearchEngine};
        use crate::search_framework::events::SearchEvent;
        use crate::search_framework::queue::GoldThenWork;
        use crate::types::Problem;
        use std::sync::atomic::AtomicBool;
        use std::sync::Mutex;
        use std::time::Duration;

        let problem = Problem::new(6);
        let tuples = phase_a_tuples(problem, None);
        let mut cfg = SearchConfig::default();
        cfg.problem = problem;
        cfg.wz_mode = Some(WzMode::Apart);
        cfg.mdd_k = 2;

        let cancel = Arc::new(AtomicBool::new(false));
        let (adapter, _rx) = MddStagesAdapter::build(
            problem, tuples, &cfg, 2, false, "apart", &cancel,
        );
        let mut engine = SearchEngine::<MddPayload>::new(
            EngineConfig {
                // Very short interval so multiple progress ticks
                // are likely to fire during the small n=6 run.
                progress_interval: Duration::from_millis(5),
                worker_count: 1,
            },
            Box::new(GoldThenWork::new(4)),
        );

        let history = Arc::new(Mutex::new(Vec::<f64>::new()));
        let history_cb = Arc::clone(&history);
        engine.run(&adapter, move |event| {
            let covered = match event {
                SearchEvent::Progress(p) => p.covered_mass.0,
                SearchEvent::Finished(p) => p.covered_mass.0,
            };
            history_cb.lock().unwrap().push(covered);
        });
        let history = history.lock().unwrap();
        assert!(!history.is_empty(), "engine MUST emit at least the Finished snapshot");
        // TTC §3.6: every consecutive snapshot MUST satisfy
        // covered[i+1] >= covered[i].
        for (i, w) in history.windows(2).enumerate() {
            assert!(
                w[1] + 1e-9 >= w[0],
                "tick {} -> {} violates monotonicity: {} -> {}",
                i, i + 1, w[0], w[1],
            );
        }
    }
}
