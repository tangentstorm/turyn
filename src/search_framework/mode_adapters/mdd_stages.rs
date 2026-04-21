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
use std::sync::{Arc, Mutex};

use crate::config::SearchConfig;
use crate::mdd_pipeline::{
    process_boundary, process_solve_w, process_solve_wz, process_solve_xy, process_solve_z,
    BoundaryWork, PhaseBContext, PipelineMetrics, PipelineWork, SolveWWork, SolveWZWork,
    SolveXYWork, SolveZWork, ZStageScratch,
};
use crate::search_framework::engine::{AdapterInit, SearchModeAdapter};
use crate::search_framework::mass::{CoverageQuality, MassValue, SearchMassModel};
use crate::search_framework::stage::{
    StageContext, StageHandler, StageId, StageOutcome, WorkItem, WorkItemMeta,
};
use crate::xy_sat::SatXYTemplate;
use crate::legacy_search::WarmStartState;
use crate::spectrum::{FftScratch, SpectralFilter};
use crate::types::{Problem, SumTuple};

pub const STAGE_BOUNDARY: StageId = "mdd.boundary";
pub const STAGE_SOLVE_W: StageId = "mdd.solve_w";
pub const STAGE_SOLVE_WZ: StageId = "mdd.solve_wz";
pub const STAGE_SOLVE_Z: StageId = "mdd.solve_z";
pub const STAGE_SOLVE_XY: StageId = "mdd.solve_xy";

/// Payload discriminator for the framework `WorkItem<MddPayload>`.
/// Mirrors `PipelineWork` (minus the internal `Shutdown`) so each
/// stage handler can pull out its expected variant.
pub enum MddPayload {
    Boundary(BoundaryWork),
    SolveW(SolveWWork),
    SolveWZ(SolveWZWork),
    SolveZ(SolveZWork),
    SolveXY(SolveXYWork),
}

impl MddPayload {
    fn stage_id(&self) -> StageId {
        match self {
            MddPayload::Boundary(_) => STAGE_BOUNDARY,
            MddPayload::SolveW(_) => STAGE_SOLVE_W,
            MddPayload::SolveWZ(_) => STAGE_SOLVE_WZ,
            MddPayload::SolveZ(_) => STAGE_SOLVE_Z,
            MddPayload::SolveXY(_) => STAGE_SOLVE_XY,
        }
    }
}

fn from_pipeline_work(work: PipelineWork) -> Option<MddPayload> {
    match work {
        PipelineWork::Boundary(b) => Some(MddPayload::Boundary(b)),
        PipelineWork::SolveW(w) => Some(MddPayload::SolveW(w)),
        PipelineWork::SolveWZ(wz) => Some(MddPayload::SolveWZ(wz)),
        PipelineWork::SolveZ(z) => Some(MddPayload::SolveZ(z)),
        PipelineWork::SolveXY(xy) => Some(MddPayload::SolveXY(xy)),
        PipelineWork::Shutdown => None,
    }
}

fn wrap_items(items: Vec<PipelineWork>, parent: &WorkItemMeta) -> Vec<WorkItem<MddPayload>> {
    items
        .into_iter()
        .filter_map(|pw| {
            let payload = from_pipeline_work(pw)?;
            let stage_id = payload.stage_id();
            Some(WorkItem {
                stage_id,
                priority: default_priority_for_stage(stage_id),
                cost_hint: 1,
                replay_key: parent.item_id,
                mass_hint: None,
                meta: WorkItemMeta {
                    item_id: parent.item_id.wrapping_add(1),
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
    // The legacy scheduler prioritizes later stages and high-
    // quality gold XY candidates. Approximate: Boundary=0,
    // SolveW/SolveWZ=1, SolveZ=2, SolveXY=3 (gold).
    match stage {
        STAGE_BOUNDARY => 0,
        STAGE_SOLVE_W | STAGE_SOLVE_WZ => 1,
        STAGE_SOLVE_Z => 2,
        STAGE_SOLVE_XY => 3,
        _ => 0,
    }
}

pub struct BoundaryStage {
    ctx: Arc<PhaseBContext>,
    metrics: PipelineMetrics,
    use_wz_mode: bool,
}

impl StageHandler<MddPayload> for BoundaryStage {
    fn id(&self) -> StageId {
        STAGE_BOUNDARY
    }
    fn handle(
        &self,
        item: WorkItem<MddPayload>,
        _ctx: &StageContext<'_>,
    ) -> StageOutcome<MddPayload> {
        let parent_meta = item.meta;
        let MddPayload::Boundary(bnd) = item.payload else {
            return StageOutcome::default();
        };
        let emitted_raw = process_boundary(bnd, &self.ctx, &self.metrics, self.use_wz_mode);
        let mut out = StageOutcome::default();
        out.emitted = wrap_items(emitted_raw, &parent_meta);
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
}

impl StageHandler<MddPayload> for SolveWStage {
    fn id(&self) -> StageId {
        STAGE_SOLVE_W
    }
    fn handle(
        &self,
        item: WorkItem<MddPayload>,
        _ctx: &StageContext<'_>,
    ) -> StageOutcome<MddPayload> {
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
        let emitted_raw = process_solve_w(
            sw,
            &self.ctx,
            &self.metrics,
            w_bases,
            &self.spectral_w,
            fft_buf_w,
            rng,
        );
        let mut out = StageOutcome::default();
        out.emitted = wrap_items(emitted_raw, &parent_meta);
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
}

impl StageHandler<MddPayload> for SolveWZStage {
    fn id(&self) -> StageId {
        STAGE_SOLVE_WZ
    }
    fn handle(
        &self,
        item: WorkItem<MddPayload>,
        _ctx: &StageContext<'_>,
    ) -> StageOutcome<MddPayload> {
        let parent_meta = item.meta;
        let MddPayload::SolveWZ(swz) = item.payload else {
            return StageOutcome::default();
        };
        let mut guard = self.scratch.lock().unwrap();
        let SolveWZScratch {
            template_cache,
            rng,
        } = &mut *guard;
        let deferred = process_solve_wz(
            swz,
            &self.ctx,
            &self.metrics,
            template_cache,
            &self.sat_config,
            &self.result_tx,
            rng,
        );
        let mut out = StageOutcome::default();
        if let Some((item, _priority)) = deferred {
            // Framework priority is i32 (coarse tag); legacy f64
            // continuation priority is dropped. Re-enqueue as
            // low-priority "maybe".
            out.emitted = wrap_items(vec![item], &parent_meta)
                .into_iter()
                .map(|mut w| {
                    w.priority = 1;
                    w
                })
                .collect();
        }
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
}

impl StageHandler<MddPayload> for SolveZStage {
    fn id(&self) -> StageId {
        STAGE_SOLVE_Z
    }
    fn handle(
        &self,
        item: WorkItem<MddPayload>,
        _ctx: &StageContext<'_>,
    ) -> StageOutcome<MddPayload> {
        let _parent_meta = item.meta;
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
        // `process_solve_z` is terminal (no follow-up items emitted
        // via the queue — it fires XY solves inline and reports
        // solutions through `result_tx`). Returns nothing.
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
        );
        StageOutcome::default()
    }
}

struct SolveXYScratch {
    template_cache: HashMap<Vec<(i32, i32, i32, i32)>, SatXYTemplate>,
    warm: WarmStartState,
}

pub struct SolveXYStage {
    ctx: Arc<PhaseBContext>,
    metrics: PipelineMetrics,
    sat_config: Arc<radical::SolverConfig>,
    result_tx: std::sync::mpsc::Sender<(
        crate::types::PackedSeq,
        crate::types::PackedSeq,
        crate::types::PackedSeq,
        crate::types::PackedSeq,
    )>,
    scratch: Mutex<SolveXYScratch>,
}

impl StageHandler<MddPayload> for SolveXYStage {
    fn id(&self) -> StageId {
        STAGE_SOLVE_XY
    }
    fn handle(
        &self,
        item: WorkItem<MddPayload>,
        _ctx: &StageContext<'_>,
    ) -> StageOutcome<MddPayload> {
        let MddPayload::SolveXY(xy) = item.payload else {
            return StageOutcome::default();
        };
        let mut guard = self.scratch.lock().unwrap();
        let SolveXYScratch {
            template_cache,
            warm,
        } = &mut *guard;
        process_solve_xy(
            xy,
            &self.ctx,
            &self.metrics,
            template_cache,
            warm,
            &self.sat_config,
            &self.result_tx,
        );
        StageOutcome::default()
    }
}

/// Trivial boundary-count mass model for the staged MDD adapter.
/// Not a meaningful coverage-bits unit yet; hooks the framework's
/// TTC pipeline for progress reporting.
pub struct BoundaryCountMassModel {
    total: MassValue,
}

impl SearchMassModel for BoundaryCountMassModel {
    fn total_mass(&self) -> MassValue {
        self.total
    }
    fn covered_mass(&self) -> MassValue {
        MassValue::ZERO
    }
    fn quality(&self) -> CoverageQuality {
        CoverageQuality::Estimated
    }
}

/// Adapter that walks the MDD boundary space through five real
/// `StageHandler`s. Consumes the same `PhaseBContext` the legacy
/// `run_mdd_sat_search` builds, plus a shared
/// `PipelineMetrics`/result channel so legacy and framework paths
/// roll up to identical counters.
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
}

impl SearchModeAdapter<MddPayload> for MddStagesAdapter {
    fn name(&self) -> &'static str {
        self.mode_name
    }

    fn init(&self) -> AdapterInit<MddPayload> {
        let seed_items = self
            .seed_boundaries
            .iter()
            .enumerate()
            .map(|(i, b)| WorkItem {
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
            })
            .collect();
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
            }),
        );
        m.insert(
            STAGE_SOLVE_XY,
            Box::new(SolveXYStage {
                ctx: Arc::clone(&self.ctx),
                metrics: self.metrics.clone(),
                sat_config: Arc::clone(&self.sat_config),
                result_tx: self.result_tx.clone(),
                scratch: Mutex::new(SolveXYScratch {
                    template_cache: HashMap::new(),
                    warm: WarmStartState {
                        phase: None,
                        inject_phase: true,
                    },
                }),
            }),
        );
        m
    }

    fn mass_model(&self) -> Box<dyn SearchMassModel> {
        Box::new(BoundaryCountMassModel {
            total: MassValue(self.seed_boundaries.len() as f64),
        })
    }
}

// Unused import marker — `SearchConfig` parameter pattern placeholder
// kept so future `MddStagesAdapter::new(problem, tuples, cfg, ...)`
// constructor doesn't need a separate import edit.
#[allow(dead_code)]
fn _marker(_cfg: &SearchConfig, _problem: Problem, _tuples: &[SumTuple]) {}
