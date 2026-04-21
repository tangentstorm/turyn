//! Framework adapter for `--wz=sync`.
//!
//! The sync walker (`sync_walker::search_sync`) is a self-contained
//! parallel DFS that owns its own thread-pool and shared `cancel`
//! flag; per-level `ForcingDelta` telemetry integration is a future
//! refactor. This v1 adapter wraps the whole walk as a single
//! `SyncWalkStage` — `--engine=new --wz=sync` routes through
//! `SearchEngine::run` purely so the universal `ProgressSnapshot`
//! schema (elapsed, covered/total, TTC, forcings rollups) applies
//! uniformly.
//!
//! Coverage semantics: `total_mass = 1.0`, credited as `1.0` on
//! completion (one walker-node unit). When future work lifts the
//! per-level coverage product from `SyncStats` into
//! `StageOutcome::forcings`, this becomes true coverage-bits.

use std::collections::BTreeMap;
use std::sync::Arc;

use crate::search_framework::engine::{AdapterInit, SearchModeAdapter};
use crate::search_framework::mass::{CoverageQuality, MassDelta, MassValue, SearchMassModel};
use crate::search_framework::stage::{
    StageContext, StageHandler, StageId, StageOutcome, WorkItem, WorkItemMeta,
};
use crate::sync_walker::{search_sync, SyncConfig};
use crate::types::{PackedSeq, Problem};

pub const STAGE_SYNC_WALK: StageId = "sync.walk";

#[derive(Clone, Debug, Default)]
pub struct SyncPayload;

pub struct SyncWalkStage {
    problem: Problem,
    cfg: Arc<SyncConfig>,
    verbose: bool,
    result_tx: std::sync::mpsc::Sender<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>,
}

impl StageHandler<SyncPayload> for SyncWalkStage {
    fn id(&self) -> StageId {
        STAGE_SYNC_WALK
    }
    fn handle(
        &self,
        _item: WorkItem<SyncPayload>,
        _ctx: &StageContext<'_>,
    ) -> StageOutcome<SyncPayload> {
        let (found, _stats, _elapsed) = search_sync(self.problem, &self.cfg, self.verbose);
        if let Some(sol) = found {
            let _ = self.result_tx.send(sol);
        }
        let mut out = StageOutcome::default();
        out.mass_delta = MassDelta {
            covered_exact: MassValue(1.0),
            covered_partial: MassValue::ZERO,
        };
        out
    }
}

pub struct SyncWalkMassModel;

impl SearchMassModel for SyncWalkMassModel {
    fn total_mass(&self) -> MassValue {
        MassValue(1.0)
    }
    fn covered_mass(&self) -> MassValue {
        MassValue::ZERO
    }
    fn quality(&self) -> CoverageQuality {
        // The walker is exhaustive within its budget, but the single
        // `1.0` unit is coarse; mark as projected pending the
        // per-level coverage-bits upgrade.
        CoverageQuality::Projected
    }
}

pub struct SyncAdapter {
    pub problem: Problem,
    pub cfg: Arc<SyncConfig>,
    pub verbose: bool,
    pub result_tx: std::sync::mpsc::Sender<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>,
}

impl SyncAdapter {
    pub fn build(
        problem: Problem,
        cfg: SyncConfig,
        verbose: bool,
    ) -> (
        Self,
        std::sync::mpsc::Receiver<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>,
    ) {
        let (result_tx, result_rx) = std::sync::mpsc::channel();
        (
            SyncAdapter {
                problem,
                cfg: Arc::new(cfg),
                verbose,
                result_tx,
            },
            result_rx,
        )
    }
}

impl SearchModeAdapter<SyncPayload> for SyncAdapter {
    fn name(&self) -> &'static str {
        "sync"
    }
    fn init(&self) -> AdapterInit<SyncPayload> {
        // Single seed: the walker is internally parallel and one
        // `handle` call runs the full DFS.
        let seed_items = vec![WorkItem {
            stage_id: STAGE_SYNC_WALK,
            priority: 0,
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
            payload: SyncPayload,
        }];
        AdapterInit { seed_items }
    }
    fn stages(&self) -> BTreeMap<StageId, Box<dyn StageHandler<SyncPayload>>> {
        let mut m: BTreeMap<StageId, Box<dyn StageHandler<SyncPayload>>> = BTreeMap::new();
        m.insert(
            STAGE_SYNC_WALK,
            Box::new(SyncWalkStage {
                problem: self.problem,
                cfg: Arc::clone(&self.cfg),
                verbose: self.verbose,
                result_tx: self.result_tx.clone(),
            }),
        );
        m
    }
    fn mass_model(&self) -> Box<dyn SearchMassModel> {
        Box::new(SyncWalkMassModel)
    }
}
