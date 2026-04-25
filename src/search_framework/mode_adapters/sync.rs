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
//! Coverage semantics: `total_mass = 1.0`; `covered_mass` is read
//! from the walker's projected-fraction hook at end of run
//! (`SyncConfig::projected_fraction_ppm`), so the universal
//! `ProgressSnapshot.ttc` is non-`None` for sync mode. Quality stays
//! `Projected` — the sync walker's own Block-2/Block-3 telemetry is
//! authoritative for mid-run progress.

use std::collections::BTreeMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::search_framework::engine::{AdapterInit, SearchModeAdapter};
use crate::search_framework::mass::{CoverageQuality, MassValue, SearchMassModel};
use crate::search_framework::stage::{
    StageContext, StageHandler, StageId, StageOutcome, WorkItem, WorkItemMeta,
};
use crate::sync_walker::{SyncConfig, search_sync};
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
        let (found, stats, _elapsed) = search_sync(self.problem, &self.cfg, self.verbose);
        if let Some(sol) = found {
            let _ = self.result_tx.send(sol);
        }
        // No `mass_delta` credit here. The walker's projected-
        // fraction covered flows through the pull-polled mass
        // model (`SyncWalkMassModel::covered_mass`), so the
        // universal `ProgressSnapshot.ttc` reflects the walker's
        // own projection rather than a bogus "1.0 at end"
        // saturation the handler would otherwise trigger.
        let mut out = StageOutcome::default();
        // Flatten the sync walker's aggregated
        // `forced_by_level_kind[level][kind]` matrix into the
        // universal `(level, feature, count)` triples. The
        // walker aggregates per-worker counters across every
        // CDCL solver it owns, so this attributes all sync SAT
        // propagation to the sync stage — matching the
        // `docs/TELEMETRY.md` §4 attribution rule.
        let mut triples: Vec<(u16, u8, u32)> = Vec::new();
        for (level, row) in stats.forced_by_level_kind.iter().enumerate() {
            for (kind, &count) in row.iter().enumerate() {
                if count > 0 {
                    triples.push((level as u16, kind as u8, count.min(u32::MAX as u64) as u32));
                }
            }
        }
        out.forcings = crate::search_framework::stage::ForcingDelta {
            by_level_feature: triples,
        };
        out
    }
}

pub struct SyncWalkMassModel {
    projected_fraction_ppm: Arc<AtomicU64>,
    problem_n: usize,
}

impl SearchMassModel for SyncWalkMassModel {
    fn covered_mass(&self) -> MassValue {
        // Walker writes its projected-fraction covered as
        // parts-per-million. Engine polls this on each progress
        // tick and at Finished — at which point it's non-zero and
        // `ProgressSnapshot.ttc` becomes meaningful.
        let ppm = self.projected_fraction_ppm.load(Ordering::Relaxed);
        MassValue(ppm as f64 / 1_000_000.0)
    }
    fn quality(&self) -> CoverageQuality {
        // Fraction is derived from a branching-factor projection —
        // not a direct count of covered nodes — so quality stays
        // `Projected`. Consumers should pair it with the walker's
        // own per-level telemetry for authoritative analysis.
        CoverageQuality::Projected
    }
    fn total_log2_work(&self) -> Option<f64> {
        Some(2.0 * self.problem_n as f64)
    }
}

pub struct SyncAdapter {
    pub problem: Problem,
    pub cfg: Arc<SyncConfig>,
    pub verbose: bool,
    pub result_tx: std::sync::mpsc::Sender<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>,
    pub projected_fraction_ppm: Arc<AtomicU64>,
}

impl SyncAdapter {
    pub fn build(
        problem: Problem,
        mut cfg: SyncConfig,
        verbose: bool,
    ) -> (
        Self,
        std::sync::mpsc::Receiver<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>,
    ) {
        let (result_tx, result_rx) = std::sync::mpsc::channel();
        // Install the projected-fraction sink on the cloned cfg the
        // walker sees. A fresh atomic per adapter so concurrent runs
        // don't clobber each other.
        let projected_fraction_ppm = Arc::new(AtomicU64::new(0));
        cfg.projected_fraction_ppm = Some(Arc::clone(&projected_fraction_ppm));
        (
            SyncAdapter {
                problem,
                cfg: Arc::new(cfg),
                verbose,
                result_tx,
                projected_fraction_ppm,
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
        Box::new(SyncWalkMassModel {
            projected_fraction_ppm: Arc::clone(&self.projected_fraction_ppm),
            problem_n: self.problem.n,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// TTC §7.3 + §10 item 7: sync publishes a branching-factor
    /// projection, not a direct count. Quality MUST be `Projected`.
    #[test]
    fn sync_mass_model_is_projected() {
        let model = SyncWalkMassModel {
            projected_fraction_ppm: Arc::new(AtomicU64::new(0)),
            problem_n: 26,
        };
        assert_eq!(
            model.quality(),
            CoverageQuality::Projected,
            "sync fraction is an estimator output; quality MUST be Projected per TTC §7.3"
        );
    }
}
