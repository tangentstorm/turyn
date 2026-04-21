//! Framework adapter for `--stochastic` / `turyn guess
//! --stochastic`. Wraps `stochastic::stochastic_search` as a
//! single-stage handler. The stochastic path is inherently non-
//! exhaustive, so the mass model declares its coverage quality as
//! [`CoverageQuality::Projected`] and keeps `total_mass = 1.0`
//! (one "run" unit) — consistent with the spec's v1 stochastic
//! mapping.

use std::collections::BTreeMap;

use crate::search_framework::engine::{AdapterInit, SearchModeAdapter};
use crate::search_framework::mass::{CoverageQuality, MassDelta, MassValue, SearchMassModel};
use crate::search_framework::stage::{
    StageContext, StageHandler, StageId, StageOutcome, WorkItem, WorkItemMeta,
};
use crate::stochastic::stochastic_search;
use crate::types::{Problem, SumTuple};

pub const STAGE_STOCHASTIC: StageId = "stochastic.search";

#[derive(Clone, Debug, Default)]
pub struct StochasticPayload;

pub struct StochasticStage {
    problem: Problem,
    test_tuple: Option<SumTuple>,
    verbose: bool,
    time_limit_secs: u64,
    found: std::sync::Arc<std::sync::atomic::AtomicBool>,
}

impl StageHandler<StochasticPayload> for StochasticStage {
    fn id(&self) -> StageId {
        STAGE_STOCHASTIC
    }
    fn handle(
        &self,
        _item: WorkItem<StochasticPayload>,
        _ctx: &StageContext<'_>,
    ) -> StageOutcome<StochasticPayload> {
        let report = stochastic_search(
            self.problem,
            self.test_tuple.as_ref(),
            self.verbose,
            self.time_limit_secs,
        );
        if report.found_solution {
            self.found
                .store(true, std::sync::atomic::Ordering::Relaxed);
        }
        let mut out = StageOutcome::default();
        out.mass_delta = MassDelta {
            covered_exact: MassValue(1.0),
            covered_partial: MassValue::ZERO,
        };
        out
    }
}

pub struct StochasticMassModel;

impl SearchMassModel for StochasticMassModel {
    fn total_mass(&self) -> MassValue {
        MassValue(1.0)
    }
    fn covered_mass(&self) -> MassValue {
        MassValue::ZERO
    }
    fn quality(&self) -> CoverageQuality {
        CoverageQuality::Projected
    }
}

pub struct StochasticAdapter {
    pub problem: Problem,
    pub test_tuple: Option<SumTuple>,
    pub verbose: bool,
    pub time_limit_secs: u64,
    pub found: std::sync::Arc<std::sync::atomic::AtomicBool>,
}

impl StochasticAdapter {
    pub fn build(
        problem: Problem,
        test_tuple: Option<SumTuple>,
        verbose: bool,
        time_limit_secs: u64,
    ) -> (Self, std::sync::Arc<std::sync::atomic::AtomicBool>) {
        let found = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        (
            StochasticAdapter {
                problem,
                test_tuple,
                verbose,
                time_limit_secs,
                found: std::sync::Arc::clone(&found),
            },
            found,
        )
    }
}

impl SearchModeAdapter<StochasticPayload> for StochasticAdapter {
    fn name(&self) -> &'static str {
        "stochastic"
    }
    fn init(&self) -> AdapterInit<StochasticPayload> {
        AdapterInit {
            seed_items: vec![WorkItem {
                stage_id: STAGE_STOCHASTIC,
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
                payload: StochasticPayload,
            }],
        }
    }
    fn stages(&self) -> BTreeMap<StageId, Box<dyn StageHandler<StochasticPayload>>> {
        let mut m: BTreeMap<StageId, Box<dyn StageHandler<StochasticPayload>>> = BTreeMap::new();
        m.insert(
            STAGE_STOCHASTIC,
            Box::new(StochasticStage {
                problem: self.problem,
                test_tuple: self.test_tuple,
                verbose: self.verbose,
                time_limit_secs: self.time_limit_secs,
                found: std::sync::Arc::clone(&self.found),
            }),
        );
        m
    }
    fn mass_model(&self) -> Box<dyn SearchMassModel> {
        Box::new(StochasticMassModel)
    }
}
