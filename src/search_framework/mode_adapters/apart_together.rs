use std::collections::BTreeMap;
use std::sync::Arc;

use crate::config::SearchConfig;
use crate::legacy_search::SearchReport;
use crate::mdd_pipeline::run_mdd_sat_search;
use crate::search_framework::engine::{AdapterInit, SearchModeAdapter};
use crate::search_framework::mass::{CoverageQuality, MassDelta, MassValue, SearchMassModel};
use crate::search_framework::stage::{StageHandler, StageId, StageOutcome, WorkItem, WorkItemMeta};
use crate::types::{Problem, SumTuple};

pub const STAGE_TUPLE_SOLVE: StageId = "tuple_solve";

#[derive(Clone, Debug, Default)]
pub struct TuplePayload {
    pub tuple_idx: usize,
}

pub struct TupleCountMassModel {
    total: MassValue,
}

impl TupleCountMassModel {
    pub fn new(total: usize) -> Self {
        Self {
            total: MassValue(total as f64),
        }
    }
}

impl SearchMassModel for TupleCountMassModel {
    fn total_mass(&self) -> MassValue {
        self.total
    }

    fn covered_mass(&self) -> MassValue {
        MassValue::ZERO
    }

    fn quality(&self) -> CoverageQuality {
        CoverageQuality::Exact
    }
}

pub struct TupleSolveStage {
    problem: Problem,
    tuples: Arc<Vec<SumTuple>>,
    cfg: Arc<SearchConfig>,
    k: usize,
    verbose: bool,
}

impl TupleSolveStage {
    pub fn new(
        problem: Problem,
        tuples: Arc<Vec<SumTuple>>,
        cfg: Arc<SearchConfig>,
        k: usize,
        verbose: bool,
    ) -> Self {
        Self {
            problem,
            tuples,
            cfg,
            k,
            verbose,
        }
    }

    fn solve_one(&self, tuple_idx: usize) -> Option<SearchReport> {
        let tuple = *self.tuples.get(tuple_idx)?;
        let report = run_mdd_sat_search(self.problem, &[tuple], &self.cfg, self.verbose, self.k);
        Some(report)
    }
}

impl StageHandler<TuplePayload> for TupleSolveStage {
    fn id(&self) -> StageId {
        STAGE_TUPLE_SOLVE
    }

    fn handle(
        &self,
        item: WorkItem<TuplePayload>,
        _ctx: &crate::search_framework::stage::StageContext<'_>,
    ) -> StageOutcome<TuplePayload> {
        let mut out = StageOutcome::default();
        let found = self
            .solve_one(item.payload.tuple_idx)
            .map(|r| r.found_solution)
            .unwrap_or(false);
        out.mass_delta = MassDelta {
            covered_exact: MassValue(1.0),
            covered_partial: MassValue::ZERO,
        };
        if found {
            out.diagnostics
                .push(crate::search_framework::stage::DiagEvent {
                    code: "solution_found",
                    message: Arc::<str>::from("tuple solve found a solution"),
                });
        }
        out
    }
}

pub struct ApartTogetherAdapter {
    pub problem: Problem,
    pub tuples: Arc<Vec<SumTuple>>,
    pub cfg: Arc<SearchConfig>,
    pub k: usize,
    pub verbose: bool,
    pub mode_name: &'static str,
}

impl SearchModeAdapter<TuplePayload> for ApartTogetherAdapter {
    fn name(&self) -> &'static str {
        self.mode_name
    }

    fn init(&self) -> AdapterInit<TuplePayload> {
        let mut seed_items = Vec::with_capacity(self.tuples.len());
        for idx in 0..self.tuples.len() {
            seed_items.push(WorkItem {
                stage_id: STAGE_TUPLE_SOLVE,
                priority: 1,
                cost_hint: 1,
                replay_key: idx as u64,
                mass_hint: Some(1.0),
                meta: WorkItemMeta {
                    item_id: idx as u64,
                    parent_item_id: None,
                    fanout_root_id: idx as u64,
                    depth_from_root: 0,
                    spawn_seq: 0,
                },
                payload: TuplePayload { tuple_idx: idx },
            });
        }
        AdapterInit { seed_items }
    }

    fn stages(&self) -> BTreeMap<StageId, Box<dyn StageHandler<TuplePayload>>> {
        let mut stages: BTreeMap<StageId, Box<dyn StageHandler<TuplePayload>>> = BTreeMap::new();
        stages.insert(
            STAGE_TUPLE_SOLVE,
            Box::new(TupleSolveStage::new(
                self.problem,
                Arc::clone(&self.tuples),
                Arc::clone(&self.cfg),
                self.k,
                self.verbose,
            )),
        );
        stages
    }

    fn mass_model(&self) -> Box<dyn SearchMassModel> {
        Box::new(TupleCountMassModel::new(self.tuples.len()))
    }
}
