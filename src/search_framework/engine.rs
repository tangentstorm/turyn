use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

use crate::search_framework::events::{
    EdgeFlowCounters, FanoutRootCounters, ForcingRollups, ProgressSnapshot, SearchEvent,
};
use crate::search_framework::mass::{MassSnapshot, SearchMassModel, TtcQuality};
use crate::search_framework::queue::SchedulerPolicy;
use crate::search_framework::stage::{Continuation, StageContext, StageHandler, StageId, WorkItem};

pub struct AdapterInit<T> {
    pub seed_items: Vec<WorkItem<T>>,
}

pub trait SearchModeAdapter<T>: Send + Sync {
    fn name(&self) -> &'static str;
    fn init(&self) -> AdapterInit<T>;
    fn stages(&self) -> BTreeMap<StageId, Box<dyn StageHandler<T>>>;
    fn mass_model(&self) -> Box<dyn SearchMassModel>;
}

pub struct EngineConfig {
    pub progress_interval: Duration,
    pub worker_count: usize,
}

impl Default for EngineConfig {
    fn default() -> Self {
        Self {
            progress_interval: Duration::from_secs(1),
            worker_count: std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(1),
        }
    }
}

pub struct SearchEngine<T> {
    cfg: EngineConfig,
    scheduler: Box<dyn SchedulerPolicy<T>>,
    cancelled: AtomicBool,
}

impl<T: Send + 'static> SearchEngine<T> {
    pub fn new(cfg: EngineConfig, scheduler: Box<dyn SchedulerPolicy<T>>) -> Self {
        Self {
            cfg,
            scheduler,
            cancelled: AtomicBool::new(false),
        }
    }

    pub fn cancel(&self) {
        self.cancelled.store(true, Ordering::Relaxed);
    }

    pub fn run(
        &mut self,
        adapter: &dyn SearchModeAdapter<T>,
        mut on_event: impl FnMut(SearchEvent),
    ) {
        let start = Instant::now();
        let mut last_progress = start;
        let mut edge_flow: BTreeMap<(String, String), EdgeFlowCounters> = BTreeMap::new();
        let mut fanout_roots: BTreeMap<u64, FanoutRootCounters> = BTreeMap::new();
        let mut forcings = ForcingRollups::default();

        let mut mass = MassSnapshot::new(adapter.mass_model().total_mass());
        let stages = adapter.stages();
        let init = adapter.init();

        for seed in init.seed_items {
            self.scheduler.push(seed);
        }

        while !self.cancelled.load(Ordering::Relaxed) && !self.scheduler.is_empty() {
            if let Some(item) = self.scheduler.pop() {
                let stage = match stages.get(item.stage_id) {
                    Some(stage) => stage,
                    None => continue,
                };
                let ctx = StageContext {
                    cancelled: self.cancelled.load(Ordering::Relaxed),
                    now_millis: start.elapsed().as_millis(),
                    adapter_name: adapter.name(),
                };
                let from_stage: StageId = item.stage_id;
                let outcome = stage.handle(item, &ctx);
                mass.apply_delta(outcome.mass_delta);
                forcings.apply(from_stage, &outcome.forcings);

                let emitted_len = outcome.emitted.len() as u64;
                fanout_roots
                    .entry(
                        outcome
                            .emitted
                            .first()
                            .map(|w| w.meta.fanout_root_id)
                            .unwrap_or_default(),
                    )
                    .or_default()
                    .live_descendants += emitted_len;

                for child in outcome.emitted {
                    let to_stage = child.stage_id;
                    edge_flow
                        .entry((from_stage.to_string(), to_stage.to_string()))
                        .or_default()
                        .spawned += 1;
                    self.scheduler.push(child);
                }

                // Deferral: push continuation work back for later pickup.
                // Under the universal contract, `mass_delta` above has
                // already credited the portion of the sub-cube this call
                // actually covered; the continuation represents *only*
                // the residual that still needs to be searched.
                match outcome.continuation {
                    Continuation::None => {}
                    Continuation::Split(items) => {
                        for child in items {
                            let to_stage = child.stage_id;
                            edge_flow
                                .entry((from_stage.to_string(), to_stage.to_string()))
                                .or_default()
                                .spawned += 1;
                            self.scheduler.push(child);
                        }
                    }
                    Continuation::Resume(child) => {
                        self.scheduler.push(child);
                    }
                }

                if last_progress.elapsed() >= self.cfg.progress_interval {
                    last_progress = Instant::now();
                    on_event(SearchEvent::Progress(build_snapshot(
                        start.elapsed(),
                        &mass,
                        TtcQuality::Hybrid,
                        &edge_flow,
                        &fanout_roots,
                        &forcings,
                    )));
                }
            }
        }

        on_event(SearchEvent::Finished(build_snapshot(
            start.elapsed(),
            &mass,
            adapter.mass_model().quality(),
            &edge_flow,
            &fanout_roots,
            &forcings,
        )));
    }
}

fn build_snapshot(
    elapsed: Duration,
    mass: &MassSnapshot,
    quality: TtcQuality,
    edge_flow: &BTreeMap<(String, String), EdgeFlowCounters>,
    fanout_roots: &BTreeMap<u64, FanoutRootCounters>,
    forcings: &ForcingRollups,
) -> ProgressSnapshot {
    ProgressSnapshot {
        elapsed,
        throughput_per_sec: mass.throughput_per_sec(elapsed),
        covered_mass: mass.covered(),
        total_mass: mass.total,
        remaining_mass: mass.remaining(),
        ttc: mass.ttc(elapsed),
        quality,
        edge_flow: edge_flow.clone(),
        fanout_roots: fanout_roots.clone(),
        forcings: forcings.clone(),
    }
}
