use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use crate::search_framework::events::{
    EdgeFlowCounters, FanoutRootCounters, ForcingRollups, ProgressSnapshot, SearchEvent,
};
use crate::search_framework::mass::{MassSnapshot, SearchMassModel, TtcQuality};
use crate::search_framework::queue::SchedulerPolicy;
use crate::search_framework::stage::{
    Continuation, StageContext, StageHandler, StageId, StageOutcome, WorkItem,
};

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
    /// How many worker threads to spawn. Defaults to `1` — adapters
    /// whose individual stage handlers are fine-grained (e.g. one SAT
    /// attempt per call) should raise this. Adapters that already
    /// parallelize internally (e.g. today's `TupleSolveStage` which
    /// calls `run_mdd_sat_search`, itself multi-threaded) should keep
    /// it at 1 to avoid oversubscription.
    pub worker_count: usize,
}

impl Default for EngineConfig {
    fn default() -> Self {
        Self {
            progress_interval: Duration::from_secs(1),
            worker_count: 1,
        }
    }
}

/// The single coordinator thread owns scheduler, registries, and
/// mass accounting. `N` worker threads self-fetch `WorkItem`s from
/// the shared scheduler (guarded by a `Mutex` + `Condvar`), call
/// `stage.handle`, and send the resulting `WorkerReport` back to the
/// coordinator over an `mpsc::channel`. The coordinator applies
/// mass, forcings, and fan-out side effects, then pushes any
/// `emitted` children or `continuation` items back into the
/// scheduler for workers to pick up.
///
/// Shutdown: when `in_flight == 0` *and* the scheduler is empty, the
/// coordinator sets `shutdown` and wakes all workers; workers see
/// the flag inside their wait loop and exit cleanly. `thread::scope`
/// then joins everything.
pub struct SearchEngine<T> {
    cfg: EngineConfig,
    scheduler: Option<Box<dyn SchedulerPolicy<T>>>,
    cancelled: Arc<AtomicBool>,
}

struct WorkerReport<T> {
    from_stage: StageId,
    outcome: StageOutcome<T>,
}

impl<T: Send + 'static> SearchEngine<T> {
    pub fn new(cfg: EngineConfig, scheduler: Box<dyn SchedulerPolicy<T>>) -> Self {
        Self {
            cfg,
            scheduler: Some(scheduler),
            cancelled: Arc::new(AtomicBool::new(false)),
        }
    }

    pub fn cancel(&self) {
        self.cancelled.store(true, Ordering::Relaxed);
    }

    /// Hand out a clone of the internal cancel flag. Lets external
    /// threads (e.g. the solution drain) stop the search without
    /// holding a `&SearchEngine` reference (which is borrowed by the
    /// main thread running `run()`).
    pub fn cancel_flag(&self) -> Arc<AtomicBool> {
        Arc::clone(&self.cancelled)
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
        // Hold the mass model across the run so progress ticks can
        // publish the adapter's current `quality()` rather than a
        // hardcoded placeholder, and so the coordinator can poll
        // `covered_mass()` each tick to surface pull-based
        // coverage (e.g. sync's projected fraction).
        let mass_model: Arc<dyn SearchMassModel> = Arc::from(adapter.mass_model());
        let mut mass = MassSnapshot::new(mass_model.total_mass());

        let stages_map: BTreeMap<StageId, Arc<dyn StageHandler<T>>> = adapter
            .stages()
            .into_iter()
            .map(|(k, v)| (k, Arc::<dyn StageHandler<T>>::from(v)))
            .collect();
        let stages = Arc::new(stages_map);
        let adapter_name: &'static str = adapter.name();

        // Move scheduler into shared-ownership cell so workers can pop
        // and the coordinator can push concurrently.
        let scheduler_box = self
            .scheduler
            .take()
            .expect("SearchEngine::run called twice on the same engine");
        let scheduler = Arc::new((Mutex::new(scheduler_box), Condvar::new()));

        // Seed
        {
            let (lock, _) = &*scheduler;
            let mut guard = lock.lock().unwrap();
            for seed in adapter.init().seed_items {
                guard.push(seed);
            }
        }

        let in_flight = Arc::new(AtomicUsize::new(0));
        let shutdown = Arc::new(AtomicBool::new(false));
        let worker_count = self.cfg.worker_count.max(1);
        let (event_tx, event_rx) = mpsc::channel::<WorkerReport<T>>();

        thread::scope(|scope| {
            // Workers
            for _ in 0..worker_count {
                let scheduler = Arc::clone(&scheduler);
                let stages = Arc::clone(&stages);
                let in_flight = Arc::clone(&in_flight);
                let shutdown = Arc::clone(&shutdown);
                let cancelled = Arc::clone(&self.cancelled);
                let event_tx = event_tx.clone();
                let start_clone = start;
                scope.spawn(move || {
                    loop {
                        let next: Option<WorkItem<T>> = {
                            let (lock, cvar) = &*scheduler;
                            let mut guard = lock.lock().unwrap();
                            loop {
                                if shutdown.load(Ordering::Acquire) {
                                    break None;
                                }
                                if let Some(item) = guard.pop() {
                                    // Increment while still holding the lock
                                    // so the coordinator's "is the queue
                                    // quiescent" check never sees
                                    // (scheduler_empty && in_flight==0) while
                                    // this item is in limbo.
                                    in_flight.fetch_add(1, Ordering::AcqRel);
                                    break Some(item);
                                }
                                guard = cvar.wait(guard).unwrap();
                            }
                        };
                        let Some(item) = next else { return; };
                        let stage_id: StageId = item.stage_id;
                        let Some(handler) = stages.get(stage_id) else {
                            // Unknown stage — credit nothing, move on.
                            in_flight.fetch_sub(1, Ordering::AcqRel);
                            continue;
                        };
                        let ctx = StageContext {
                            cancelled: cancelled.load(Ordering::Relaxed),
                            now_millis: start_clone.elapsed().as_millis(),
                            adapter_name,
                        };
                        let outcome = handler.handle(item, &ctx);
                        if event_tx
                            .send(WorkerReport {
                                from_stage: stage_id,
                                outcome,
                            })
                            .is_err()
                        {
                            return;
                        }
                    }
                });
            }
            // Drop coordinator's copy so `event_rx` terminates once
            // every worker has exited.
            drop(event_tx);

            // Coordinator loop
            loop {
                if self.cancelled.load(Ordering::Relaxed) {
                    break;
                }
                if is_quiescent(&scheduler, &in_flight) {
                    break;
                }

                let wait = self
                    .cfg
                    .progress_interval
                    .saturating_sub(last_progress.elapsed());
                match event_rx.recv_timeout(wait.max(Duration::from_millis(1))) {
                    Ok(report) => {
                        apply_report(
                            report,
                            &scheduler,
                            &mut mass,
                            &mut forcings,
                            &mut edge_flow,
                            &mut fanout_roots,
                        );
                        in_flight.fetch_sub(1, Ordering::AcqRel);
                    }
                    Err(RecvTimeoutError::Timeout) => { /* progress tick below */ }
                    Err(RecvTimeoutError::Disconnected) => break,
                }

                if last_progress.elapsed() >= self.cfg.progress_interval {
                    last_progress = Instant::now();
                    // Pull any live-polled coverage from the mass
                    // model. Adapters with a running counter (e.g.
                    // `tuples_done`) surface progress here even when
                    // they don't push `MassDelta` per handler. Takes
                    // the max so push-based deltas aren't clobbered.
                    let polled = mass_model.covered_mass();
                    if polled.0 > mass.covered_exact.0 {
                        mass.covered_exact = polled;
                    }
                    on_event(SearchEvent::Progress(build_snapshot(
                        start.elapsed(),
                        &mass,
                        mass_model.quality(),
                        &edge_flow,
                        &fanout_roots,
                        &forcings,
                    )));
                }
            }

            // Release workers so they can exit their wait loops.
            shutdown.store(true, Ordering::Release);
            {
                let (_, cvar) = &*scheduler;
                cvar.notify_all();
            }

            // Drain any remaining events workers send while exiting.
            while let Ok(report) = event_rx.recv() {
                apply_report(
                    report,
                    &scheduler,
                    &mut mass,
                    &mut forcings,
                    &mut edge_flow,
                    &mut fanout_roots,
                );
                in_flight.fetch_sub(1, Ordering::AcqRel);
            }
        });

        // Final poll for any live-counted coverage the last tick
        // missed — same policy as the in-loop tick.
        let polled = mass_model.covered_mass();
        if polled.0 > mass.covered_exact.0 {
            mass.covered_exact = polled;
        }
        on_event(SearchEvent::Finished(build_snapshot(
            start.elapsed(),
            &mass,
            mass_model.quality(),
            &edge_flow,
            &fanout_roots,
            &forcings,
        )));
    }
}

type SharedScheduler<T> = Arc<(Mutex<Box<dyn SchedulerPolicy<T>>>, Condvar)>;

fn is_quiescent<T>(scheduler: &SharedScheduler<T>, in_flight: &AtomicUsize) -> bool {
    if in_flight.load(Ordering::Acquire) > 0 {
        return false;
    }
    let (lock, _) = &**scheduler;
    let guard = lock.lock().unwrap();
    guard.is_empty() && in_flight.load(Ordering::Acquire) == 0
}

fn apply_report<T>(
    report: WorkerReport<T>,
    scheduler: &SharedScheduler<T>,
    mass: &mut MassSnapshot,
    forcings: &mut ForcingRollups,
    edge_flow: &mut BTreeMap<(String, String), EdgeFlowCounters>,
    fanout_roots: &mut BTreeMap<u64, FanoutRootCounters>,
) {
    let from_stage = report.from_stage;
    let outcome = report.outcome;
    mass.apply_delta(outcome.mass_delta);
    forcings.apply(from_stage, &outcome.forcings);

    let emitted_len = outcome.emitted.len() as u64;
    if let Some(first) = outcome.emitted.first() {
        fanout_roots
            .entry(first.meta.fanout_root_id)
            .or_default()
            .live_descendants += emitted_len;
    }

    let mut notify = false;
    {
        let (lock, _) = &**scheduler;
        let mut guard = lock.lock().unwrap();
        for child in outcome.emitted {
            let to_stage = child.stage_id;
            edge_flow
                .entry((from_stage.to_string(), to_stage.to_string()))
                .or_default()
                .spawned += 1;
            guard.push(child);
            notify = true;
        }
        match outcome.continuation {
            Continuation::None => {}
            Continuation::Split(items) => {
                for child in items {
                    let to_stage = child.stage_id;
                    edge_flow
                        .entry((from_stage.to_string(), to_stage.to_string()))
                        .or_default()
                        .spawned += 1;
                    guard.push(child);
                    notify = true;
                }
            }
            Continuation::Resume(child) => {
                guard.push(child);
                notify = true;
            }
        }
    }
    if notify {
        let (_, cvar) = &**scheduler;
        cvar.notify_one();
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::search_framework::mass::{CoverageQuality, MassDelta, MassValue};
    use crate::search_framework::queue::GoldThenWork;
    use crate::search_framework::stage::{
        Continuation, ForcingDelta, StageOutcome, WorkItemMeta,
    };
    use std::sync::atomic::AtomicU64;

    #[derive(Default)]
    struct CounterAdapter {
        seeds: usize,
        counter: Arc<AtomicU64>,
    }

    struct CounterStage {
        counter: Arc<AtomicU64>,
    }

    impl StageHandler<u64> for CounterStage {
        fn id(&self) -> StageId {
            "counter"
        }
        fn handle(
            &self,
            item: WorkItem<u64>,
            _ctx: &StageContext<'_>,
        ) -> StageOutcome<u64> {
            self.counter.fetch_add(1, Ordering::Relaxed);
            let mut out = StageOutcome::default();
            out.mass_delta = MassDelta {
                covered_exact: MassValue(1.0),
                covered_partial: MassValue::ZERO,
            };
            // Emit a small cascade to exercise fan-out + forcings.
            if item.payload < 2 {
                out.emitted.push(WorkItem {
                    stage_id: "counter",
                    priority: 0,
                    cost_hint: 1,
                    replay_key: item.payload * 10 + 1,
                    mass_hint: Some(1.0),
                    meta: WorkItemMeta {
                        item_id: item.payload * 10 + 1,
                        parent_item_id: Some(item.meta.item_id),
                        fanout_root_id: item.meta.fanout_root_id,
                        depth_from_root: item.meta.depth_from_root + 1,
                        spawn_seq: 0,
                    },
                    payload: item.payload + 1,
                });
            }
            out.forcings = ForcingDelta {
                by_level_feature: vec![(0, 0, 3), (1, 2, 5)],
            };
            out
        }
    }

    struct CounterMass {
        total: MassValue,
    }
    impl SearchMassModel for CounterMass {
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

    impl SearchModeAdapter<u64> for CounterAdapter {
        fn name(&self) -> &'static str {
            "counter"
        }
        fn init(&self) -> AdapterInit<u64> {
            let seed_items = (0..self.seeds as u64)
                .map(|i| WorkItem {
                    stage_id: "counter",
                    priority: 0,
                    cost_hint: 1,
                    replay_key: i,
                    mass_hint: Some(1.0),
                    meta: WorkItemMeta {
                        item_id: i,
                        parent_item_id: None,
                        fanout_root_id: i,
                        depth_from_root: 0,
                        spawn_seq: 0,
                    },
                    payload: 0,
                })
                .collect();
            AdapterInit { seed_items }
        }
        fn stages(&self) -> BTreeMap<StageId, Box<dyn StageHandler<u64>>> {
            let mut m: BTreeMap<StageId, Box<dyn StageHandler<u64>>> = BTreeMap::new();
            m.insert(
                "counter",
                Box::new(CounterStage {
                    counter: Arc::clone(&self.counter),
                }),
            );
            m
        }
        fn mass_model(&self) -> Box<dyn SearchMassModel> {
            Box::new(CounterMass {
                total: MassValue(self.seeds as f64 * 3.0),
            })
        }
    }

    fn run_with_workers(seeds: usize, worker_count: usize) -> (u64, ForcingRollups) {
        let counter = Arc::new(AtomicU64::new(0));
        let adapter = CounterAdapter {
            seeds,
            counter: Arc::clone(&counter),
        };
        let cfg = EngineConfig {
            progress_interval: Duration::from_millis(50),
            worker_count,
        };
        let mut engine = SearchEngine::<u64>::new(cfg, Box::new(GoldThenWork::new(4)));

        let mut final_forcings: Option<ForcingRollups> = None;
        engine.run(&adapter, |event| {
            if let SearchEvent::Finished(p) = event {
                final_forcings = Some(p.forcings);
            }
        });
        (
            counter.load(Ordering::Relaxed),
            final_forcings.expect("Finished event was not emitted"),
        )
    }

    #[test]
    fn coordinator_drains_and_exits_single_worker() {
        // Each seed fires 3 handle() calls (payload=0, 1, 2) via
        // Continuation-less cascading emit.
        let (count, _) = run_with_workers(4, 1);
        assert_eq!(count, 4 * 3);
    }

    #[test]
    fn coordinator_drains_and_exits_multiple_workers() {
        let (count, _) = run_with_workers(8, 4);
        assert_eq!(count, 8 * 3);
    }

    #[test]
    fn forcings_rollups_accumulate_over_run() {
        let (_, forcings) = run_with_workers(2, 2);
        // Each handle() contributes (level=0, kind=0, count=3) and
        // (level=1, kind=2, count=5). Seeds=2, cascade depth 3 each:
        // 6 total handle() calls.
        let total: u64 = forcings.stage_level.values().sum();
        assert_eq!(total, 6 * (3 + 5));
        let lvl0_clause = forcings
            .stage_level
            .get(&("counter", 0))
            .copied()
            .unwrap_or(0);
        assert_eq!(lvl0_clause, 6 * 3);
        let feat_clause = forcings
            .stage_feature
            .get(&("counter", 0))
            .copied()
            .unwrap_or(0);
        assert_eq!(feat_clause, 6 * 3);
    }
}
