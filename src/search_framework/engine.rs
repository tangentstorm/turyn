use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use crate::search_framework::events::{
    EdgeFlowCounters, FanoutRootCounters, ForcingRollups, ProgressSnapshot, SearchEvent,
};
use crate::search_framework::mass::{MassSnapshot, MassValue, SearchMassModel, TtcQuality};
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
    /// The `fanout_root_id` of the item that produced this report.
    /// Carried so `apply_report` can decrement
    /// `FanoutRootCounters.live_descendants` when the item
    /// finishes (subtree-size tracking; issue flagged in review).
    fanout_root_id: u64,
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
        on_event: impl FnMut(SearchEvent),
    ) {
        self.run_since(Instant::now(), adapter, on_event)
    }

    /// Variant of [`run`] that takes a caller-provided `start` so
    /// `ProgressSnapshot::elapsed` covers pre-engine setup work
    /// (MDD load, seed-boundary enumeration, scheduler fill) the
    /// caller already did before handing control over. Without
    /// this override the Finished summary reported `elapsed=0.3s`
    /// after the user actually spent ~1s — `--sat-secs` fires in
    /// the setup phase and the coordinator loop barely runs.
    pub fn run_since(
        &mut self,
        start: Instant,
        adapter: &dyn SearchModeAdapter<T>,
        mut on_event: impl FnMut(SearchEvent),
    ) {
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

        // Seed. Poll the engine's cancel flag every 64k pushes so
        // the `--sat-secs` watchdog can short-circuit construction
        // on adapters with very large seed sets (e.g. 18M boundaries
        // at apart/together n=26 k=8). Without this check, pushing
        // 18M items into a `BinaryHeap` dominates the wall-clock
        // budget even when the adapter's `init()` already bailed.
        const SEED_CANCEL_POLL_STRIDE: usize = 1 << 16;
        {
            let (lock, _) = &*scheduler;
            let mut guard = lock.lock().unwrap();
            for (i, seed) in adapter.init().seed_items.into_iter().enumerate() {
                if i & (SEED_CANCEL_POLL_STRIDE - 1) == 0
                    && self.cancelled.load(Ordering::Relaxed)
                {
                    break;
                }
                // Seed items each start one in-flight descendant
                // for their fanout_root. `apply_report` decrements
                // as items complete and increments by emitted
                // children, so `live_descendants` tracks the real
                // mid-flight subtree size.
                fanout_roots
                    .entry(seed.meta.fanout_root_id)
                    .or_default()
                    .live_descendants += 1;
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
                        // `ctx.cancelled` is now a live `&AtomicBool`
                        // reference into the engine's flag so handlers
                        // running long internal loops (cross's
                        // brute-force XY walk, sync's DFS) can poll it
                        // without relying on a dispatch-time snapshot.
                        let fanout_root_id = item.meta.fanout_root_id;
                        let ctx = StageContext {
                            cancelled: &cancelled,
                            now_millis: start_clone.elapsed().as_millis(),
                            adapter_name,
                        };
                        let outcome = handler.handle(item, &ctx);
                        if event_tx
                            .send(WorkerReport {
                                from_stage: stage_id,
                                fanout_root_id,
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
                    // Pull both live-polled coverage streams from
                    // the mass model. Adapters with a running
                    // counter surface progress here even when they
                    // don't push `MassDelta` per handler; takes the
                    // max so push-based deltas aren't clobbered.
                    let polled = mass_model.covered_mass();
                    if polled.0 > mass.covered_exact.0 {
                        mass.covered_exact = polled;
                    }
                    let polled_partial = mass_model.covered_partial_mass();
                    if polled_partial.0 > mass.covered_partial.0 {
                        // Clamp under residual so we don't exceed
                        // the total — matches `apply_delta`.
                        let cap =
                            (mass.total.0 - mass.covered_exact.0).max(0.0);
                        mass.covered_partial = MassValue(polled_partial.0.min(cap));
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
        let polled_partial = mass_model.covered_partial_mass();
        if polled_partial.0 > mass.covered_partial.0 {
            let cap = (mass.total.0 - mass.covered_exact.0).max(0.0);
            mass.covered_partial = MassValue(polled_partial.0.min(cap));
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
    let fanout_root_id = report.fanout_root_id;
    let outcome = report.outcome;
    mass.apply_delta(outcome.mass_delta);
    forcings.apply(from_stage, &outcome.forcings);

    // `live_descendants` is a true *in-flight* subtree count: every
    // continuation path that creates a new scheduler-visible work
    // item adds 1; the item we just finished subtracts 1. Per
    // docs/TELEMETRY.md §3 the counter MUST include split children
    // and — under this engine's chosen Resume model — resumed work
    // as well (see the Resume arm below).
    let split_count = match &outcome.continuation {
        Continuation::None => 0u64,
        Continuation::Split(items) => items.len() as u64,
        // Resume re-enters the scheduler as a live logical item, so
        // it keeps the boundary alive exactly like a split child.
        Continuation::Resume(_) => 1,
    };
    let new_live = outcome.emitted.len() as u64 + split_count;
    {
        let entry = fanout_roots.entry(fanout_root_id).or_default();
        entry.live_descendants = entry
            .live_descendants
            .saturating_add(new_live)
            .saturating_sub(1);
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
                // Per docs/TELEMETRY.md §2, each split child is a
                // logical work transition and MUST contribute one
                // `spawned` count on its own edge.
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
                // This engine adopts the "explicit self-edge"
                // Resume model from docs/TELEMETRY.md §2.
                // Resuming the same logical subproblem counts as
                // one logical work transition on the
                // `(from_stage, same_stage)` edge, so resume
                // volume is observable in `edge_flow` and matches
                // the `live_descendants` accounting above.
                let to_stage = child.stage_id;
                edge_flow
                    .entry((from_stage.to_string(), to_stage.to_string()))
                    .or_default()
                    .spawned += 1;
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
    use crate::search_framework::mass::{CoverageQuality, MassDelta};
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

    /// Stage that uses `Continuation::Split` once then stops.
    /// Each handled item with `payload < depth` splits into two
    /// children (same stage, same fanout_root) via Continuation; no
    /// `emitted` entries. Lets us verify split-child accounting in
    /// isolation from the `emitted` path.
    struct SplitStage {
        depth: u64,
        counter: Arc<AtomicU64>,
    }
    impl StageHandler<u64> for SplitStage {
        fn id(&self) -> StageId { "split" }
        fn handle(&self, item: WorkItem<u64>, _ctx: &StageContext<'_>) -> StageOutcome<u64> {
            self.counter.fetch_add(1, Ordering::Relaxed);
            let mut out = StageOutcome::default();
            if item.payload < self.depth {
                let mk_child = |bump: u64| WorkItem {
                    stage_id: "split",
                    priority: 0,
                    cost_hint: 1,
                    replay_key: 0,
                    mass_hint: None,
                    meta: WorkItemMeta {
                        item_id: item.meta.item_id * 10 + bump,
                        parent_item_id: Some(item.meta.item_id),
                        fanout_root_id: item.meta.fanout_root_id,
                        depth_from_root: item.meta.depth_from_root + 1,
                        spawn_seq: bump as u32,
                    },
                    payload: item.payload + 1,
                };
                out.continuation = Continuation::Split(vec![mk_child(1), mk_child(2)]);
            }
            out
        }
    }

    struct SplitAdapter { counter: Arc<AtomicU64>, depth: u64 }
    impl SearchModeAdapter<u64> for SplitAdapter {
        fn name(&self) -> &'static str { "split" }
        fn init(&self) -> AdapterInit<u64> {
            AdapterInit {
                seed_items: vec![WorkItem {
                    stage_id: "split",
                    priority: 0,
                    cost_hint: 1,
                    replay_key: 0,
                    mass_hint: None,
                    meta: WorkItemMeta {
                        item_id: 1,
                        parent_item_id: None,
                        fanout_root_id: 42,
                        depth_from_root: 0,
                        spawn_seq: 0,
                    },
                    payload: 0,
                }],
            }
        }
        fn stages(&self) -> BTreeMap<StageId, Box<dyn StageHandler<u64>>> {
            let mut m: BTreeMap<StageId, Box<dyn StageHandler<u64>>> = BTreeMap::new();
            m.insert("split", Box::new(SplitStage {
                depth: self.depth,
                counter: Arc::clone(&self.counter),
            }));
            m
        }
        fn mass_model(&self) -> Box<dyn SearchMassModel> {
            Box::new(CounterMass { total: MassValue::ONE })
        }
    }

    /// Stage that resumes its own item `resumes` times, then stops.
    /// Uses `Continuation::Resume` so we can verify Resume
    /// bookkeeping independently of `emitted` and `Split`.
    struct ResumeStage {
        resumes: u64,
        counter: Arc<AtomicU64>,
    }
    impl StageHandler<u64> for ResumeStage {
        fn id(&self) -> StageId { "resume" }
        fn handle(&self, item: WorkItem<u64>, _ctx: &StageContext<'_>) -> StageOutcome<u64> {
            self.counter.fetch_add(1, Ordering::Relaxed);
            let mut out = StageOutcome::default();
            if item.payload < self.resumes {
                out.continuation = Continuation::Resume(WorkItem {
                    stage_id: "resume",
                    priority: 0,
                    cost_hint: 1,
                    replay_key: 0,
                    mass_hint: None,
                    meta: WorkItemMeta {
                        item_id: item.meta.item_id,
                        parent_item_id: item.meta.parent_item_id,
                        fanout_root_id: item.meta.fanout_root_id,
                        depth_from_root: item.meta.depth_from_root,
                        spawn_seq: item.meta.spawn_seq.saturating_add(1),
                    },
                    payload: item.payload + 1,
                });
            }
            out
        }
    }

    struct ResumeAdapter { counter: Arc<AtomicU64>, resumes: u64 }
    impl SearchModeAdapter<u64> for ResumeAdapter {
        fn name(&self) -> &'static str { "resume" }
        fn init(&self) -> AdapterInit<u64> {
            AdapterInit {
                seed_items: vec![WorkItem {
                    stage_id: "resume",
                    priority: 0,
                    cost_hint: 1,
                    replay_key: 0,
                    mass_hint: None,
                    meta: WorkItemMeta {
                        item_id: 1,
                        parent_item_id: None,
                        fanout_root_id: 7,
                        depth_from_root: 0,
                        spawn_seq: 0,
                    },
                    payload: 0,
                }],
            }
        }
        fn stages(&self) -> BTreeMap<StageId, Box<dyn StageHandler<u64>>> {
            let mut m: BTreeMap<StageId, Box<dyn StageHandler<u64>>> = BTreeMap::new();
            m.insert("resume", Box::new(ResumeStage {
                resumes: self.resumes,
                counter: Arc::clone(&self.counter),
            }));
            m
        }
        fn mass_model(&self) -> Box<dyn SearchMassModel> {
            Box::new(CounterMass { total: MassValue::ONE })
        }
    }

    fn final_snapshot<T: Send + 'static>(
        adapter: &dyn SearchModeAdapter<T>,
    ) -> ProgressSnapshot {
        let cfg = EngineConfig {
            progress_interval: Duration::from_millis(50),
            worker_count: 1,
        };
        let mut engine = SearchEngine::<T>::new(cfg, Box::new(GoldThenWork::new(4)));
        let mut final_snap: Option<ProgressSnapshot> = None;
        engine.run(adapter, |event| {
            if let SearchEvent::Finished(p) = event {
                final_snap = Some(p);
            }
        });
        final_snap.expect("Finished event was not emitted")
    }

    #[test]
    fn split_children_count_on_edge_flow_and_live_descendants() {
        // One seed, depth 2 ⇒ tree: seed(1) splits into 2 children,
        // each splits into 2 leaves. Handles: 1 + 2 + 4 = 7.
        // Every split child edge is a logical work transition
        // between `split -> split` per docs/TELEMETRY.md §2; the
        // seed subtree fully drains so `live_descendants` ends at 0.
        let counter = Arc::new(AtomicU64::new(0));
        let adapter = SplitAdapter { counter: Arc::clone(&counter), depth: 2 };
        let p = final_snapshot::<u64>(&adapter);
        assert_eq!(counter.load(Ordering::Relaxed), 7);
        // 3 split parents × 2 children each = 6 spawned edges.
        let spawned = p
            .edge_flow
            .get(&("split".to_string(), "split".to_string()))
            .map(|c| c.spawned)
            .unwrap_or(0);
        assert_eq!(spawned, 6, "Continuation::Split children MUST contribute to edge_flow.spawned");
        let live = p.fanout_roots.get(&42).map(|c| c.live_descendants).unwrap_or(0);
        assert_eq!(live, 0, "subtree fully drained — live_descendants must decay to 0");
    }

    #[test]
    fn resume_as_self_edge_counts_each_resumption() {
        // Engine's declared Resume model (docs/TELEMETRY.md §2
        // option 1): Resume IS an explicit self-edge in edge_flow
        // and IS a live descendant while it sits in the queue.
        // One seed, 3 resumes ⇒ 4 handle() calls, 3 resume edges
        // on (resume -> resume).
        let counter = Arc::new(AtomicU64::new(0));
        let adapter = ResumeAdapter { counter: Arc::clone(&counter), resumes: 3 };
        let p = final_snapshot::<u64>(&adapter);
        assert_eq!(counter.load(Ordering::Relaxed), 4);
        let spawned = p
            .edge_flow
            .get(&("resume".to_string(), "resume".to_string()))
            .map(|c| c.spawned)
            .unwrap_or(0);
        assert_eq!(spawned, 3, "Continuation::Resume MUST count as one self-edge per resumption under the engine's declared model");
        let live = p.fanout_roots.get(&7).map(|c| c.live_descendants).unwrap_or(0);
        assert_eq!(live, 0, "resume chain must terminate at zero live descendants");
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
