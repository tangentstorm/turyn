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
                    poll_mass(&*mass_model, &mut mass);
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
        poll_mass(&*mass_model, &mut mass);
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

/// Merge the latest polled coverage from `model` into `mass`, preserving
/// the TTC-spec invariants:
///
/// - `covered_exact` and `covered_partial` are both **monotone
///   non-decreasing** (TTC §3 invariant 6). The polled value only
///   displaces the stored value when strictly greater.
/// - `covered_exact + covered_partial ≤ total` (TTC §3 invariants 2/4).
///   When `covered_exact` grows through polling, `covered_partial` is
///   re-clamped against the new residual. Without this re-clamp,
///   `covered_partial`'s high-water mark could ride above the residual
///   (possible when an adapter like Cross zeros its in-flight
///   `cov_micro` after a tuple completes while `covered_exact` bumps up
///   in the same tick — sum could exceed 1.0).
fn poll_mass(model: &dyn SearchMassModel, mass: &mut MassSnapshot) {
    let polled = model.covered_mass();
    if polled.0 > mass.covered_exact.0 {
        mass.covered_exact = polled;
    }
    let polled_partial = model.covered_partial_mass();
    if polled_partial.0 > mass.covered_partial.0 {
        mass.covered_partial = polled_partial;
    }
    let cap = (mass.total.0 - mass.covered_exact.0).max(0.0);
    if mass.covered_partial.0 > cap {
        mass.covered_partial = MassValue(cap);
    }
}

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
        // TELEMETRY.md §3 invariant: `live_descendants` MUST
        // decrement when an in-flight item completes — which is
        // exactly what this call models. If the entry was 0 going
        // in, either seeding failed to register this root or a
        // handler emitted a child with a stale / unknown
        // `fanout_root_id`. The spec says the counter must never
        // go negative; u64 saturating_sub enforces that
        // structurally, but a pre-decrement count of 0 signals a
        // real bookkeeping bug. Catch it in debug/test builds
        // instead of silently absorbing the decrement.
        debug_assert!(
            entry.live_descendants >= 1,
            "TELEMETRY §3: apply_report on fanout_root_id={} found live_descendants=0 before decrement; \
             seeding did not register this root or a handler produced a stale root_id",
            fanout_root_id,
        );
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
    let covered = mass.covered();
    let remaining = mass.remaining();
    // TELEMETRY.md §7 SHOULD checks, enforced as debug asserts so
    // any regression breaks tests and debug builds immediately
    // without burdening release runs. Each invariant:
    //   1. covered_mass <= 1.0 (also TTC §3 invariant 4)
    //   2. remaining_mass >= 0 (TTC §3 invariant 5)
    //   3. live_descendants never negative (u64 saturating, but
    //      we still require it to stay inside representable range
    //      across every fan-out root)
    //   4. forcing axis totals agree when both are populated
    //      (TELEMETRY.md §4 consistency rule)
    debug_assert!(
        covered.0 <= mass.total.0 + 1e-9,
        "TELEMETRY §7.1: covered_mass={} MUST be <= total_mass={}",
        covered.0, mass.total.0,
    );
    debug_assert!(
        remaining.0 + 1e-9 >= 0.0,
        "TELEMETRY §7.2: remaining_mass={} MUST be >= 0",
        remaining.0,
    );
    // `live_descendants` is u64, so non-negativity is structural
    // (TELEMETRY.md §3 "never go negative"). The real bookkeeping
    // bugs we care about are caught by the pre-decrement guard
    // inside `apply_report`; here we only sanity-check that no
    // entry has saturated at the upper bound, which would be a
    // runaway `saturating_add` producing a telemetry value that
    // can no longer shrink back.
    debug_assert!(
        fanout_roots.values().all(|c| c.live_descendants < u64::MAX / 2),
        "TELEMETRY §3: fanout_roots.live_descendants has saturated near u64::MAX ({} entries > half-range); \
         a handler is emitting children without corresponding completions",
        fanout_roots.values().filter(|c| c.live_descendants >= u64::MAX / 2).count(),
    );
    let sum_level: u64 = forcings.stage_level.values().sum();
    let sum_feature: u64 = forcings.stage_feature.values().sum();
    if !forcings.stage_level.is_empty() && !forcings.stage_feature.is_empty() {
        debug_assert_eq!(
            sum_level, sum_feature,
            "TELEMETRY §4 consistency rule: stage_level and stage_feature totals MUST agree when both populated",
        );
    }
    ProgressSnapshot {
        elapsed,
        throughput_per_sec: mass.throughput_per_sec(elapsed),
        covered_mass: covered,
        total_mass: mass.total,
        remaining_mass: remaining,
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

    /// Test-only mass model. Obeys the TTC §1 contract
    /// (`total_mass == 1.0`) so the engine's internal
    /// `MassSnapshot.total` stays consistent with the public
    /// universal schema.
    struct CounterMass {
        total: MassValue,
    }
    impl SearchMassModel for CounterMass {
        fn covered_mass(&self) -> MassValue {
            MassValue::ZERO
        }
        fn quality(&self) -> CoverageQuality {
            CoverageQuality::Exact
        }
    }
    impl CounterMass {
        #[allow(dead_code)]
        fn for_seeds(_seeds: usize) -> Self {
            // `total_mass` is defaulted to `MassValue::ONE` per
            // the spec. `total` is retained only as a marker for
            // test legibility; the trait impl never reads it.
            Self { total: MassValue::ONE }
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
            // Per TTC §1, `total_mass` must be 1.0; the former
            // `seeds * 3.0` value predated the fraction-based
            // contract.
            Box::new(CounterMass { total: MassValue::ONE })
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
        let total_level: u64 = forcings.stage_level.values().sum();
        let total_feature: u64 = forcings.stage_feature.values().sum();
        assert_eq!(total_level, 6 * (3 + 5));
        // docs/TELEMETRY.md §4 consistency rule: when both axes are
        // populated from the same forcing events, their totals MUST
        // be equal. CounterStage emits each event exactly once per
        // (level, feature) pair, so this equality is invariant.
        assert_eq!(total_level, total_feature,
            "TELEMETRY.md §4 consistency rule: stage_level and stage_feature MUST sum to the same total when populated from the same events");
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

    /// TTC §5.1 + §10 item 5: split paths MUST NOT double-count
    /// credited mass. A parent that credits 0.3 and splits into
    /// two children, where each child credits 0.2, should yield
    /// total covered = 0.7 — not 0.7 doubled. The engine applies
    /// `mass_delta` exactly once per `apply_report` call, so the
    /// correctness of this rule depends on adapters not
    /// re-crediting residuals; this test is a belt-and-braces
    /// assertion against the engine-side plumbing.
    #[test]
    fn split_credit_flows_once_per_apply_report() {
        struct SplitCreditStage {
            counter: Arc<AtomicU64>,
        }
        impl StageHandler<u64> for SplitCreditStage {
            fn id(&self) -> StageId { "split_credit" }
            fn handle(&self, item: WorkItem<u64>, _ctx: &StageContext<'_>) -> StageOutcome<u64> {
                self.counter.fetch_add(1, Ordering::Relaxed);
                let mut out = StageOutcome::default();
                match item.payload {
                    0 => {
                        // Parent: credit 0.3 exact and split into
                        // two residual children that each credit
                        // 0.2 — total credited mass 0.7.
                        out.mass_delta = MassDelta {
                            covered_exact: MassValue(0.3),
                            covered_partial: MassValue::ZERO,
                        };
                        let mk_child = |bump: u64| WorkItem {
                            stage_id: "split_credit",
                            priority: 0,
                            cost_hint: 1,
                            replay_key: 0,
                            mass_hint: None,
                            meta: WorkItemMeta {
                                item_id: bump,
                                parent_item_id: Some(item.meta.item_id),
                                fanout_root_id: item.meta.fanout_root_id,
                                depth_from_root: 1,
                                spawn_seq: bump as u32,
                            },
                            payload: 1,
                        };
                        out.continuation = Continuation::Split(vec![mk_child(10), mk_child(11)]);
                    }
                    _ => {
                        out.mass_delta = MassDelta {
                            covered_exact: MassValue(0.2),
                            covered_partial: MassValue::ZERO,
                        };
                    }
                }
                out
            }
        }

        struct SplitCreditAdapter { counter: Arc<AtomicU64> }
        impl SearchModeAdapter<u64> for SplitCreditAdapter {
            fn name(&self) -> &'static str { "split_credit" }
            fn init(&self) -> AdapterInit<u64> {
                AdapterInit {
                    seed_items: vec![WorkItem {
                        stage_id: "split_credit",
                        priority: 0,
                        cost_hint: 1,
                        replay_key: 0,
                        mass_hint: None,
                        meta: WorkItemMeta {
                            item_id: 1,
                            parent_item_id: None,
                            fanout_root_id: 1,
                            depth_from_root: 0,
                            spawn_seq: 0,
                        },
                        payload: 0,
                    }],
                }
            }
            fn stages(&self) -> BTreeMap<StageId, Box<dyn StageHandler<u64>>> {
                let mut m: BTreeMap<StageId, Box<dyn StageHandler<u64>>> = BTreeMap::new();
                m.insert("split_credit", Box::new(SplitCreditStage {
                    counter: Arc::clone(&self.counter),
                }));
                m
            }
            fn mass_model(&self) -> Box<dyn SearchMassModel> {
                Box::new(CounterMass { total: MassValue::ONE })
            }
        }

        let counter = Arc::new(AtomicU64::new(0));
        let adapter = SplitCreditAdapter { counter: Arc::clone(&counter) };
        let p = final_snapshot::<u64>(&adapter);
        // Three handle() calls: parent + 2 children.
        assert_eq!(counter.load(Ordering::Relaxed), 3);
        let covered = p.covered_mass.0;
        // Expected: 0.3 + 0.2 + 0.2 = 0.7. Any double-count would
        // push this above 0.7 (or trip the 1.0 clamp and still be
        // wrong).
        assert!((covered - 0.7).abs() < 1e-9,
            "split credit must be additive, not double-counted: got {}", covered);
        assert!(covered <= p.total_mass.0 + 1e-12,
            "covered_mass MUST stay ≤ total per TTC §3");
    }

    /// TTC §1: `total_search_mass MUST equal 1.0` for every live
    /// adapter's mass model. Synthetic test adapters get the same
    /// contract — the test-only `CounterMass` returns the
    /// default.
    #[test]
    fn all_test_adapters_total_mass_is_one() {
        assert_eq!(CounterMass { total: MassValue::ONE }.total_mass().0, 1.0);
    }

    /// TTC §5.2 Resume semantics: progress already credited before
    /// the resume MUST persist; the resumed item MUST NOT be
    /// treated as a fresh full-mass subproblem; completion of the
    /// resumed item MUST credit only the remaining uncovered
    /// mass. This test constructs a two-call handler sequence
    /// where the parent credits 0.3 then resumes, and the resumed
    /// call credits 0.2 — the cumulative covered_mass MUST be 0.5,
    /// not 0.3 + 0.3 + 0.2 = 0.8 or any other variant implying
    /// the parent's credit was double-booked on resume.
    #[test]
    fn resume_preserves_prior_credit_without_refresh() {
        use std::sync::atomic::AtomicU64 as A64;
        struct ResumeCreditStage {
            phase: Arc<A64>,
        }
        impl StageHandler<u64> for ResumeCreditStage {
            fn id(&self) -> StageId { "resume_credit" }
            fn handle(&self, item: WorkItem<u64>, _ctx: &StageContext<'_>) -> StageOutcome<u64> {
                let ph = self.phase.fetch_add(1, Ordering::Relaxed);
                let mut out = StageOutcome::default();
                match ph {
                    0 => {
                        // First call: credit 0.3 of the parent
                        // subproblem (eliminated so far), then
                        // Resume — the resumed logical item
                        // represents the remaining 0.7.
                        out.mass_delta = MassDelta {
                            covered_exact: MassValue(0.3),
                            covered_partial: MassValue::ZERO,
                        };
                        out.continuation = Continuation::Resume(WorkItem {
                            stage_id: "resume_credit",
                            priority: 0,
                            cost_hint: 1,
                            replay_key: 0,
                            mass_hint: None,
                            meta: WorkItemMeta {
                                item_id: item.meta.item_id,
                                parent_item_id: item.meta.parent_item_id,
                                fanout_root_id: item.meta.fanout_root_id,
                                depth_from_root: item.meta.depth_from_root,
                                spawn_seq: item.meta.spawn_seq + 1,
                            },
                            payload: item.payload + 1,
                        });
                    }
                    1 => {
                        // Resumed call: credit only the additional
                        // 0.2 eliminated this pass. Spec says the
                        // resumed item MUST NOT be treated as a
                        // fresh 1.0 subproblem — so the total is
                        // 0.3 + 0.2 = 0.5, not 1.0, not 1.3.
                        out.mass_delta = MassDelta {
                            covered_exact: MassValue(0.2),
                            covered_partial: MassValue::ZERO,
                        };
                    }
                    _ => {}
                }
                out
            }
        }

        struct ResumeCreditAdapter { phase: Arc<A64> }
        impl SearchModeAdapter<u64> for ResumeCreditAdapter {
            fn name(&self) -> &'static str { "resume_credit" }
            fn init(&self) -> AdapterInit<u64> {
                AdapterInit {
                    seed_items: vec![WorkItem {
                        stage_id: "resume_credit",
                        priority: 0,
                        cost_hint: 1,
                        replay_key: 0,
                        mass_hint: None,
                        meta: WorkItemMeta {
                            item_id: 1,
                            parent_item_id: None,
                            fanout_root_id: 1,
                            depth_from_root: 0,
                            spawn_seq: 0,
                        },
                        payload: 0,
                    }],
                }
            }
            fn stages(&self) -> BTreeMap<StageId, Box<dyn StageHandler<u64>>> {
                let mut m: BTreeMap<StageId, Box<dyn StageHandler<u64>>> = BTreeMap::new();
                m.insert("resume_credit", Box::new(ResumeCreditStage {
                    phase: Arc::clone(&self.phase),
                }));
                m
            }
            fn mass_model(&self) -> Box<dyn SearchMassModel> {
                Box::new(CounterMass { total: MassValue::ONE })
            }
        }

        let phase = Arc::new(A64::new(0));
        let adapter = ResumeCreditAdapter { phase: Arc::clone(&phase) };
        let p = final_snapshot::<u64>(&adapter);
        assert_eq!(phase.load(Ordering::Relaxed), 2,
            "resume should produce exactly 2 handle() calls");
        assert!((p.covered_mass.0 - 0.5).abs() < 1e-9,
            "Resume MUST persist prior 0.3 credit and add only 0.2: total covered = 0.5, got {}",
            p.covered_mass.0);
        assert!(p.covered_mass.0 <= p.total_mass.0 + 1e-12,
            "covered MUST stay ≤ total per TTC §3");
    }

    /// TTC §3 invariant 6 + §7.3 monotone envelope: a
    /// `SearchMassModel` whose `covered_mass()` fluctuates downward
    /// between ticks (e.g., sync walker's projected-fraction
    /// estimator lowering as new samples arrive) MUST NOT cause
    /// the published `ProgressSnapshot.covered_mass` to decrease.
    /// The engine's `poll_mass` helper holds the high-water mark;
    /// this end-to-end test exercises that contract against the
    /// real engine coordinator loop, not just the helper in
    /// isolation.
    #[test]
    fn engine_publishes_monotone_envelope_against_fluctuating_model() {
        use crate::search_framework::mass::MassSnapshot;
        use std::sync::atomic::AtomicU64 as A64;
        use std::time::Duration;

        /// Mass model whose `covered_mass` reads a sequence of
        /// published ppm values that go up, then down, then up
        /// again. The engine poll_mass MUST hold the high-water.
        struct FluctuatingMass {
            ppm: Arc<A64>,
        }
        impl SearchMassModel for FluctuatingMass {
            fn covered_mass(&self) -> MassValue {
                MassValue(self.ppm.load(Ordering::Relaxed) as f64 / 1_000_000.0)
            }
            fn quality(&self) -> CoverageQuality {
                CoverageQuality::Projected
            }
        }

        /// Long-running handler that advances `ppm` through a
        /// non-monotone sequence between progress ticks, then
        /// terminates. Emits a trickle of successor items so the
        /// engine coordinator loop stays alive long enough to
        /// observe multiple progress ticks.
        struct FluctuatingStage {
            ppm: Arc<A64>,
            schedule: Arc<Vec<u64>>,
            calls: Arc<A64>,
        }
        impl StageHandler<u64> for FluctuatingStage {
            fn id(&self) -> StageId { "fluctuating" }
            fn handle(&self, item: WorkItem<u64>, _ctx: &StageContext<'_>) -> StageOutcome<u64> {
                let idx = self.calls.fetch_add(1, Ordering::Relaxed) as usize;
                if let Some(&v) = self.schedule.get(idx) {
                    self.ppm.store(v, Ordering::Relaxed);
                }
                let mut out = StageOutcome::default();
                // Sleep briefly so the engine's progress_interval
                // fires between successive handle() calls.
                std::thread::sleep(Duration::from_millis(25));
                if (idx + 1) < self.schedule.len() {
                    out.emitted.push(WorkItem {
                        stage_id: "fluctuating",
                        priority: 0,
                        cost_hint: 1,
                        replay_key: 0,
                        mass_hint: None,
                        meta: WorkItemMeta {
                            item_id: (idx as u64) + 100,
                            parent_item_id: Some(item.meta.item_id),
                            fanout_root_id: item.meta.fanout_root_id,
                            depth_from_root: item.meta.depth_from_root + 1,
                            spawn_seq: 0,
                        },
                        payload: item.payload + 1,
                    });
                }
                out
            }
        }

        struct FluctuatingAdapter {
            ppm: Arc<A64>,
            schedule: Arc<Vec<u64>>,
            calls: Arc<A64>,
        }
        impl SearchModeAdapter<u64> for FluctuatingAdapter {
            fn name(&self) -> &'static str { "fluctuating" }
            fn init(&self) -> AdapterInit<u64> {
                AdapterInit {
                    seed_items: vec![WorkItem {
                        stage_id: "fluctuating",
                        priority: 0,
                        cost_hint: 1,
                        replay_key: 0,
                        mass_hint: None,
                        meta: WorkItemMeta {
                            item_id: 1,
                            parent_item_id: None,
                            fanout_root_id: 1,
                            depth_from_root: 0,
                            spawn_seq: 0,
                        },
                        payload: 0,
                    }],
                }
            }
            fn stages(&self) -> BTreeMap<StageId, Box<dyn StageHandler<u64>>> {
                let mut m: BTreeMap<StageId, Box<dyn StageHandler<u64>>> = BTreeMap::new();
                m.insert("fluctuating", Box::new(FluctuatingStage {
                    ppm: Arc::clone(&self.ppm),
                    schedule: Arc::clone(&self.schedule),
                    calls: Arc::clone(&self.calls),
                }));
                m
            }
            fn mass_model(&self) -> Box<dyn SearchMassModel> {
                Box::new(FluctuatingMass { ppm: Arc::clone(&self.ppm) })
            }
        }

        // The estimator climbs to 50%, drops to 30%, climbs to
        // 70%, drops to 40%, lands at 80%. The engine snapshot
        // stream MUST stay monotone across ticks regardless.
        let schedule = Arc::new(vec![
            500_000,
            300_000,  // drop — engine MUST ignore this downward move
            700_000,
            400_000,  // drop — engine MUST still hold 700_000 high-water
            800_000,
        ]);
        let ppm = Arc::new(A64::new(0));
        let calls = Arc::new(A64::new(0));
        let adapter = FluctuatingAdapter {
            ppm: Arc::clone(&ppm),
            schedule: Arc::clone(&schedule),
            calls: Arc::clone(&calls),
        };

        let cfg = EngineConfig {
            progress_interval: Duration::from_millis(10),
            worker_count: 1,
        };
        let mut engine = SearchEngine::<u64>::new(cfg, Box::new(GoldThenWork::new(4)));
        let observed = Arc::new(std::sync::Mutex::new(Vec::<(f64, MassSnapshot)>::new()));
        let observed_cb = Arc::clone(&observed);
        engine.run(&adapter, move |event| {
            let (covered, snap_total) = match &event {
                SearchEvent::Progress(p) => (p.covered_mass.0, p.total_mass),
                SearchEvent::Finished(p) => (p.covered_mass.0, p.total_mass),
            };
            observed_cb.lock().unwrap().push((
                covered,
                MassSnapshot {
                    total: snap_total,
                    covered_exact: MassValue(covered),
                    covered_partial: MassValue::ZERO,
                },
            ));
        });

        let observed = observed.lock().unwrap();
        assert!(!observed.is_empty(), "engine MUST emit at least one snapshot");
        // Final value MUST reflect the highest ever observed ppm
        // (which is 800_000 = 0.8).
        let final_covered = observed.last().unwrap().0;
        assert!(
            (final_covered - 0.8).abs() < 1e-9,
            "engine Finished covered_mass MUST reflect the high-water mark (0.8); got {}",
            final_covered,
        );
        // Strict monotonicity across every consecutive snapshot.
        for w in observed.windows(2) {
            assert!(
                w[1].0 + 1e-9 >= w[0].0,
                "covered_mass MUST be monotone non-decreasing: {} -> {} violates §3.6 / §7.3",
                w[0].0, w[1].0,
            );
        }
    }

    /// Verifies the TELEMETRY §3 pre-decrement assertion in
    /// `apply_report` actually fires when the fanout root entry
    /// is zero before decrement. Without the assertion,
    /// saturating_sub would silently absorb the underflow and
    /// hide a bookkeeping bug (e.g. a handler emitting a child
    /// with a stale / unregistered `fanout_root_id`). Calls
    /// `apply_report` directly rather than running a full engine
    /// — an engine-harness panic fires inside a worker thread and
    /// the coordinator deadlocks, which `#[should_panic]` can't
    /// observe cleanly.
    #[test]
    #[should_panic(expected = "apply_report on fanout_root_id=")]
    #[cfg(debug_assertions)]
    fn apply_report_panics_on_unregistered_root() {
        use crate::search_framework::mass::MassSnapshot;
        use crate::search_framework::queue::GoldThenWork;

        let scheduler: SharedScheduler<u64> = Arc::new((
            Mutex::new(Box::new(GoldThenWork::new(4)) as Box<dyn SchedulerPolicy<u64>>),
            Condvar::new(),
        ));
        let mut mass = MassSnapshot::new(MassValue::ONE);
        let mut forcings = ForcingRollups::default();
        let mut edge_flow: BTreeMap<(String, String), EdgeFlowCounters> = BTreeMap::new();
        // Empty `fanout_roots` intentionally — the decrement path
        // should catch this before saturating_sub masks it.
        let mut fanout_roots: BTreeMap<u64, FanoutRootCounters> = BTreeMap::new();

        let report = WorkerReport::<u64> {
            from_stage: "ghost",
            fanout_root_id: 0xDEADBEEF, // never seeded
            outcome: StageOutcome::default(),
        };
        apply_report(
            report,
            &scheduler,
            &mut mass,
            &mut forcings,
            &mut edge_flow,
            &mut fanout_roots,
        );
    }

    /// TELEMETRY.md §5 deferrals: "The same residual search space
    /// MUST NOT be counted both as covered and as fully live
    /// remainder." Verifies that a handler which credits 0.4 and
    /// defers a continuation does NOT also surface that 0.4 as
    /// live descendant work — live_descendants reflects only the
    /// uncovered residual items, not the already-credited mass.
    #[test]
    fn deferral_does_not_double_count_mass_as_live() {
        use std::sync::atomic::AtomicU64 as A64;
        struct DeferCreditStage {
            counter: Arc<A64>,
        }
        impl StageHandler<u64> for DeferCreditStage {
            fn id(&self) -> StageId { "defer_credit" }
            fn handle(&self, item: WorkItem<u64>, _ctx: &StageContext<'_>) -> StageOutcome<u64> {
                self.counter.fetch_add(1, Ordering::Relaxed);
                let mut out = StageOutcome::default();
                match item.payload {
                    0 => {
                        // Credit 0.4 of the original cube then
                        // split the remaining 0.6 into a single
                        // residual child. Credit + residual
                        // children = 1 logical unit; but ONLY the
                        // residual shows up in live_descendants.
                        out.mass_delta = MassDelta {
                            covered_exact: MassValue(0.4),
                            covered_partial: MassValue::ZERO,
                        };
                        out.continuation = Continuation::Split(vec![WorkItem {
                            stage_id: "defer_credit",
                            priority: 0,
                            cost_hint: 1,
                            replay_key: 0,
                            mass_hint: None,
                            meta: WorkItemMeta {
                                item_id: 42,
                                parent_item_id: Some(item.meta.item_id),
                                fanout_root_id: item.meta.fanout_root_id,
                                depth_from_root: 1,
                                spawn_seq: 0,
                            },
                            payload: 1,
                        }]);
                    }
                    _ => {
                        // Residual child closes the remaining 0.6.
                        out.mass_delta = MassDelta {
                            covered_exact: MassValue(0.6),
                            covered_partial: MassValue::ZERO,
                        };
                    }
                }
                out
            }
        }

        struct DeferCreditAdapter { counter: Arc<A64> }
        impl SearchModeAdapter<u64> for DeferCreditAdapter {
            fn name(&self) -> &'static str { "defer_credit" }
            fn init(&self) -> AdapterInit<u64> {
                AdapterInit {
                    seed_items: vec![WorkItem {
                        stage_id: "defer_credit",
                        priority: 0,
                        cost_hint: 1,
                        replay_key: 0,
                        mass_hint: None,
                        meta: WorkItemMeta {
                            item_id: 1,
                            parent_item_id: None,
                            fanout_root_id: 99,
                            depth_from_root: 0,
                            spawn_seq: 0,
                        },
                        payload: 0,
                    }],
                }
            }
            fn stages(&self) -> BTreeMap<StageId, Box<dyn StageHandler<u64>>> {
                let mut m: BTreeMap<StageId, Box<dyn StageHandler<u64>>> = BTreeMap::new();
                m.insert("defer_credit", Box::new(DeferCreditStage {
                    counter: Arc::clone(&self.counter),
                }));
                m
            }
            fn mass_model(&self) -> Box<dyn SearchMassModel> {
                Box::new(CounterMass { total: MassValue::ONE })
            }
        }

        let counter = Arc::new(A64::new(0));
        let adapter = DeferCreditAdapter { counter: Arc::clone(&counter) };
        let p = final_snapshot::<u64>(&adapter);
        assert_eq!(counter.load(Ordering::Relaxed), 2);
        // Final: covered = 0.4 (parent) + 0.6 (residual child) = 1.0.
        // If the residual's mass were double-counted as already
        // covered, we'd see covered > 1.0 (clamped, but the test
        // construction makes the miscount visible via the
        // live_descendants dump).
        assert!((p.covered_mass.0 - 1.0).abs() < 1e-9,
            "credit + residual-completion MUST equal parent incoming mass; got {}",
            p.covered_mass.0);
        // At end, all work completed: live_descendants = 0.
        let live = p.fanout_roots.get(&99).map(|c| c.live_descendants).unwrap_or(0);
        assert_eq!(live, 0,
            "live_descendants MUST drain to 0 once residual completes; got {}", live);
    }

    /// TTC §3 invariants + §7.3 monotone envelope: the coordinator's
    /// `poll_mass` helper MUST (a) never let either axis decrease,
    /// (b) always keep `covered_exact + covered_partial ≤ total`
    /// even when `covered_exact` grows in the same tick that the
    /// mass model's partial counter has reset to a lower value.
    /// This reproduces the pre-fix Cross scenario: partial hit a
    /// high-water mark mid-tuple, then a tuple completed (exact
    /// bumped, partial counter zeroed) — without the re-clamp the
    /// published covered could exceed 1.0.
    #[test]
    fn poll_mass_clamps_high_water_partial_when_exact_grows() {
        use crate::search_framework::mass::MassSnapshot;
        struct TestModel {
            exact: std::sync::Mutex<f64>,
            partial: std::sync::Mutex<f64>,
        }
        impl SearchMassModel for TestModel {
            fn covered_mass(&self) -> MassValue {
                MassValue(*self.exact.lock().unwrap())
            }
            fn covered_partial_mass(&self) -> MassValue {
                MassValue(*self.partial.lock().unwrap())
            }
            fn quality(&self) -> CoverageQuality {
                CoverageQuality::Hybrid
            }
        }
        let model = TestModel {
            exact: std::sync::Mutex::new(0.0),
            partial: std::sync::Mutex::new(0.0),
        };
        let mut mass = MassSnapshot::new(MassValue::ONE);

        // Tick 1: exact=0, partial=0.3 in-flight.
        *model.partial.lock().unwrap() = 0.3;
        poll_mass(&model, &mut mass);
        assert!((mass.covered().0 - 0.3).abs() < 1e-9);

        // Tick 2: partial transient peaks at 0.6; still room under 1.0.
        *model.partial.lock().unwrap() = 0.6;
        poll_mass(&model, &mut mass);
        assert!((mass.covered().0 - 0.6).abs() < 1e-9);

        // Tick 3: a chunk completes — exact jumps to 0.8 and the
        // model zeros its in-flight partial. `covered_partial`
        // must NOT stay at its 0.6 high-water; it MUST clamp to
        // 1.0 - 0.8 = 0.2 so the published covered stays ≤ 1.0.
        *model.exact.lock().unwrap() = 0.8;
        *model.partial.lock().unwrap() = 0.0;
        poll_mass(&model, &mut mass);
        assert!(mass.covered().0 <= 1.0 + 1e-12,
            "covered MUST stay ≤ total; got exact={} partial={}",
            mass.covered_exact.0, mass.covered_partial.0);
        assert!(mass.covered_exact.0 >= 0.8,
            "covered_exact is monotone non-decreasing");
        // Tick 4: exact advances further. Partial stays ≤ residual.
        *model.exact.lock().unwrap() = 1.0;
        poll_mass(&model, &mut mass);
        assert!((mass.covered().0 - 1.0).abs() < 1e-9);
    }

    /// TELEMETRY.md §4 consistency rule, direct unit test at the
    /// rollup helper level so future adapter code can't silently
    /// diverge the two axes. Any single `ForcingDelta` applied via
    /// `ForcingRollups::apply` MUST produce equal totals across
    /// `stage_level` and `stage_feature`.
    #[test]
    fn forcing_rollups_consistency_equality_invariant() {
        let mut rollups = ForcingRollups::default();
        let deltas = [
            ForcingDelta { by_level_feature: vec![(0, 0, 3), (1, 2, 5), (3, 4, 7)] },
            ForcingDelta { by_level_feature: vec![(0, 4, 1), (2, 0, 9)] },
        ];
        for d in &deltas {
            rollups.apply("stageA", d);
        }
        rollups.apply("stageB", &ForcingDelta { by_level_feature: vec![(0, 0, 11)] });
        let sum_level: u64 = rollups.stage_level.values().sum();
        let sum_feature: u64 = rollups.stage_feature.values().sum();
        assert_eq!(sum_level, sum_feature,
            "forcing axes MUST sum to the same total per TELEMETRY.md §4 consistency rule");
    }
}
