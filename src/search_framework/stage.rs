use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use crate::search_framework::mass::MassDelta;

pub type StageId = &'static str;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct WorkItemMeta {
    pub item_id: u64,
    pub parent_item_id: Option<u64>,
    pub fanout_root_id: u64,
    pub depth_from_root: u16,
    pub spawn_seq: u32,
}

/// A scheduled unit of search work.
///
/// `priority` is a loose tag that the baseline scheduler reads as
/// `> 0` ⇒ "gold" lane, `<= 0` ⇒ "work" lane. Handlers that defer
/// residual sub-cubes back onto the queue should set a priority that
/// reflects their own confidence in the remainder:
///
///   * `priority = 2+` — "valuable": likely to contain a solution or
///     shrink a tight bound; the scheduler should pull it before
///     fresh low-ranked items.
///   * `priority = 1` — "maybe": ordinary work, same lane as fresh
///     items.
///   * `priority = 0` — "junk": large but low-yield residual, pulled
///     only when nothing else is available.
///
/// Absolute values above 2 are not meaningful to the baseline
/// scheduler but may be read by custom policies.
#[derive(Clone, Debug, PartialEq)]
pub struct WorkItem<T> {
    pub stage_id: StageId,
    pub priority: i32,
    pub cost_hint: u32,
    pub replay_key: u64,
    pub mass_hint: Option<f64>,
    pub meta: WorkItemMeta,
    pub payload: T,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FanoutDelta {
    pub children_emitted: u64,
    pub children_dropped: u64,
    pub children_merged: u64,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DiagEvent {
    pub code: &'static str,
    pub message: Arc<str>,
}

/// Per-`(level, feature)` forced-literal counts attributed to the
/// stage that produced this outcome. Feeds the coordinator's
/// `[stage, level]` and `[stage, feature]` rollups (the `[feature,
/// level]` rollup is owned by radical and read directly from the
/// solver).
///
/// Entries are `(decision_level, PropKind::as usize, count)`; a stage
/// that forced no literals returns an empty `Vec`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ForcingDelta {
    pub by_level_feature: Vec<(u16, u8, u32)>,
}

impl ForcingDelta {
    pub fn is_empty(&self) -> bool {
        self.by_level_feature.is_empty()
    }

    /// Total forced literals across all (level, feature) pairs.
    pub fn total(&self) -> u64 {
        self.by_level_feature.iter().map(|(_, _, c)| *c as u64).sum()
    }
}

/// How a handler hands the residual sub-cube back to the scheduler
/// when it runs out of budget.
///
/// There is no "timed out" outcome in this framework. A handler that
/// exhausts a conflict, wall-clock, or heap budget always returns (a)
/// a [`MassDelta`] crediting the cube it actually covered and (b) one
/// of the variants below describing what to do with the rest.
pub enum Continuation<T> {
    /// Handler finished the entire sub-cube. Nothing to resume.
    None,
    /// Residual split into smaller cubes (e.g. branch on one more
    /// variable). Each child re-enters the scheduler as a fresh
    /// item, tagged with its own priority.
    Split(Vec<WorkItem<T>>),
    /// Same sub-cube, resumed from a saved solver checkpoint carried
    /// in the item's payload. Used by SolveW/SolveZ which can call
    /// `Solver::save_checkpoint()`/`restore_checkpoint()`.
    Resume(WorkItem<T>),
}

impl<T> Default for Continuation<T> {
    fn default() -> Self {
        Continuation::None
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for Continuation<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Continuation::None => f.write_str("Continuation::None"),
            Continuation::Split(items) => {
                write!(f, "Continuation::Split(len={})", items.len())
            }
            Continuation::Resume(_) => f.write_str("Continuation::Resume(..)"),
        }
    }
}

pub struct StageOutcome<T> {
    pub emitted: Vec<WorkItem<T>>,
    pub continuation: Continuation<T>,
    pub mass_delta: MassDelta,
    pub fanout_delta: FanoutDelta,
    pub diagnostics: Vec<DiagEvent>,
    pub forcings: ForcingDelta,
}

impl<T> Default for StageOutcome<T> {
    fn default() -> Self {
        Self {
            emitted: Vec::new(),
            continuation: Continuation::None,
            mass_delta: MassDelta::default(),
            fanout_delta: FanoutDelta::default(),
            diagnostics: Vec::new(),
            forcings: ForcingDelta::default(),
        }
    }
}

/// Context passed into every `StageHandler::handle` call.
///
/// `cancelled` is a **live** handle into the engine's cancel flag —
/// long-running handlers (e.g. cross's O(2^(4k)) brute-force
/// enumeration) should poll it inside their inner loops so the
/// engine's `cancel()` or the drain thread's solution-found hook
/// actually stops work in flight. Use [`StageContext::is_cancelled`]
/// for a `bool` snapshot at poll time.
pub struct StageContext<'a> {
    pub cancelled: &'a AtomicBool,
    pub now_millis: u128,
    pub adapter_name: &'a str,
}

impl StageContext<'_> {
    /// Snapshot of the live cancel flag. Safe to call in a tight loop
    /// — one relaxed atomic load.
    pub fn is_cancelled(&self) -> bool {
        self.cancelled
            .load(std::sync::atomic::Ordering::Relaxed)
    }
}

pub trait StageHandler<T>: Send + Sync {
    fn id(&self) -> StageId;
    fn handle(&self, item: WorkItem<T>, ctx: &StageContext<'_>) -> StageOutcome<T>;
}
