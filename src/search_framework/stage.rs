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

#[derive(Clone, Debug, Default, PartialEq)]
pub struct StageOutcome<T> {
    pub emitted: Vec<WorkItem<T>>,
    pub mass_delta: MassDelta,
    pub fanout_delta: FanoutDelta,
    pub diagnostics: Vec<DiagEvent>,
}

pub struct StageContext<'a> {
    pub cancelled: bool,
    pub now_millis: u128,
    pub adapter_name: &'a str,
}

pub trait StageHandler<T>: Send + Sync {
    fn id(&self) -> StageId;
    fn handle(&self, item: WorkItem<T>, ctx: &StageContext<'_>) -> StageOutcome<T>;
}
