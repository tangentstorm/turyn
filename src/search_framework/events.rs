use std::collections::BTreeMap;
use std::fmt::Write;
use std::time::Duration;

use crate::search_framework::mass::{MassValue, TtcQuality};
use crate::search_framework::stage::StageId;

#[derive(Clone, Debug, Default)]
pub struct EdgeFlowCounters {
    pub spawned: u64,
    pub dropped: u64,
    pub queued: u64,
    pub started: u64,
    pub completed: u64,
}

#[derive(Clone, Debug, Default)]
pub struct FanoutRootCounters {
    pub live_descendants: u64,
    pub completed_descendants: u64,
    pub credited_mass: MassValue,
}

/// Two 2-D forcing rollups owned by the coordinator (the third —
/// `[feature, level]` — is read directly from radical's
/// `propagations_by_kind_level`). Both maps accumulate across the
/// whole run, fed by each `StageOutcome::forcings` delta.
#[derive(Clone, Debug, Default)]
pub struct ForcingRollups {
    /// `[stage, decision_level] -> forced literal count`.
    pub stage_level: BTreeMap<(StageId, u16), u64>,
    /// `[stage, PropKind as u8] -> forced literal count`.
    pub stage_feature: BTreeMap<(StageId, u8), u64>,
}

impl ForcingRollups {
    pub fn apply(
        &mut self,
        stage: StageId,
        delta: &crate::search_framework::stage::ForcingDelta,
    ) {
        for &(level, feature, count) in &delta.by_level_feature {
            let c = count as u64;
            *self.stage_level.entry((stage, level)).or_insert(0) += c;
            *self.stage_feature.entry((stage, feature)).or_insert(0) += c;
        }
    }
}

#[derive(Clone, Debug)]
pub struct ProgressSnapshot {
    pub elapsed: Duration,
    pub throughput_per_sec: MassValue,
    pub covered_mass: MassValue,
    pub total_mass: MassValue,
    pub remaining_mass: MassValue,
    pub ttc: Option<Duration>,
    pub quality: TtcQuality,
    pub edge_flow: BTreeMap<(String, String), EdgeFlowCounters>,
    pub fanout_roots: BTreeMap<u64, FanoutRootCounters>,
    pub forcings: ForcingRollups,
}

#[derive(Clone, Debug)]
pub enum SearchEvent {
    Progress(ProgressSnapshot),
    Finished(ProgressSnapshot),
}

#[derive(Clone, Debug, Default)]
pub struct LevelCutAttribution {
    pub level: usize,
    pub cut_source: String,
    pub absolute_cuts: u64,
    pub cut_share: f64,
}

pub fn render_sankey_text(edge_flow: &BTreeMap<(String, String), EdgeFlowCounters>) -> String {
    let mut out = String::new();
    out.push_str("edge | spawned -> dropped -> queued -> started -> completed\n");
    for ((from, to), c) in edge_flow {
        let _ = writeln!(
            out,
            "{}->{} | {} -> {} -> {} -> {} -> {}",
            from, to, c.spawned, c.dropped, c.queued, c.started, c.completed
        );
    }
    out
}

pub fn render_cut_attribution_text(rows: &[LevelCutAttribution]) -> String {
    let mut out = String::new();
    out.push_str("level | source | absolute | share\n");
    for row in rows {
        let _ = writeln!(
            out,
            "{} | {} | {} | {:.4}",
            row.level, row.cut_source, row.absolute_cuts, row.cut_share
        );
    }
    out
}
