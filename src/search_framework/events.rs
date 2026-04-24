use std::collections::BTreeMap;
use std::fmt::Write;
use std::time::Duration;

use crate::search_framework::mass::{MassValue, TtcQuality};
use crate::search_framework::stage::StageId;

/// Per-edge lifecycle counter. Only `spawned` is populated today
/// (every `WorkItem` pushed from a parent stage to a child stage
/// is counted). `dropped` / `queued` / `started` / `completed`
/// were part of the originally-proposed Sankey schema but the
/// engine does not track item lifecycle transitions yet; they are
/// deliberately not in this struct to avoid publishing an
/// apparently-richer surface than the data supports. Restore them
/// once the coordinator tracks queue depth + start / completion
/// per edge.
#[derive(Clone, Debug, Default)]
pub struct EdgeFlowCounters {
    pub spawned: u64,
}

/// Per-fan-out-root counter. `live_descendants` tracks the
/// current in-flight subtree size — incremented by 1 per
/// emitted child and decremented by 1 per completed item, so
/// the count hits zero when the whole subtree finishes.
/// `completed_descendants` / `credited_mass` are part of the
/// proposed fan-out viz schema but not wired; see the
/// [`EdgeFlowCounters`] note above.
#[derive(Clone, Debug, Default)]
pub struct FanoutRootCounters {
    pub live_descendants: u64,
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

/// Minimal Sankey-flavoured text dump. Today only the `spawned`
/// column is meaningful — see [`EdgeFlowCounters`]. The full
/// `in → filtered → queued → started → completed` layout from
/// `UNIFIED_SEARCH_FRAMEWORK_SPEC.md` §8.1 lands when those fields
/// get wired.
pub fn render_sankey_text(edge_flow: &BTreeMap<(String, String), EdgeFlowCounters>) -> String {
    let mut out = String::new();
    out.push_str("edge | spawned\n");
    for ((from, to), c) in edge_flow {
        let _ = writeln!(out, "{}->{} | {}", from, to, c.spawned);
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
