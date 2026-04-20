use std::collections::BTreeMap;
use std::fmt::Write;
use std::time::Duration;

use crate::search_framework::mass::{CoverageQuality, MassValue};

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

#[derive(Clone, Debug)]
pub struct ProgressSnapshot {
    pub elapsed: Duration,
    pub throughput_per_sec: MassValue,
    pub covered_mass: MassValue,
    pub total_mass: MassValue,
    pub remaining_mass: MassValue,
    pub ttc: Option<Duration>,
    pub quality: CoverageQuality,
    pub edge_flow: BTreeMap<(String, String), EdgeFlowCounters>,
    pub fanout_roots: BTreeMap<u64, FanoutRootCounters>,
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
