//! Framework adapter for `--wz=cross`.
//!
//! Unlike `MddStagesAdapter` (which enumerates live MDD boundary
//! paths and dispatches them through Boundary → SolveW → SolveZ),
//! the cross path is a **brute-force Z × W producer**: for each
//! sum tuple we enumerate every full Z sequence and every full W
//! sequence that passes its spectral filter, bucket the W sides
//! by frequency via `SpectralIndex`, and cross-match to yield
//! `(Z, W)` pairs that pass the combined spectral pair bound.
//! Each surviving pair is handed to the shared XY SAT fast path
//! (`walk_xy_sub_mdd` + `SolveXyPerCandidate`).
//!
//! The heavy lifting lives in `crate::enumerate::build_w_candidates`
//! and `crate::enumerate::for_each_zw_pair`; this adapter plugs
//! them into a single `CrossEnumerateStage` that runs
//! synchronously (one handler call per run) and reports the
//! solution back through a channel, matching the shape of
//! `SyncAdapter`.
//!
//! This adapter does **not** require a pre-built `mdd-<k>.bin`
//! file — the shared `build_phase_b_context` falls back to an
//! on-the-fly BFS MDD. The MDD is still used by the XY sub-walk
//! inside `SolveXyPerCandidate`, but cross-mode users no longer
//! have to generate one up front for the search to run.

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use crate::config::SearchConfig;
use crate::enumerate::{build_w_candidates, for_each_zw_pair, CandidateZW};
use crate::legacy_search::SearchStats;
use crate::mdd_pipeline::build_phase_b_context;
use crate::search_framework::engine::{AdapterInit, SearchModeAdapter};
use crate::search_framework::mass::{CoverageQuality, MassValue, SearchMassModel};
use crate::search_framework::stage::{
    StageContext, StageHandler, StageId, StageOutcome, WorkItem, WorkItemMeta,
};
use crate::spectrum::{SeqWithSpectrum, SpectralFilter, SpectralIndex};
use crate::types::{verify_tt, PackedSeq, Problem, SumTuple};
use crate::xy_sat::{walk_xy_sub_mdd, SatXYTemplate, SolveXyPerCandidate, XyTryResult};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

pub const STAGE_CROSS: StageId = "cross.enumerate";

#[derive(Clone, Debug, Default)]
pub struct CrossPayload;

pub struct CrossEnumerateStage {
    problem: Problem,
    cfg: Arc<SearchConfig>,
    tuples: Vec<SumTuple>,
    verbose: bool,
    k: usize,
    /// Counter published to the adapter so its mass model can emit
    /// a live fraction: `tuples_done / tuples.len()`.
    tuples_done: Arc<AtomicUsize>,
    found: Arc<AtomicBool>,
    result_tx: std::sync::mpsc::Sender<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>,
}

impl StageHandler<CrossPayload> for CrossEnumerateStage {
    fn id(&self) -> StageId {
        STAGE_CROSS
    }
    fn handle(
        &self,
        _item: WorkItem<CrossPayload>,
        _ctx: &StageContext<'_>,
    ) -> StageOutcome<CrossPayload> {
        let problem = self.problem;
        let cfg = &*self.cfg;
        let tuples = &self.tuples;
        let found = &*self.found;
        let spectral_z = SpectralFilter::new(problem.n, cfg.theta_samples);
        let spectral_w = SpectralFilter::new(problem.n, cfg.theta_samples);
        let mut stats = SearchStats::default();
        // Per-|σ_W| cache: W candidate arrays + `SpectralIndex`
        // reused across tuples that share a `|σ_W|`.
        let mut w_cache: HashMap<i32, (Vec<SeqWithSpectrum>, SpectralIndex)> = HashMap::new();
        let mut seen_zw: std::collections::HashSet<Vec<i32>> = std::collections::HashSet::new();

        // XY stage state. Each surviving (Z, W) pair clones a template
        // matching its tuple and walks the XY sub-MDD. The shared
        // `PhaseBContext` (built via `build_phase_b_context`) provides
        // the MDD nodes + `xy_pos_order`.
        let ctx = build_phase_b_context(problem, tuples, cfg, self.verbose, self.k);
        let k = ctx.k;
        let mut template_cache: HashMap<Vec<(i32, i32, i32, i32)>, SatXYTemplate> = HashMap::new();

        for (tuple_idx, tuple) in tuples.iter().copied().enumerate() {
            if found.load(Ordering::Relaxed) {
                break;
            }
            self.tuples_done.store(tuple_idx, Ordering::Relaxed);
            if !w_cache.contains_key(&tuple.w) {
                let w_candidates =
                    build_w_candidates(problem, tuple.w, cfg, &spectral_w, &mut stats, found);
                let w_index = SpectralIndex::build(&w_candidates);
                w_cache.insert(tuple.w, (w_candidates, w_index));
            }
            let (w_candidates, w_index) = w_cache.get(&tuple.w).unwrap();
            if found.load(Ordering::Relaxed) {
                break;
            }
            for_each_zw_pair(
                problem,
                tuple.z,
                w_candidates,
                w_index,
                cfg,
                &spectral_z,
                &mut stats,
                found,
                |z_seq, w_seq, zw, _z_spec, _w_spec| {
                    if found.load(Ordering::Relaxed) {
                        return false;
                    }
                    if !seen_zw.insert(zw.clone()) {
                        return true;
                    }
                    // Navigate the ZW half of the MDD to the xy_root
                    // for this boundary. Mirrors `process_solve_xy`'s
                    // deleted machinery, kept inline here so the XY
                    // fast path still benefits from MDD pruning
                    // without a scheduled handler round-trip.
                    let mut z_bits = 0u32;
                    let mut w_bits = 0u32;
                    for i in 0..k {
                        if z_seq.get(i) == 1 {
                            z_bits |= 1 << i;
                        }
                        if z_seq.get(problem.n - k + i) == 1 {
                            z_bits |= 1 << (k + i);
                        }
                        if w_seq.get(i) == 1 {
                            w_bits |= 1 << i;
                        }
                        if w_seq.get(problem.m() - k + i) == 1 {
                            w_bits |= 1 << (k + i);
                        }
                    }
                    let mut nid = ctx.mdd.root;
                    let mut live = true;
                    for level in 0..ctx.zw_depth {
                        if nid == turyn::mdd_reorder::DEAD {
                            live = false;
                            break;
                        }
                        let pos = ctx.xy_pos_order[level];
                        let z_val = (z_bits >> pos) & 1;
                        let w_val = (w_bits >> pos) & 1;
                        let branch = (z_val | (w_val << 1)) as usize;
                        if nid != turyn::mdd_reorder::LEAF {
                            nid = ctx.mdd.nodes[nid as usize][branch];
                        }
                    }
                    if !live || nid == turyn::mdd_reorder::DEAD {
                        return true;
                    }
                    let xy_root = nid;

                    let tuple_key: Vec<(i32, i32, i32, i32)> =
                        vec![(tuple.x, tuple.y, tuple.z, tuple.w)];
                    let template = template_cache.entry(tuple_key).or_insert_with(|| {
                        SatXYTemplate::build_multi_opts(
                            problem,
                            std::slice::from_ref(&tuple),
                            &cfg.sat_config,
                            cfg.conj_xy_product,
                        )
                        .unwrap()
                    });
                    let candidate = CandidateZW { zw_autocorr: zw };
                    let z_seq_clone = z_seq.clone();
                    let w_seq_clone = w_seq.clone();
                    if let Some(mut state) =
                        SolveXyPerCandidate::new(problem, &candidate, template, k)
                    {
                        if problem.n > 30 {
                            state.solver.set_conflict_limit(5000);
                        }
                        walk_xy_sub_mdd(
                            xy_root,
                            0,
                            ctx.xy_zw_depth,
                            0,
                            0,
                            &ctx.xy_pos_order,
                            &ctx.mdd.nodes,
                            ctx.max_bnd_sum,
                            ctx.middle_n as i32,
                            std::slice::from_ref(&tuple),
                            &mut |x_bits, y_bits| {
                                if found.load(Ordering::Relaxed) {
                                    return;
                                }
                                let (result, _stats) = state.try_candidate(x_bits, y_bits);
                                if let XyTryResult::Sat(x, y) = result {
                                    if verify_tt(
                                        problem,
                                        &x,
                                        &y,
                                        &z_seq_clone,
                                        &w_seq_clone,
                                    ) {
                                        found.store(true, Ordering::Relaxed);
                                        let _ = self.result_tx.send((
                                            x,
                                            y,
                                            z_seq_clone.clone(),
                                            w_seq_clone.clone(),
                                        ));
                                    }
                                }
                            },
                        );
                    }
                    !found.load(Ordering::Relaxed)
                },
            );
        }
        self.tuples_done
            .store(tuples.len(), Ordering::Relaxed);
        // Emit the full fraction at the end so the engine's
        // accumulated `MassSnapshot` matches what the mass model
        // now reports (`tuples_done / tuples_total == 1.0`). With
        // a single one-shot handler call we can't stream
        // intermediate progress via `mass_delta`; callers that
        // want per-tuple updates can poll `tuples_done`.
        let mut out = StageOutcome::default();
        out.mass_delta = crate::search_framework::mass::MassDelta {
            covered_exact: crate::search_framework::mass::MassValue(1.0),
            covered_partial: crate::search_framework::mass::MassValue::ZERO,
        };
        out
    }
}

pub struct CrossMassModel {
    tuples_done: Arc<AtomicUsize>,
    tuples_total: usize,
}

impl SearchMassModel for CrossMassModel {
    fn covered_mass(&self) -> MassValue {
        if self.tuples_total == 0 {
            MassValue::ZERO
        } else {
            let done = self.tuples_done.load(Ordering::Relaxed).min(self.tuples_total);
            MassValue(done as f64 / self.tuples_total as f64)
        }
    }
    fn quality(&self) -> CoverageQuality {
        CoverageQuality::Direct
    }
}

pub struct CrossAdapter {
    pub problem: Problem,
    pub tuples: Vec<SumTuple>,
    pub cfg: Arc<SearchConfig>,
    pub verbose: bool,
    pub k: usize,
    pub tuples_done: Arc<AtomicUsize>,
    pub found: Arc<AtomicBool>,
    pub result_tx: std::sync::mpsc::Sender<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>,
}

impl CrossAdapter {
    pub fn build(
        problem: Problem,
        tuples: Vec<SumTuple>,
        cfg: SearchConfig,
        verbose: bool,
        k: usize,
    ) -> (
        Self,
        std::sync::mpsc::Receiver<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>,
    ) {
        let (result_tx, result_rx) = std::sync::mpsc::channel();
        let tuples_done = Arc::new(AtomicUsize::new(0));
        let found = Arc::new(AtomicBool::new(false));
        (
            CrossAdapter {
                problem,
                tuples,
                cfg: Arc::new(cfg),
                verbose,
                k,
                tuples_done,
                found,
                result_tx,
            },
            result_rx,
        )
    }
}

impl SearchModeAdapter<CrossPayload> for CrossAdapter {
    fn name(&self) -> &'static str {
        "cross"
    }
    fn init(&self) -> AdapterInit<CrossPayload> {
        AdapterInit {
            seed_items: vec![WorkItem {
                stage_id: STAGE_CROSS,
                priority: 0,
                cost_hint: 1,
                replay_key: 0,
                mass_hint: Some(1.0),
                meta: WorkItemMeta {
                    item_id: 0,
                    parent_item_id: None,
                    fanout_root_id: 0,
                    depth_from_root: 0,
                    spawn_seq: 0,
                },
                payload: CrossPayload,
            }],
        }
    }
    fn stages(&self) -> BTreeMap<StageId, Box<dyn StageHandler<CrossPayload>>> {
        let mut m: BTreeMap<StageId, Box<dyn StageHandler<CrossPayload>>> = BTreeMap::new();
        m.insert(
            STAGE_CROSS,
            Box::new(CrossEnumerateStage {
                problem: self.problem,
                cfg: Arc::clone(&self.cfg),
                tuples: self.tuples.clone(),
                verbose: self.verbose,
                k: self.k,
                tuples_done: Arc::clone(&self.tuples_done),
                found: Arc::clone(&self.found),
                result_tx: self.result_tx.clone(),
            }),
        );
        m
    }
    fn mass_model(&self) -> Box<dyn SearchMassModel> {
        Box::new(CrossMassModel {
            tuples_done: Arc::clone(&self.tuples_done),
            tuples_total: self.tuples.len(),
        })
    }
}
