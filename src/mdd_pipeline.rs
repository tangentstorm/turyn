//! Unified 4-stage MDD pipeline driver + supporting work items and navigation.

#![allow(unused_imports)]

use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::sync::atomic::{AtomicBool, Ordering as AtomicOrdering};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use rustfft::num_complex::Complex;

use turyn::mdd_bfs;
use turyn::mdd_reorder;
use turyn::mdd_zw_first;
use turyn::sat_z_middle;

use crate::SPECTRAL_FREQS;
use crate::config::*;
use crate::enumerate::*;
use crate::legacy_search::*;
use crate::spectrum::*;
use crate::stochastic::*;
use crate::types::*;
use crate::xy_sat::*;

/// Produce a `(decision_level, PropKind as u8, count)` list for the
/// forced literals attributable to `solver` since `baseline` was
/// snapshotted. `baseline` is typically `solver.propagations_by_kind_level().to_vec()`
/// captured before the stage ran its solve loop.
///
/// For freshly-constructed solvers whose entire lifetime is within
/// one stage call, pass an empty baseline (`&[]`) so the full
/// `prop_by_kind_level` snapshot is reported as this call's
/// attribution — matches the spec's "cause == this stage's own
/// action" rule (`docs/TELEMETRY.md` §4 attribution rule) because
/// the fresh solver has no prior history.
pub(crate) fn forcing_delta_triples(
    solver: &radical::Solver,
    baseline: &[[u64; radical::PropKind::COUNT]],
) -> Vec<(u16, u8, u32)> {
    let after = solver.propagations_by_kind_level();
    let mut out: Vec<(u16, u8, u32)> = Vec::new();
    for (lvl, after_row) in after.iter().enumerate() {
        let zeros = [0u64; radical::PropKind::COUNT];
        let before_row = baseline.get(lvl).unwrap_or(&zeros);
        for kind in 0..radical::PropKind::COUNT {
            let d = after_row[kind].saturating_sub(before_row[kind]);
            if d > 0 {
                // `count` is a u32 on the wire. Cap at u32::MAX in
                // the astronomically-unlikely event the solver
                // forced > 4B literals at the same (level, kind);
                // saturating keeps the ordering invariant.
                out.push((lvl as u16, kind as u8, d.min(u32::MAX as u64) as u32));
            }
        }
    }
    out
}

pub(crate) fn compute_zw_autocorr(problem: Problem, z: &PackedSeq, w: &PackedSeq) -> Vec<i32> {
    let mut zw = vec![0i32; problem.n];
    for s in 1..problem.n {
        let nz = z.autocorrelation(s);
        let nw = if s < problem.m() {
            w.autocorrelation(s)
        } else {
            0
        };
        zw[s] = 2 * nz + 2 * nw;
    }
    zw
}

/// `--conj-zw-bound` filter: at lag `s = n - diff` for `diff in 1..=3`
/// (only while `k >= diff`), check the tightness conjecture
/// `|N_Z(s) + N_W(s)| = ((n - s) + N_U(s)) / 2` where
/// `u_i = x_i y_i`.  All positions involved live at the boundary, so
/// the check is O(1) given the fully-decoded `z_seq`, `w_seq` and the
/// `x_bits`/`y_bits` packing used by `walk_xy_sub_mdd` (prefix bits at
/// 0..k, suffix bits at k..2k, i.e., position `n-k+i`).  Returns true
/// iff every applicable lag satisfies equality.
///
/// Empirical note (n ∈ {18, 26}): at `s = n - 1, n - 2` the equality is
/// provably forced by Turyn at that lag combined with BDKR rules (i)
/// and (vi) plus the top-lag identity, so the check rejects nothing
/// in practice; the real conjectural content lives at `s = n - 3` and
/// the aggressive `s ∈ {n-4, n-5}` regime (not yet wired).  Filter is
/// retained for correctness and for future aggressive-lag extensions.
pub(crate) fn check_conj_zw_bound(
    n: usize,
    k: usize,
    x_bits: u32,
    y_bits: u32,
    z_seq: &PackedSeq,
    w_seq: &PackedSeq,
) -> bool {
    let m = n - 1;
    let boundary_val = |bits: u32, pos: usize| -> i32 {
        let bit_idx = if pos < k { pos } else { k + (pos - (n - k)) };
        if (bits >> bit_idx) & 1 == 1 { 1 } else { -1 }
    };
    let u_at = |pos: usize| -> i32 { boundary_val(x_bits, pos) * boundary_val(y_bits, pos) };

    for diff in 1..=3usize {
        if k < diff {
            break;
        }
        let s = n - diff;
        let nz = z_seq.autocorrelation(s);
        let nw = if s < m { w_seq.autocorrelation(s) } else { 0 };
        let lhs = nz + nw;

        // Sum u_i * u_{i+s} for i in 0..=(n-1-s) = 0..diff.  Both
        // endpoints sit at the boundary: i ∈ [0, k), i+s ∈ [n-k, n).
        let mut nu: i32 = 0;
        for i in 0..diff {
            nu += u_at(i) * u_at(i + s);
        }

        let rhs_twice = diff as i32 + nu;
        // `rhs` is a count of matching-U pairs, guaranteed non-negative
        // and same parity as `diff` (odd+odd or even+even).  A mismatch
        // here means the candidate violates the conjecture.
        if rhs_twice < 0 || rhs_twice % 2 != 0 {
            return false;
        }
        if lhs.abs() != rhs_twice / 2 {
            return false;
        }
    }
    true
}

/// Generic 4-way MDD walker. Walks from `nid` at `level` down to `depth`,
/// accumulating two bit-packed values (a_acc, b_acc) for branches (low bit, high bit).
/// Calls `emit(a_acc, b_acc, terminal_nid)` at terminal depth.
/// When a LEAF sentinel is reached before depth, enumerates all remaining branches.
pub(crate) fn walk_mdd_4way(
    nid: u32,
    level: usize,
    depth: usize,
    a_acc: u32,
    b_acc: u32,
    pos_order: &[usize],
    nodes: &[[u32; 4]],
    emit: &mut impl FnMut(u32, u32, u32),
) {
    if nid == mdd_reorder::DEAD {
        return;
    }
    if level == depth {
        emit(a_acc, b_acc, nid);
        return;
    }
    if nid == mdd_reorder::LEAF {
        walk_mdd_4way_leaf(level, depth, a_acc, b_acc, pos_order, emit);
        return;
    }
    let pos = pos_order[level];
    for branch in 0u32..4 {
        let child = nodes[nid as usize][branch as usize];
        if child == mdd_reorder::DEAD {
            continue;
        }
        let a_val = (branch >> 0) & 1;
        let b_val = (branch >> 1) & 1;
        walk_mdd_4way(
            child,
            level + 1,
            depth,
            a_acc | (a_val << pos),
            b_acc | (b_val << pos),
            pos_order,
            nodes,
            emit,
        );
    }
}

pub(crate) fn walk_mdd_4way_leaf(
    level: usize,
    depth: usize,
    a_acc: u32,
    b_acc: u32,
    pos_order: &[usize],
    emit: &mut impl FnMut(u32, u32, u32),
) {
    if level == depth {
        emit(a_acc, b_acc, mdd_reorder::LEAF);
        return;
    }
    let pos = pos_order[level];
    for branch in 0u32..4 {
        let a_val = (branch >> 0) & 1;
        let b_val = (branch >> 1) & 1;
        walk_mdd_4way_leaf(
            level + 1,
            depth,
            a_acc | (a_val << pos),
            b_acc | (b_val << pos),
            pos_order,
            emit,
        );
    }
}

/// Try to load the best available MDD file, scanning from max_k down to 1.
pub(crate) fn load_best_mdd(max_k: usize, verbose: bool) -> Option<mdd_reorder::Mdd4> {
    for try_k in (1..=max_k).rev() {
        let path = format!("mdd-{}.bin", try_k);
        if let Some(m) = mdd_reorder::Mdd4::load(&path) {
            if verbose {
                let live = m.count_live_paths();
                let total = 4.0f64.powi(m.depth as i32);
                let live_frac = live / total;
                // Print the live fraction with enough precision to distinguish
                // "0.00001% live" (typical for k=7 n=26) from "literally zero".
                // The "100% pruned" framing rounds away the only interesting
                // digits at this scale.
                eprintln!(
                    "Loaded MDD from {} (k={}, {} nodes, {:.1} MB, {:.2e} live / {:.2e} total paths, {:.2e} live fraction)",
                    path,
                    m.k,
                    m.nodes.len(),
                    m.nodes.len() as f64 * 16.0 / 1_048_576.0,
                    live,
                    total,
                    live_frac
                );
            }
            return Some(m);
        }
    }
    None
}

/// Items the five stage helpers (`process_boundary`,
/// `process_solve_w`, `process_solve_wz`, `process_solve_z`,
/// `process_solve_xy`) emit as follow-up work. The framework
/// `MddStagesAdapter` wraps these into its own `MddPayload` and
/// pushes them back onto `SearchEngine`'s scheduler.
///
/// The Boundary / SolveXY / Shutdown variants the legacy worker
/// loop used were trimmed with the legacy removal: nothing
/// constructs them anymore. The adapter delivers Boundary items
/// via its `MddPayload::Boundary` seed; SolveXY items are pushed
/// by `process_solve_z` only via the `MddPayload::SolveXY`
/// wrapper, not via `PipelineWork::SolveXY`.
pub(crate) enum PipelineWork {
    /// Stage 1: SAT-solve W given boundary + tuple.
    SolveW(SolveWWork),
    /// Stage 1 (alt): SAT-solve W+Z simultaneously in one call.
    SolveWZ(SolveWZWork),
    /// Stage 2: SAT-solve Z given boundary + W.
    SolveZ(SolveZWork),
}

#[derive(Clone)]
pub(crate) struct XyRuntimeGraph {
    pub(crate) root: u32,
    pub(crate) nodes: Option<Arc<Vec<[u32; 4]>>>,
}

pub(crate) struct BoundaryWork {
    pub(crate) z_bits: u32,
    pub(crate) w_bits: u32,
    pub(crate) xy_graph: XyRuntimeGraph,
}

pub(crate) struct SolveWZWork {
    /// Representative tuple (for trace / cache keys).  The real candidate
    /// set is `candidate_tuples`.
    pub(crate) tuple: SumTuple,
    pub(crate) z_bits: u32,
    pub(crate) w_bits: u32,
    pub(crate) xy_graph: XyRuntimeGraph,
    /// All tuples this boundary is compatible with; the combined SAT
    /// sees `V_w` = union of ±|σ_W| counts and `V_z` = union of ±|σ_Z|
    /// counts across this list.
    pub(crate) candidate_tuples: Vec<SumTuple>,
    /// Re-enumeration attempt counter.  0 = initial.  Higher attempts
    /// use different RNG seeds (to pick different random phases) and
    /// larger conflict budgets, and sit at lower priority so fresh
    /// boundaries / first-attempt items run first (otherwise stuck
    /// boundaries would monopolise the workers and we'd never cover
    /// the space).
    pub(crate) attempt: u32,
    /// Blocking clauses for (W, Z) pairs already enumerated by earlier
    /// attempts on this boundary.  Persisting these across re-queues is
    /// what makes this a true "defer never cancel" search: every attempt
    /// picks up where the last left off, so eventually SAT proves
    /// `Some(false)` (no more (W, Z) pairs exist) for every boundary.
    /// Literals refer to the stable W[0..middle_m] / Z[0..middle_n]
    /// middle vars (numbered 1..=middle_m+middle_n), which have the
    /// same IDs in every freshly-built solver for this boundary.
    pub(crate) prior_blocks: Vec<Vec<i32>>,
}

pub(crate) struct SolveWWork {
    /// Representative tuple (for trace/cache keys).  Under the multi-tuple
    /// pipeline the *real* surviving tuple set is `candidate_tuples`.
    pub(crate) tuple: SumTuple,
    pub(crate) z_bits: u32,
    pub(crate) w_bits: u32,
    pub(crate) xy_graph: XyRuntimeGraph,
    /// All unsigned tuples this boundary is compatible with.  The W SAT
    /// is built with a `PbSetEq` over the union of their ±|σ_W| counts;
    /// each solved W middle decodes to a specific σ_W which narrows this
    /// list for the next stage (SolveZ).
    pub(crate) candidate_tuples: Vec<SumTuple>,
}

pub(crate) struct SolveZWork {
    pub(crate) tuple: SumTuple,
    pub(crate) z_bits: u32,
    pub(crate) w_bits: u32,
    pub(crate) w_vals: Vec<i8>,
    pub(crate) w_spectrum: Vec<f64>,
    pub(crate) xy_graph: XyRuntimeGraph,
    /// Tuples surviving the σ_W narrowing (|σ_W| of candidate matches
    /// the W the solver locked in).  The Z SAT is built with a
    /// `PbSetEq` over the union of their ±|σ_Z| counts.
    pub(crate) candidate_tuples: Vec<SumTuple>,
}

/// Read-only context shared across all workers (via Arc). Populated
/// once in `run_mdd_sat_search` before spawning workers and read-only
/// thereafter.
pub(crate) struct PhaseBContext {
    pub(crate) mdd: Arc<mdd_reorder::Mdd4>,
    pub(crate) xy_pos_order: Vec<usize>, // full pos_order for XY sub-MDD walk
    pub(crate) tuples: Vec<SumTuple>,
    pub(crate) w_tmpl: sat_z_middle::LagTemplate,
    pub(crate) z_tmpl: sat_z_middle::LagTemplate,
    pub(crate) problem: Problem,
    pub(crate) k: usize,
    pub(crate) zw_depth: usize, // full 2*k — matches the MDD's ZW half depth
    pub(crate) xy_zw_depth: usize, // full 2*k for XY sub-MDD walk
    pub(crate) middle_n: usize,
    pub(crate) middle_m: usize,
    pub(crate) max_bnd_sum: i32,
    pub(crate) max_z: usize,
    pub(crate) individual_bound: f64,
    pub(crate) pair_bound: f64,
    pub(crate) theta: usize,
    pub(crate) mdd_extend: usize,
    /// Optional XY product-law conjecture (`U_i = -U_{n+1-i}` for
    /// 2 <= i <= n-1, with U_i = x_i*y_i). Plumbed from
    /// cfg.conj_xy_product; only consulted by stages that build an
    /// XY SAT template. See conjectures/xy-product.md.
    pub(crate) conj_xy_product: bool,
    /// Optional ZW u-bound tightness conjecture: enforce
    /// `|N_Z(s)+N_W(s)| = ((n-s)+N_U(s))/2` at s in {n-1, n-2, n-3}.
    /// Plumbed from cfg.conj_zw_bound; applied as an XY-stage
    /// pre-filter per (x_bits, y_bits). See
    /// conjectures/zw-u-bound-tight.md.
    pub(crate) conj_zw_bound: bool,
    /// Benchmark mode: report solutions but do not let a SAT hit
    /// terminate producer loops. The engine will stop on its fixed
    /// covered-work target instead.
    pub(crate) continue_after_sat: bool,
    /// Prototype: replace the per-leaf walk_xy_sub_mdd fan-out with a
    /// single `try_candidate_via_mdd` call that uses radical's native
    /// `MddConstraint` propagator. Gated by env `XY_MDD=1`. Only the
    /// `--wz=apart` SolveZ stage is wired in this prototype.
    pub(crate) xy_mdd_mode: bool,
    pub(crate) structural_xy_runtime: bool,
    pub(crate) structural_xy_cache: Arc<Mutex<HashMap<u128, XyRuntimeGraph>>>,
    pub(crate) w_mid_vars: Vec<i32>,
    pub(crate) z_mid_vars: Vec<i32>,
    pub(crate) z_spectral_tables: Option<radical::SpectralTables>,
    pub(crate) w_spectral_tables: Option<radical::SpectralTables>,
    pub(crate) found: Arc<AtomicBool>,
    /// When `--outfix=...:X:Y` is supplied, restrict the XY sub-MDD
    /// walk to this single (x_bits, y_bits).  `None` means enumerate
    /// the whole sub-MDD normally.
    pub(crate) outfix_xy: Option<(u32, u32)>,
    /// Middle-position pins from `--outfix` (longer than k digits).
    /// Each `(middle_idx, ±1)` forces the corresponding SAT var in
    /// SolveWZ / SolveW / SolveZ / XY stages as a unit clause.  Empty
    /// when the outfix only covers the boundary.
    pub(crate) outfix_z_mid_pins: Vec<(usize, i8)>,
    pub(crate) outfix_w_mid_pins: Vec<(usize, i8)>,
    pub(crate) outfix_x_mid_pins: Vec<(usize, i8)>,
    pub(crate) outfix_y_mid_pins: Vec<(usize, i8)>,
}

/// Metric atomics shared across workers in the MDD pipeline. Also
/// passed as a bundle into the per-stage handler helpers
/// (`process_boundary` and friends) so that both the legacy worker
/// loop in `run_mdd_sat_search` and the framework `StageHandler`
/// adapters update the same counters. Each field is an `Arc` so it
/// can be cheaply cloned into each worker thread. `Clone` on
/// `PipelineMetrics` clones only the Arcs, so every handler
/// instance keeps pointing at the same underlying counters.
#[derive(Clone)]
pub(crate) struct PipelineMetrics {
    // Shared
    pub(crate) flow_bnd_sum_fail: Arc<std::sync::atomic::AtomicU64>,
    /// Per-stage enter counters, indexed 0..4 (Boundary/SolveW/SolveZ/SolveXY).
    pub(crate) stage_enter: Vec<Arc<std::sync::atomic::AtomicU64>>,
    pub(crate) stage_exit: Vec<Arc<std::sync::atomic::AtomicU64>>,
    /// Tracks how many Boundary items are pending in the queue or
    /// mid-processing; decremented when the Boundary stage starts.
    pub(crate) pending_boundaries: Arc<std::sync::atomic::AtomicU64>,

    // SolveW stage
    pub(crate) flow_w_unsat: Arc<std::sync::atomic::AtomicU64>,
    /// W-search exited via conflict-budget timeout rather than
    /// proving UNSAT. Distinguishes "no more W candidates exist"
    /// (UNSAT) from "ran out of budget, might be more" (TIMEOUT).
    /// Under TTC §4.1 only the UNSAT case strictly counts as
    /// "no residual work remains"; the TIMEOUT case is why the
    /// MDD adapter's quality label is `Hybrid` not `Direct`.
    pub(crate) flow_w_timeout: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_w_solutions: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_w_spec_fail: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_w_spec_pass: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_w_solves: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_w_decisions: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_w_propagations: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_w_root_forced: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_w_free_sum: Arc<std::sync::atomic::AtomicU64>,

    // SolveXY / cross-mode XY stage
    pub(crate) items_completed: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_z_prep_fail: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_xy_zw_bound_rej: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_xy_sat: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_xy_unsat: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_xy_timeout: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_xy_timeout_cov_micro: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_xy_solves: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_xy_decisions: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_xy_propagations: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_xy_root_forced: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_xy_free_sum: Arc<std::sync::atomic::AtomicU64>,

    // SolveZ stage
    pub(crate) flow_z_unsat: Arc<std::sync::atomic::AtomicU64>,
    /// Z-search exited via conflict-budget timeout. Same
    /// UNSAT-vs-TIMEOUT distinction as `flow_w_timeout`; also
    /// contributes to why MDD quality stays `Hybrid`.
    pub(crate) flow_z_timeout: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_z_solutions: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_z_spec_fail: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_z_pair_fail: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_z_solves: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_z_decisions: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_z_propagations: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_z_root_forced: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_z_free_sum: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) extensions_pruned: Arc<std::sync::atomic::AtomicU64>,

    // SolveWZ combined stage
    pub(crate) flow_wz_empty_v: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_wz_rule_viol: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_wz_sat_calls: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_wz_first_unsat: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_wz_solutions: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_wz_exhausted: Arc<std::sync::atomic::AtomicU64>,
    pub(crate) flow_wz_budget_hit: Arc<std::sync::atomic::AtomicU64>,
}

/// Per-worker scratch state for the SolveZ stage. Kept as a bundle
/// so `process_solve_z` takes one `&mut ZStageScratch` instead of
/// six individual mutable references.
pub(crate) struct ZStageScratch {
    pub(crate) z_bases: HashMap<i32, radical::Solver>,
    pub(crate) z_prep: sat_z_middle::ZBoundaryPrep,
    pub(crate) z_prep_z_bits: Option<u32>,
    pub(crate) z_re_boundary: Vec<f64>,
    pub(crate) z_im_boundary: Vec<f64>,
    pub(crate) z_spectrum_buf: Vec<f64>,
    pub(crate) ext_cache: HashMap<u128, bool>,
}

fn compute_zw_sums_for_boundary(k: usize, z_bits: u32, w_bits: u32) -> Vec<i8> {
    let mut zw_sums = vec![0i8; k];
    for j in 0..k {
        let mut sum = 0i32;
        for i in 0..k - j {
            let pos_a = i;
            let pos_b = k + i + j;
            let za = if (z_bits >> pos_a) & 1 == 1 { 1i32 } else { -1 };
            let zb = if (z_bits >> pos_b) & 1 == 1 { 1i32 } else { -1 };
            sum += 2 * za * zb;
        }
        if j < k - 1 {
            for i in 0..k - j - 1 {
                let pos_a = i;
                let pos_b = k + i + j + 1;
                let wa = if (w_bits >> pos_a) & 1 == 1 { 1i32 } else { -1 };
                let wb = if (w_bits >> pos_b) & 1 == 1 { 1i32 } else { -1 };
                sum += 2 * wa * wb;
            }
        }
        zw_sums[j] = sum as i8;
    }
    zw_sums
}

pub(crate) fn loaded_xy_graph(xy_root: u32) -> XyRuntimeGraph {
    XyRuntimeGraph {
        root: xy_root,
        nodes: None,
    }
}

pub(crate) fn resolve_xy_graph<'a>(
    xy_graph: &'a XyRuntimeGraph,
    fallback_nodes: &'a [[u32; 4]],
) -> (u32, &'a [[u32; 4]]) {
    match &xy_graph.nodes {
        Some(nodes) => (xy_graph.root, nodes.as_slice()),
        None => (xy_graph.root, fallback_nodes),
    }
}

pub(crate) fn xy_graph_for_boundary(
    ctx: &PhaseBContext,
    z_bits: u32,
    w_bits: u32,
    loaded_root: u32,
) -> XyRuntimeGraph {
    if !ctx.structural_xy_runtime {
        return loaded_xy_graph(loaded_root);
    }

    let zw_sums = compute_zw_sums_for_boundary(ctx.k, z_bits, w_bits);
    let key = mdd_zw_first::pack_sums(&zw_sums);
    let mut cache = ctx.structural_xy_cache.lock().unwrap();
    cache
        .entry(key)
        .or_insert_with(|| {
            let (nodes, root) = mdd_zw_first::build_xy_for_boundary(ctx.k, &zw_sums);
            XyRuntimeGraph {
                root,
                nodes: Some(Arc::new(nodes)),
            }
        })
        .clone()
}

/// Boundary (stage 0) handler body, callable from both the legacy
/// worker loop (`run_mdd_sat_search`) and the framework
/// `BoundaryStage` adapter. Returns the 0-or-1 follow-up
/// `PipelineWork` items the boundary expands into (either a
/// `SolveWZ` under `use_wz_mode=true` or a `SolveW`).
///
/// Side effects:
/// - decrements `metrics.pending_boundaries` on entry,
/// - increments `metrics.flow_bnd_sum_fail` for each dropped tuple,
/// - increments `metrics.stage_enter[1]` once if any tuple survives,
/// - increments `metrics.stage_exit[0]` on return (whether or not
///   anything was emitted).
pub(crate) fn process_boundary(
    bnd: BoundaryWork,
    ctx: &PhaseBContext,
    metrics: &PipelineMetrics,
    use_wz_mode: bool,
) -> Vec<PipelineWork> {
    let trace_bnd = bnd.z_bits == 43 && bnd.w_bits == 47;
    if trace_bnd {
        eprintln!(
            "TRACE: found target boundary z=43 w=47 xy_root={}",
            bnd.xy_graph.root
        );
    }
    // Boundary dequeued — the walker is free to push another.
    metrics
        .pending_boundaries
        .fetch_sub(1, AtomicOrdering::Relaxed);

    let xy_graph = xy_graph_for_boundary(ctx, bnd.z_bits, bnd.w_bits, bnd.xy_graph.root);
    let z_bnd_sum = 2 * (bnd.z_bits.count_ones() as i32) - ctx.max_bnd_sum;
    let w_bnd_sum = 2 * (bnd.w_bits.count_ones() as i32) - ctx.max_bnd_sum;
    let (xy_root, xy_nodes) = resolve_xy_graph(&xy_graph, &ctx.mdd.nodes);

    let mut candidate_tuples: Vec<SumTuple> = Vec::with_capacity(ctx.tuples.len());
    for &tuple in &ctx.tuples {
        // Both ±|σ_W|, ±|σ_Z| allowed — feasible if AT LEAST ONE sign
        // of each is in range and parity.
        let z_feas = [tuple.z.abs(), -tuple.z.abs()]
            .iter()
            .any(|&s| crate::spectrum::sigma_full_to_cnt(s, z_bnd_sum, ctx.middle_n).is_some());
        let w_feas = [tuple.w.abs(), -tuple.w.abs()]
            .iter()
            .any(|&s| crate::spectrum::sigma_full_to_cnt(s, w_bnd_sum, ctx.middle_m).is_some());
        if !z_feas || !w_feas {
            metrics
                .flow_bnd_sum_fail
                .fetch_add(1, AtomicOrdering::Relaxed);
            continue;
        }
        // MDD-guided fail-fast on XY sub-tree compatibility.
        if !crate::xy_sat::any_valid_xy(
            xy_root,
            0,
            ctx.xy_zw_depth,
            0,
            0,
            &ctx.xy_pos_order,
            xy_nodes,
            ctx.max_bnd_sum,
            ctx.middle_n as i32,
            tuple,
        ) {
            metrics
                .flow_bnd_sum_fail
                .fetch_add(1, AtomicOrdering::Relaxed);
            continue;
        }
        candidate_tuples.push(tuple);
    }
    if candidate_tuples.is_empty() {
        metrics.stage_exit[0].fetch_add(1, AtomicOrdering::Relaxed);
        return Vec::new();
    }
    // Use the first candidate as the representative for legacy fields
    // (z_mid_sum, w_mid_sum, tuple).
    let rep = candidate_tuples[0];
    metrics.stage_enter[1].fetch_add(1, AtomicOrdering::Relaxed);
    let work = if use_wz_mode {
        PipelineWork::SolveWZ(SolveWZWork {
            tuple: rep,
            z_bits: bnd.z_bits,
            w_bits: bnd.w_bits,
            xy_graph: xy_graph.clone(),
            candidate_tuples,
            attempt: 0,
            prior_blocks: Vec::new(),
        })
    } else {
        PipelineWork::SolveW(SolveWWork {
            tuple: rep,
            z_bits: bnd.z_bits,
            w_bits: bnd.w_bits,
            xy_graph: xy_graph.clone(),
            candidate_tuples,
        })
    };
    if trace_bnd {
        eprintln!("TRACE: emitting ONE SolveW for canonical TT(18) boundary");
    }
    metrics.stage_exit[0].fetch_add(1, AtomicOrdering::Relaxed);
    vec![work]
}

/// SolveW (stage 1) handler body, callable from both the legacy
/// worker loop (`run_mdd_sat_search`) and the framework
/// `SolveWStage` adapter. Returns the `SolveZ` follow-up items
/// produced by enumerating W middles that pass the spectral filter.
///
/// Per-worker scratch is passed in as `&mut`: `spectral_w` and
/// `fft_buf_w` back the FFT spectral check, and `rng` is the
/// worker's xorshift state (also advanced here so the branching
/// phase decisions differ across retries). The `_w_bases` slot is
/// retained for API/storage compatibility with the legacy layout
/// but is no longer read or written — see the fresh-per-call
/// comment at the SAT-branch solver construction for why.
///
/// Side effects on `metrics`:
/// - `flow_w_solutions` +1 per solver hit,
/// - `flow_w_spec_fail` / `flow_w_spec_pass` +1 per FFT verdict,
/// - `flow_w_unsat` +1 if no W passed at all AND the exit was
///   clean (not via conflict-budget timeout); timeout exits are
///   exclusively counted in `flow_w_timeout`,
/// - `flow_w_timeout` +1 per SAT conflict-budget timeout exit,
/// - `flow_w_solves`, `flow_w_decisions`, `flow_w_propagations`,
///   `flow_w_root_forced`, `flow_w_free_sum` aggregated over the
///   SAT path,
/// - `stage_enter[2]` +1 per emitted SolveZ,
/// - `stage_exit[1]` +1 on return.
pub(crate) fn process_solve_w(
    sw: SolveWWork,
    ctx: &PhaseBContext,
    metrics: &PipelineMetrics,
    _w_bases: &mut HashMap<i32, radical::Solver>,
    spectral_w: &SpectralFilter,
    fft_buf_w: &mut FftScratch,
    rng: &mut u64,
    forcings_out: &mut Vec<(u16, u8, u32)>,
    // Set to true if the SAT W-enumeration exited via conflict-
    // budget timeout (residual W candidates MAY exist). The caller
    // marks the boundary abandoned on true so it's never
    // exact-credited (TTC §4.1).
    timed_out: &mut bool,
) -> Vec<PipelineWork> {
    let k = ctx.k;
    let m = ctx.problem.m();
    let trace_w = sw.z_bits == 43 && sw.w_bits == 47 && sw.tuple.z == 8 && sw.tuple.w == 1;
    if trace_w {
        eprintln!("TRACE: SolveW for target boundary, |σ_W|={}", sw.tuple.w);
    }
    let (w_prefix, w_suffix) = expand_boundary_bits(sw.w_bits, k);
    let mut w_boundary = vec![0i8; m];
    w_boundary[..k].copy_from_slice(&w_prefix);
    w_boundary[m - k..].copy_from_slice(&w_suffix);

    // BDKR rule (v) boundary pre-filter. Skip this SolveW if the W
    // boundary already fails rule (v). Legacy `continue` skipped
    // the stage_exit[1] bump; preserved here for exact parity.
    let rule_v_state = sat_z_middle::check_w_boundary_rule_v(m, k, &w_boundary);
    if rule_v_state == sat_z_middle::BoundaryRuleState::ViolatedAtBoundary {
        return Vec::new();
    }

    // Compute V_w = union over `sw.candidate_tuples` of
    // {cnt(+|σ_W|), cnt(-|σ_W|)}. One SAT call per boundary finds
    // any W middle landing on any valid σ_W — the decoded count
    // then narrows the tuple list for SolveZ.
    let w_bnd_sum_local: i32 = w_boundary.iter().map(|&v| v as i32).sum();
    let w_counts: Vec<u32> = {
        let mut cs: Vec<u32> = Vec::new();
        for t in &sw.candidate_tuples {
            let abs_w = t.w.abs();
            let signs: &[i32] = if abs_w == 0 { &[0] } else { &[1, -1] };
            for &sg in signs {
                if let Some(c) =
                    crate::spectrum::sigma_full_to_cnt(sg * abs_w, w_bnd_sum_local, ctx.middle_m)
                {
                    if !cs.contains(&c) {
                        cs.push(c);
                    }
                }
            }
        }
        cs.sort_unstable();
        cs
    };
    if w_counts.is_empty() {
        metrics.stage_exit[1].fetch_add(1, AtomicOrdering::Relaxed);
        return Vec::new();
    }

    // For small middle: brute-force W enumeration (proven to find
    // solutions). For large middle: SAT-based W generation.
    let mut w_found_any = false;
    let mut trace_w_total = 0u64;
    let mut trace_w_pass = 0u64;
    let mut out_batch: Vec<PipelineWork> = Vec::new();
    if ctx.middle_m <= 20 {
        let mut spec_buf: Vec<f64> = Vec::new();
        for &cnt in &w_counts {
            let mid_sum_iter = 2 * cnt as i32 - ctx.middle_m as i32;
            crate::enumerate::generate_sequences_permuted(
                ctx.middle_m,
                mid_sum_iter,
                false,
                false,
                200_000,
                |w_mid| {
                    if !ctx.continue_after_sat && ctx.found.load(AtomicOrdering::Relaxed) {
                        return false;
                    }
                    if !ctx.outfix_w_mid_pins.is_empty() {
                        let pin_ok = ctx
                            .outfix_w_mid_pins
                            .iter()
                            .all(|&(mid, val)| mid >= ctx.middle_m || w_mid[mid] == val);
                        if !pin_ok {
                            return true;
                        }
                    }
                    let mut w_vals = w_boundary.clone();
                    w_vals[k..k + ctx.middle_m].copy_from_slice(w_mid);
                    metrics
                        .flow_w_solutions
                        .fetch_add(1, AtomicOrdering::Relaxed);
                    if trace_w {
                        trace_w_total += 1;
                    }
                    if sat_z_middle::check_w_boundary_rule_v(m, m, &w_vals)
                        == sat_z_middle::BoundaryRuleState::ViolatedAtBoundary
                    {
                        return true;
                    }
                    if crate::spectrum::spectrum_into_if_ok(
                        &w_vals,
                        spectral_w,
                        ctx.individual_bound,
                        fft_buf_w,
                        &mut spec_buf,
                    ) {
                        if trace_w {
                            trace_w_pass += 1;
                        }
                        metrics
                            .flow_w_spec_pass
                            .fetch_add(1, AtomicOrdering::Relaxed);
                        w_found_any = true;
                        let sigma_w_full: i32 = w_vals.iter().map(|&v| v as i32).sum();
                        let narrowed: Vec<SumTuple> = sw
                            .candidate_tuples
                            .iter()
                            .copied()
                            .filter(|t| t.w.abs() == sigma_w_full.abs())
                            .collect();
                        if narrowed.is_empty() {
                            return true;
                        }
                        metrics.stage_enter[2].fetch_add(1, AtomicOrdering::Relaxed);
                        let rep = narrowed[0];
                        out_batch.push(PipelineWork::SolveZ(SolveZWork {
                            tuple: rep,
                            z_bits: sw.z_bits,
                            w_bits: sw.w_bits,
                            w_vals,
                            w_spectrum: spec_buf.clone(),
                            xy_graph: sw.xy_graph.clone(),
                            candidate_tuples: narrowed,
                        }));
                    } else {
                        metrics
                            .flow_w_spec_fail
                            .fetch_add(1, AtomicOrdering::Relaxed);
                    }
                    true
                },
            );
        }
    } else {
        // SAT-based W generation. Always build a fresh solver per
        // call — the earlier `w_bases` cache keyed everything on
        // `0i32`, which meant boundary A's cached solver (with a
        // `PbSetEq` constraint encoding A's `w_counts`) was reused
        // for boundary B whose `w_counts` may differ. B's search
        // would then be constrained by A's counts and miss
        // solutions. Mirrors the same fresh-per-call policy
        // `process_solve_z` adopted after the same class of bug.
        // TTC §4.1 / §2: the denominator and numerator must refer
        // to the same search space — a stale cached solver
        // changes the effective search space silently.
        let mut w_solver = ctx.w_tmpl.build_base_solver_pb_set(ctx.middle_m, &w_counts);
        let w_cp = w_solver.save_checkpoint();
        sat_z_middle::fill_w_solver(&mut w_solver, &ctx.w_tmpl, m, &w_boundary);
        if rule_v_state == sat_z_middle::BoundaryRuleState::DeferredToMiddle {
            let mut nv = (w_solver.num_vars() + 1) as i32;
            sat_z_middle::add_rule_v_middle_clauses(
                &mut w_solver,
                m,
                k,
                &w_boundary,
                |pf| (pf - k + 1) as i32,
                &mut nv,
            );
        }
        if let Some(ref wtab) = ctx.w_spectral_tables {
            w_solver.spectral = Some(radical::SpectralConstraint::from_tables(
                wtab,
                &w_boundary,
                ctx.individual_bound,
            ));
        }

        for &(mid, val) in &ctx.outfix_w_mid_pins {
            if mid < ctx.middle_m {
                let lit = (mid + 1) as i32;
                w_solver.add_clause([if val > 0 { lit } else { -lit }]);
            }
        }

        let w_d0 = w_solver.num_decisions();
        let w_p0 = w_solver.num_propagations();
        let w_l0 = w_solver.num_level0_vars();
        let w_nv = w_solver.num_vars();
        // Baseline for forcing attribution. `w_solver` is now
        // freshly built per call (the prior `w_bases` cache was
        // unsafe across boundaries — see the comment at
        // construction), so an empty baseline would be equivalent.
        // Keep the snapshot to preserve semantics if the solver is
        // ever built with pre-loaded blocks from a prior attempt.
        let w_plk0: Vec<[u64; radical::PropKind::COUNT]> =
            w_solver.propagations_by_kind_level().to_vec();

        let max_w_per_boundary: usize = std::env::var("TURYN_MAX_W_PER_BND")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(128);
        let w_conflict_budget: u64 = std::env::var("TURYN_W_CONFL")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(5000);
        let mut w_iter_count: usize = 0;
        loop {
            if !ctx.continue_after_sat && ctx.found.load(AtomicOrdering::Relaxed) {
                break;
            }
            if w_iter_count >= max_w_per_boundary {
                break;
            }
            w_iter_count += 1;
            let phases: Vec<bool> = (0..ctx.middle_m)
                .map(|_| {
                    *rng ^= *rng << 13;
                    *rng ^= *rng >> 7;
                    *rng ^= *rng << 17;
                    *rng & 1 == 1
                })
                .collect();
            w_solver.set_phase(&phases);
            if w_conflict_budget > 0 {
                w_solver.set_conflict_budget(w_conflict_budget);
            }
            match w_solver.solve() {
                Some(true) => {}
                Some(false) => {
                    // Genuinely UNSAT — no more W candidates
                    // exist for this boundary. Safe closure.
                    break;
                }
                None => {
                    // Conflict budget exhausted. Residual W
                    // candidates MAY exist. Per TTC §4.1 the
                    // boundary MUST NOT be exact-credited — the
                    // caller reads `*timed_out` and routes the
                    // boundary through `mark_abandoned` so it
                    // retains its accumulated partial credit but
                    // never bumps exact.
                    metrics.flow_w_timeout.fetch_add(1, AtomicOrdering::Relaxed);
                    *timed_out = true;
                    break;
                }
            }
            metrics
                .flow_w_solutions
                .fetch_add(1, AtomicOrdering::Relaxed);

            let w_mid = extract_vals(&w_solver, |i| ctx.w_mid_vars[i], ctx.middle_m);
            let mut w_vals = w_boundary.clone();
            w_vals[k..k + ctx.middle_m].copy_from_slice(&w_mid);

            let w_block: Vec<i32> = ctx
                .w_mid_vars
                .iter()
                .map(|&v| {
                    if w_solver.value(v) == Some(true) {
                        -v
                    } else {
                        v
                    }
                })
                .collect();
            w_solver.reset();
            w_solver.add_clause(w_block);

            let w_spectrum = match crate::spectrum::spectrum_if_ok(
                &w_vals,
                spectral_w,
                ctx.individual_bound,
                fft_buf_w,
            ) {
                Some(s) => s,
                None => {
                    metrics
                        .flow_w_spec_fail
                        .fetch_add(1, AtomicOrdering::Relaxed);
                    continue;
                }
            };
            metrics
                .flow_w_spec_pass
                .fetch_add(1, AtomicOrdering::Relaxed);
            w_found_any = true;

            let sigma_w_full: i32 = w_vals.iter().map(|&v| v as i32).sum();
            let narrowed: Vec<SumTuple> = sw
                .candidate_tuples
                .iter()
                .copied()
                .filter(|t| t.w.abs() == sigma_w_full.abs())
                .collect();
            if narrowed.is_empty() {
                continue;
            }
            metrics.stage_enter[2].fetch_add(1, AtomicOrdering::Relaxed);
            let rep = narrowed[0];
            out_batch.push(PipelineWork::SolveZ(SolveZWork {
                tuple: rep,
                z_bits: sw.z_bits,
                w_bits: sw.w_bits,
                w_vals,
                w_spectrum,
                xy_graph: sw.xy_graph.clone(),
                candidate_tuples: narrowed,
            }));
        }

        let w_decisions = w_solver.num_decisions().saturating_sub(w_d0);
        let w_propagations = w_solver.num_propagations().saturating_sub(w_p0);
        let w_pre_forced = w_l0 as u64;
        let w_free_vars = w_nv.saturating_sub(w_l0) as u64;
        metrics.flow_w_solves.fetch_add(1, AtomicOrdering::Relaxed);
        metrics
            .flow_w_decisions
            .fetch_add(w_decisions, AtomicOrdering::Relaxed);
        metrics
            .flow_w_propagations
            .fetch_add(w_propagations, AtomicOrdering::Relaxed);
        metrics
            .flow_w_root_forced
            .fetch_add(w_pre_forced, AtomicOrdering::Relaxed);
        metrics
            .flow_w_free_sum
            .fetch_add(w_free_vars, AtomicOrdering::Relaxed);
        forcings_out.extend(forcing_delta_triples(&w_solver, &w_plk0));

        // Fresh-per-call policy: `w_solver` is dropped at scope
        // exit (end of this `else` block). `w_cp` was taken above
        // to keep the legacy checkpoint/restore flow available if
        // caching is ever re-enabled; today it simply dies with
        // the solver.
        let _w_cp = w_cp;
        w_solver.spectral = None;
    }
    // Only attribute `flow_w_unsat` to runs where the W enumeration
    // terminated cleanly without finding any candidate. If we
    // exited via conflict-budget timeout (`*timed_out`), bumping
    // this counter would double-attribute the same exit as both
    // "unsat" and "timeout" in the diagnostic summary — the
    // boundary is genuinely incomplete, not proven empty.
    if !w_found_any && !*timed_out {
        metrics.flow_w_unsat.fetch_add(1, AtomicOrdering::Relaxed);
    }
    if trace_w {
        eprintln!(
            "TRACE: SolveW done: {} W middles checked, {} passed spectral",
            trace_w_total, trace_w_pass
        );
    }
    metrics.stage_exit[1].fetch_add(1, AtomicOrdering::Relaxed);
    out_batch
}

/// SolveZ (stage 2) handler body. Enumerates Z middles under the
/// spectral pair bound and the BDKR rule (iv) filter, then drives
/// the shared XY fast path for each surviving `(Z, W)` pair —
/// either via `try_candidate_via_mdd` (when `ctx.xy_mdd_mode`) or
/// the per-leaf `walk_xy_sub_mdd` loop with `SolveXyPerCandidate`.
///
/// Per-worker scratch is bundled in `ZStageScratch`. Cross-stage
/// scratch (`template_cache`, `warm`) and IO (`result_tx`,
/// `sat_config`, `rng`) are passed separately since they're shared
/// with SolveXY.
pub(crate) fn process_solve_z(
    sz: SolveZWork,
    ctx: &PhaseBContext,
    metrics: &PipelineMetrics,
    scratch: &mut ZStageScratch,
    spectral_z: &SpectralFilter,
    fft_buf_z: &mut FftScratch,
    template_cache: &mut HashMap<Vec<(i32, i32, i32, i32)>, SatXYTemplate>,
    warm: &mut WarmStartState,
    sat_config: &radical::SolverConfig,
    result_tx: &std::sync::mpsc::Sender<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>,
    rng: &mut u64,
    forcings_out: &mut Vec<(u16, u8, u32)>,
    // Per-call accumulator for XY-timeout `cover_micro` values.
    // A local u64 rather than snapshot-diff on the global
    // `flow_xy_timeout_cov_micro` atomic, which double-attributes
    // XY timeouts across concurrent handlers under
    // `worker_count > 1`.
    cov_micro_out: &mut u64,
    // Set to true if the SAT Z-enumeration exited via
    // conflict-budget timeout (residual Z candidates MAY exist).
    // Caller marks the boundary abandoned on true.
    timed_out: &mut bool,
) {
    let k = ctx.k;
    let n = ctx.problem.n;
    let m = ctx.problem.m();
    let trace_z = sz.z_bits == 43 && sz.w_bits == 47 && sz.tuple.z == 8;

    let mut z_boundary = vec![0i8; n];
    for i in 0..k {
        z_boundary[i] = if (sz.z_bits >> i) & 1 == 1 { 1 } else { -1 };
        z_boundary[n - k + i] = if (sz.z_bits >> (k + i)) & 1 == 1 {
            1
        } else {
            -1
        };
    }

    let rule_iv_state = sat_z_middle::check_z_boundary_rule_iv(n, k, &z_boundary);
    if rule_iv_state == sat_z_middle::BoundaryRuleState::ViolatedAtBoundary {
        return;
    }

    let z_bnd_sum_local: i32 = z_boundary.iter().map(|&v| v as i32).sum();
    let z_counts: Vec<u32> = {
        let mut cs: Vec<u32> = Vec::new();
        for t in &sz.candidate_tuples {
            let abs_z = t.z.abs();
            let signs: &[i32] = if abs_z == 0 { &[0] } else { &[1, -1] };
            for &sg in signs {
                if let Some(c) =
                    crate::spectrum::sigma_full_to_cnt(sg * abs_z, z_bnd_sum_local, ctx.middle_n)
                {
                    if !cs.contains(&c) {
                        cs.push(c);
                    }
                }
            }
        }
        cs.sort_unstable();
        cs
    };
    if z_counts.is_empty() {
        metrics.stage_exit[2].fetch_add(1, AtomicOrdering::Relaxed);
        return;
    }

    // Always build a fresh z_solver per call. The earlier
    // `scratch.z_bases` cache (keyed by a constant `0i32`) reused a
    // solver across calls via `save_checkpoint`/`restore_checkpoint`
    // — but that reuse silently produced spurious UNSATs at small
    // middle_n (e.g. n=4 middle_n=2), making the canonical TT(n)
    // unreachable in the framework path. `build_base_solver_quad_pb_pb_set`
    // is cheap; rebuilding each call trades a tiny per-call cost for
    // correctness.
    let mut z_solver = ctx
        .z_tmpl
        .build_base_solver_quad_pb_pb_set(ctx.middle_n, &z_counts);
    let z_cp = z_solver.save_checkpoint();
    if scratch.z_prep_z_bits != Some(sz.z_bits) {
        scratch
            .z_prep
            .rebuild(&ctx.z_tmpl, ctx.middle_n, &z_boundary);
        if let Some(ref ztab) = ctx.z_spectral_tables {
            let nf = ztab.num_freqs;
            scratch.z_re_boundary.iter_mut().for_each(|v| *v = 0.0);
            scratch.z_im_boundary.iter_mut().for_each(|v| *v = 0.0);
            for pos in 0..n {
                if pos >= k && pos < n - k {
                    continue;
                }
                let val = z_boundary[pos] as f64;
                let base = pos * nf;
                for fi in 0..nf {
                    scratch.z_re_boundary[fi] += val * ztab.pos_cos[base + fi];
                    scratch.z_im_boundary[fi] += val * ztab.pos_sin[base + fi];
                }
            }
        }
        scratch.z_prep_z_bits = Some(sz.z_bits);
    }
    if let Some(ref ztab) = ctx.z_spectral_tables {
        let num_freqs = ztab.num_freqs;
        let middle_len = ztab.middle_len;
        let mut z_spec = radical::SpectralConstraint {
            num_seq_vars: middle_len,
            cos_table: std::sync::Arc::clone(&ztab.cos_table),
            sin_table: std::sync::Arc::clone(&ztab.sin_table),
            num_freqs,
            re: scratch.z_re_boundary.clone(),
            im: scratch.z_im_boundary.clone(),
            re_boundary: scratch.z_re_boundary.clone(),
            im_boundary: scratch.z_im_boundary.clone(),
            bound: ctx.pair_bound,
            per_freq_bound: None,
            max_reduction: ztab.max_reduction_total.clone(),
            amplitudes: std::sync::Arc::clone(&ztab.amplitudes),
            assigned: vec![false; middle_len],
            values: vec![0i8; middle_len],
            seq2: None,
        };
        let nf = z_spec.num_freqs;
        let mut w_re = vec![0.0f64; nf];
        let mut w_im = vec![0.0f64; nf];
        for (j, &wv) in sz.w_vals.iter().enumerate() {
            let base = j * nf;
            let cos_slice = &ztab.pos_cos[base..base + nf];
            let sin_slice = &ztab.pos_sin[base..base + nf];
            if wv > 0 {
                for fi in 0..nf {
                    w_re[fi] += cos_slice[fi];
                    w_im[fi] += sin_slice[fi];
                }
            } else {
                for fi in 0..nf {
                    w_re[fi] -= cos_slice[fi];
                    w_im[fi] -= sin_slice[fi];
                }
            }
        }
        let mut pfb = vec![ctx.pair_bound; nf];
        for fi in 0..nf {
            pfb[fi] = (ctx.pair_bound - w_re[fi] * w_re[fi] - w_im[fi] * w_im[fi]).max(0.0);
        }
        z_spec.per_freq_bound = Some(pfb);
        z_solver.spectral = Some(z_spec);
    }

    sat_z_middle::fill_z_solver_quad_pb(
        &mut z_solver,
        &ctx.z_tmpl,
        n,
        m,
        ctx.middle_n,
        &scratch.z_prep,
        &sz.w_vals,
    );
    if rule_iv_state == sat_z_middle::BoundaryRuleState::DeferredToMiddle {
        let mut nv = (z_solver.num_vars() + 1) as i32;
        sat_z_middle::add_rule_iv_middle_clauses(
            &mut z_solver,
            n,
            k,
            |jf| (jf - k + 1) as i32,
            &mut nv,
        );
    }
    for &(mid, val) in &ctx.outfix_z_mid_pins {
        if mid < ctx.middle_n {
            let lit = ctx.z_mid_vars[mid];
            z_solver.add_clause([if val > 0 { lit } else { -lit }]);
        }
    }
    if z_solver.spectral.is_some() {
        let nsv = z_solver.spectral.as_ref().unwrap().num_seq_vars;
        let mut pending: Vec<(usize, i8)> = Vec::new();
        for vi in 0..nsv {
            let lit = ctx.z_mid_vars[vi];
            if let Some(b) = z_solver.value(lit) {
                let sp = z_solver.spectral.as_ref().unwrap();
                if !sp.assigned[vi] {
                    pending.push((vi, if b { 1 } else { -1 }));
                }
            }
        }
        if let Some(ref mut sp) = z_solver.spectral {
            for (vi, val) in pending {
                sp.assign(vi, val);
            }
        }
    }

    let w_seq = PackedSeq::from_values(&sz.w_vals);

    let z_d0 = z_solver.num_decisions();
    let z_p0 = z_solver.num_propagations();
    let z_l0 = z_solver.num_level0_vars();
    let z_nv = z_solver.num_vars();

    let mut z_count = 0usize;
    let z_conflict_budget: u64 = std::env::var("TURYN_Z_CONFL")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(5000);
    loop {
        if !ctx.continue_after_sat && ctx.found.load(AtomicOrdering::Relaxed) {
            break;
        }
        if z_count >= ctx.max_z {
            break;
        }
        let z_phases: Vec<bool> = (0..ctx.middle_n)
            .map(|_| {
                *rng ^= *rng << 13;
                *rng ^= *rng >> 7;
                *rng ^= *rng << 17;
                *rng & 1 == 1
            })
            .collect();
        z_solver.set_phase(&z_phases);
        if z_conflict_budget > 0 {
            z_solver.set_conflict_budget(z_conflict_budget);
        }
        let z_result = z_solver.solve();
        match z_result {
            Some(true) => {}
            Some(false) => {
                // UNSAT — no more Z candidates exist. Clean
                // boundary closure.
                if z_count == 0 {
                    metrics.flow_z_unsat.fetch_add(1, AtomicOrdering::Relaxed);
                }
                break;
            }
            None => {
                // Z-search hit its conflict budget. Residual Z
                // candidates MAY exist. Per TTC §4.1 the caller
                // marks the boundary abandoned so it retains its
                // accumulated partial credit but never bumps
                // exact.
                metrics.flow_z_timeout.fetch_add(1, AtomicOrdering::Relaxed);
                *timed_out = true;
                break;
            }
        }
        z_count += 1;
        metrics
            .flow_z_solutions
            .fetch_add(1, AtomicOrdering::Relaxed);

        let z_mid = extract_vals(&z_solver, |i| ctx.z_mid_vars[i], ctx.middle_n);

        let mut z_vals = Vec::with_capacity(n);
        z_vals.extend_from_slice(&z_boundary[..k]);
        z_vals.extend_from_slice(&z_mid);
        z_vals.extend_from_slice(&z_boundary[n - k..]);

        if z_count < ctx.max_z {
            let z_block: Vec<i32> = ctx
                .z_mid_vars
                .iter()
                .map(|&v| {
                    if z_solver.value(v) == Some(true) {
                        -v
                    } else {
                        v
                    }
                })
                .collect();
            z_solver.reset();
            z_solver.add_clause(z_block);
        }

        crate::spectrum::compute_spectrum_into(
            &z_vals,
            spectral_z,
            fft_buf_z,
            &mut scratch.z_spectrum_buf,
        );

        if ctx.middle_n <= 20 {
            if !crate::spectrum::spectral_pair_ok(
                &scratch.z_spectrum_buf,
                &sz.w_spectrum,
                ctx.pair_bound,
            ) {
                metrics
                    .flow_z_pair_fail
                    .fetch_add(1, AtomicOrdering::Relaxed);
                if trace_z {
                    eprintln!("TRACE:   Z solution #{} FAILED pair check", z_count);
                }
                continue;
            }
        }
        if trace_z {
            eprintln!("TRACE:   Z solution #{} REACHED XY!", z_count);
        }

        let z_seq = PackedSeq::from_values(&z_vals);
        let zw_autocorr = compute_zw_autocorr(ctx.problem, &z_seq, &w_seq);

        let mut tuple_key: Vec<(i32, i32, i32, i32)> = sz
            .candidate_tuples
            .iter()
            .map(|t| (t.x, t.y, t.z, t.w))
            .collect();
        tuple_key.sort_unstable();
        let template = template_cache.entry(tuple_key).or_insert_with(|| {
            SatXYTemplate::build_multi_opts(
                ctx.problem,
                &sz.candidate_tuples,
                sat_config,
                ctx.conj_xy_product,
            )
            .unwrap()
        });
        let candidate = CandidateZW { zw_autocorr };
        if ctx.xy_mdd_mode {
            let conflict_limit = if n > 30 { 5000 } else { 0 };
            let (xy_root, xy_nodes) = resolve_xy_graph(&sz.xy_graph, &ctx.mdd.nodes);
            let (xy_res, stats) = try_candidate_via_mdd(
                ctx.problem,
                &candidate,
                template,
                k,
                xy_root,
                xy_nodes,
                &ctx.xy_pos_order,
                conflict_limit,
                // Accumulate the fresh XY-MDD solver's forcing
                // triples into the stage's sink so the MDD
                // adapter's `StageOutcome::forcings` covers the
                // inline XY work, not just the outer z_solver.
                Some(forcings_out),
            );
            metrics.stage_enter[3].fetch_add(1, AtomicOrdering::Relaxed);
            metrics
                .items_completed
                .fetch_add(1, AtomicOrdering::Relaxed);
            metrics.stage_exit[3].fetch_add(1, AtomicOrdering::Relaxed);
            metrics.flow_xy_solves.fetch_add(1, AtomicOrdering::Relaxed);
            metrics
                .flow_xy_decisions
                .fetch_add(stats.decisions, AtomicOrdering::Relaxed);
            metrics
                .flow_xy_propagations
                .fetch_add(stats.propagations, AtomicOrdering::Relaxed);
            metrics
                .flow_xy_root_forced
                .fetch_add(stats.vars_pre_forced, AtomicOrdering::Relaxed);
            metrics
                .flow_xy_free_sum
                .fetch_add(stats.free_vars, AtomicOrdering::Relaxed);
            match xy_res {
                Some((x, y)) => {
                    metrics.flow_xy_sat.fetch_add(1, AtomicOrdering::Relaxed);
                    if verify_tt(ctx.problem, &x, &y, &z_seq, &w_seq) {
                        if !ctx.continue_after_sat {
                            ctx.found.store(true, AtomicOrdering::Relaxed);
                        }
                        let _ = result_tx.send((x, y, z_seq.clone(), w_seq.clone()));
                    }
                }
                None => {
                    metrics.flow_xy_unsat.fetch_add(1, AtomicOrdering::Relaxed);
                }
            }
        } else if let Some(mut state) =
            SolveXyPerCandidate::new(ctx.problem, &candidate, template, k)
        {
            if n > 30 {
                state.solver.set_conflict_limit(5000);
            }
            if warm.inject_phase {
                if let Some(ref ph) = warm.phase {
                    state.solver.set_phase(ph);
                }
            }

            // Snapshot the XY solver BEFORE the walk so only the
            // walk's contributions (many `try_candidate` calls,
            // each propagating on top of the previous trail) are
            // attributed. The solver already did some level-0
            // propagation at construction; those are part of the
            // stage's own setup work, so including them is OK,
            // but taking the snapshot now keeps it to the walk
            // proper — same contract as the outer z_solver.
            let xy_plk0: Vec<[u64; radical::PropKind::COUNT]> =
                state.solver.propagations_by_kind_level().to_vec();
            let (xy_root, xy_nodes) = resolve_xy_graph(&sz.xy_graph, &ctx.mdd.nodes);
            walk_xy_sub_mdd(
                xy_root,
                0,
                ctx.xy_zw_depth,
                0,
                0,
                &ctx.xy_pos_order,
                xy_nodes,
                ctx.max_bnd_sum,
                ctx.middle_n as i32,
                &sz.candidate_tuples,
                &mut |x_bits, y_bits| {
                    if !ctx.continue_after_sat && ctx.found.load(AtomicOrdering::Relaxed) {
                        return;
                    }
                    if let Some((fx, fy)) = ctx.outfix_xy {
                        if x_bits != fx || y_bits != fy {
                            return;
                        }
                    }
                    if ctx.conj_zw_bound
                        && !check_conj_zw_bound(n, k, x_bits, y_bits, &z_seq, &w_seq)
                    {
                        metrics
                            .flow_xy_zw_bound_rej
                            .fetch_add(1, AtomicOrdering::Relaxed);
                        return;
                    }
                    if ctx.mdd_extend > 0 {
                        let cache_key = (sz.z_bits as u128)
                            | ((sz.w_bits as u128) << 32)
                            | ((x_bits as u128) << 64)
                            | ((y_bits as u128) << 96);
                        let ext_ok = *scratch.ext_cache.entry(cache_key).or_insert_with(|| {
                            mdd_zw_first::has_extension(
                                k,
                                k + ctx.mdd_extend,
                                sz.z_bits,
                                sz.w_bits,
                                x_bits,
                                y_bits,
                            )
                        });
                        if !ext_ok {
                            metrics
                                .extensions_pruned
                                .fetch_add(1, AtomicOrdering::Relaxed);
                            return;
                        }
                    }
                    metrics.stage_enter[3].fetch_add(1, AtomicOrdering::Relaxed);
                    let (result, stats) = state.try_candidate(x_bits, y_bits);
                    metrics
                        .items_completed
                        .fetch_add(1, AtomicOrdering::Relaxed);
                    metrics.stage_exit[3].fetch_add(1, AtomicOrdering::Relaxed);
                    match &result {
                        XyTryResult::Sat(_, _) => {
                            metrics.flow_xy_sat.fetch_add(1, AtomicOrdering::Relaxed);
                        }
                        XyTryResult::Unsat | XyTryResult::Pruned => {
                            metrics.flow_xy_unsat.fetch_add(1, AtomicOrdering::Relaxed);
                        }
                        XyTryResult::Timeout => {
                            metrics
                                .flow_xy_timeout
                                .fetch_add(1, AtomicOrdering::Relaxed);
                            metrics
                                .flow_xy_timeout_cov_micro
                                .fetch_add(stats.cover_micro, AtomicOrdering::Relaxed);
                            *cov_micro_out = cov_micro_out.saturating_add(stats.cover_micro);
                        }
                    };
                    if !matches!(result, XyTryResult::Pruned) {
                        metrics.flow_xy_solves.fetch_add(1, AtomicOrdering::Relaxed);
                        metrics
                            .flow_xy_decisions
                            .fetch_add(stats.decisions, AtomicOrdering::Relaxed);
                        metrics
                            .flow_xy_propagations
                            .fetch_add(stats.propagations, AtomicOrdering::Relaxed);
                        metrics
                            .flow_xy_root_forced
                            .fetch_add(stats.vars_pre_forced, AtomicOrdering::Relaxed);
                        metrics
                            .flow_xy_free_sum
                            .fetch_add(stats.free_vars, AtomicOrdering::Relaxed);
                    }
                    if let XyTryResult::Sat(x, y) = result {
                        if verify_tt(ctx.problem, &x, &y, &z_seq, &w_seq) {
                            if !ctx.continue_after_sat {
                                ctx.found.store(true, AtomicOrdering::Relaxed);
                            }
                            let _ = result_tx.send((x, y, z_seq.clone(), w_seq.clone()));
                        }
                    }
                },
            );
            // Drain the XY solver's propagation delta into the
            // stage's forcing sink so `StageOutcome::forcings`
            // reflects the actual inline XY work, not just the
            // outer z_solver. See `docs/TELEMETRY.md` §4
            // attribution rule.
            forcings_out.extend(forcing_delta_triples(&state.solver, &xy_plk0));
            warm.phase = Some(state.solver.get_phase());
        } else {
            metrics
                .flow_z_prep_fail
                .fetch_add(1, AtomicOrdering::Relaxed);
        }
    }
    if trace_z {
        let z_sf = metrics.flow_z_spec_fail.load(AtomicOrdering::Relaxed);
        let z_pf = metrics.flow_z_pair_fail.load(AtomicOrdering::Relaxed);
        eprintln!(
            "TRACE: SolveZ done for target: {} Z found (global z_spec_fail={}, z_pair_fail={})",
            z_count, z_sf, z_pf
        );
    }

    let z_decisions = z_solver.num_decisions().saturating_sub(z_d0);
    let z_propagations = z_solver.num_propagations().saturating_sub(z_p0);
    let z_pre_forced = z_l0 as u64;
    let z_free_vars = z_nv.saturating_sub(z_l0) as u64;
    metrics.flow_z_solves.fetch_add(1, AtomicOrdering::Relaxed);
    metrics
        .flow_z_decisions
        .fetch_add(z_decisions, AtomicOrdering::Relaxed);
    metrics
        .flow_z_propagations
        .fetch_add(z_propagations, AtomicOrdering::Relaxed);
    metrics
        .flow_z_root_forced
        .fetch_add(z_pre_forced, AtomicOrdering::Relaxed);
    metrics
        .flow_z_free_sum
        .fetch_add(z_free_vars, AtomicOrdering::Relaxed);
    // `z_solver` is freshly built every call, so an empty baseline
    // reports the full forcing trace as attribution for this
    // SolveZ call. Inline XY-path solvers (SolveXyPerCandidate,
    // try_candidate_via_mdd) do their own independent propagation
    // inside this stage, but their forcings are not yet threaded
    // through — only the outer Z-middle solver contributes today.
    forcings_out.extend(forcing_delta_triples(&z_solver, &[]));

    // No cache-insert: the fresh-per-call policy above makes the
    // HashMap unused; keep the slot drained so future readers see
    // it isn't populated. The restore_checkpoint + spectral=None
    // are harmless but redundant now.
    let _ = z_cp;
    z_solver.spectral = None;
    let _ = &mut scratch.z_bases;
    metrics.stage_exit[2].fetch_add(1, AtomicOrdering::Relaxed);
}

/// SolveWZ (combined W+Z stage) handler body. Solves the coupled
/// W+Z middle SAT with per-lag Turyn-identity range constraints
/// plus a two-sequence spectral constraint, enumerates `(W, Z)`
/// pairs, and drives the XY fast path per pair via the shared
/// `walk_xy_sub_mdd`. Carries learnt blocking clauses across
/// re-queued attempts so deferred boundaries never re-enumerate
/// `(W, Z)` orbits already tried.
///
/// Returns the residual `SolveWZ` re-queue (with its bumped
/// attempt and an accumulated priority penalty) when the attempt
/// hit the conflict budget or `max_z` before proving UNSAT. The
/// caller is responsible for routing that back onto the queue via
/// `push_with_priority`.
pub(crate) fn process_solve_wz(
    swz: SolveWZWork,
    ctx: &PhaseBContext,
    metrics: &PipelineMetrics,
    template_cache: &mut HashMap<Vec<(i32, i32, i32, i32)>, SatXYTemplate>,
    sat_config: &radical::SolverConfig,
    result_tx: &std::sync::mpsc::Sender<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>,
    rng: &mut u64,
    forcings_out: &mut Vec<(u16, u8, u32)>,
    // Per-call cov_micro accumulator; see `process_solve_z`.
    cov_micro_out: &mut u64,
) -> Option<(PipelineWork, f64)> {
    let k = ctx.k;
    let n = ctx.problem.n;
    let m = ctx.problem.m();
    let mut deferred: Option<(PipelineWork, f64)> = None;
    // Combined W+Z SAT: solve for both middles simultaneously.
    // W vars: 1..middle_m, Z vars: middle_m+1..middle_m+middle_n
    let mut solver = radical::Solver::new();
    let w_var = |i: usize| -> i32 { (i + 1) as i32 };
    let z_var = |i: usize| -> i32 { (ctx.middle_m + i + 1) as i32 };
    let total_vars = ctx.middle_m + ctx.middle_n;

    // Expand boundaries (needed to build V_w and V_z).
    let (w_prefix, w_suffix) = expand_boundary_bits(swz.w_bits, k);
    let mut w_boundary = vec![0i8; m];
    w_boundary[..k].copy_from_slice(&w_prefix);
    w_boundary[m - k..].copy_from_slice(&w_suffix);
    let mut z_boundary = vec![0i8; n];
    for i in 0..k {
        z_boundary[i] = if (swz.z_bits >> i) & 1 == 1 { 1 } else { -1 };
        z_boundary[n - k + i] = if (swz.z_bits >> (k + i)) & 1 == 1 {
            1
        } else {
            -1
        };
    }

    // Sum constraints via PbSetEq: union of ±|σ_W| (resp. ±|σ_Z|)
    // counts across all `candidate_tuples`.
    let w_bnd_sum_local: i32 = w_boundary.iter().map(|&v| v as i32).sum();
    let z_bnd_sum_local: i32 = z_boundary.iter().map(|&v| v as i32).sum();
    let mut w_counts: Vec<u32> = Vec::new();
    let mut z_counts: Vec<u32> = Vec::new();
    for t in &swz.candidate_tuples {
        let abs_w = t.w.abs();
        for &sg in if abs_w == 0 {
            &[0i32] as &[i32]
        } else {
            &[1, -1]
        } {
            if let Some(c) = sigma_full_to_cnt(sg * abs_w, w_bnd_sum_local, ctx.middle_m) {
                if !w_counts.contains(&c) {
                    w_counts.push(c);
                }
            }
        }
        let abs_z = t.z.abs();
        for &sg in if abs_z == 0 {
            &[0i32] as &[i32]
        } else {
            &[1, -1]
        } {
            if let Some(c) = sigma_full_to_cnt(sg * abs_z, z_bnd_sum_local, ctx.middle_n) {
                if !z_counts.contains(&c) {
                    z_counts.push(c);
                }
            }
        }
    }
    w_counts.sort_unstable();
    z_counts.sort_unstable();
    if w_counts.is_empty() || z_counts.is_empty() {
        metrics
            .flow_wz_empty_v
            .fetch_add(1, AtomicOrdering::Relaxed);
        metrics.stage_exit[1].fetch_add(1, AtomicOrdering::Relaxed);
        return None;
    }
    let w_lits: Vec<i32> = (0..ctx.middle_m).map(|i| w_var(i)).collect();
    let z_lits: Vec<i32> = (0..ctx.middle_n).map(|i| z_var(i)).collect();
    solver.add_pb_set_eq(&w_lits, &w_counts);
    solver.add_pb_set_eq(&z_lits, &z_counts);

    // BDKR rules (iv)/(v) boundary pre-filter.
    let rule_iv_state = sat_z_middle::check_z_boundary_rule_iv(n, k, &z_boundary);
    let rule_v_state = sat_z_middle::check_w_boundary_rule_v(m, k, &w_boundary);
    if rule_iv_state == sat_z_middle::BoundaryRuleState::ViolatedAtBoundary
        || rule_v_state == sat_z_middle::BoundaryRuleState::ViolatedAtBoundary
    {
        metrics
            .flow_wz_rule_viol
            .fetch_add(1, AtomicOrdering::Relaxed);
        metrics.stage_exit[1].fetch_add(1, AtomicOrdering::Relaxed);
        return None;
    }
    // Rule (iv) / (v) middle clauses in the combined
    // SolveWZ solver.  The separate helpers take a
    // full-seq-pos → SAT-var closure; here the W
    // middle occupies vars 1..middle_m and the Z
    // middle occupies middle_m+1..middle_m+middle_n.
    let total_existing_vars = total_vars;
    let mut nv_combined = (total_existing_vars + 1) as i32;
    if rule_iv_state == sat_z_middle::BoundaryRuleState::DeferredToMiddle {
        sat_z_middle::add_rule_iv_middle_clauses(
            &mut solver,
            n,
            k,
            |jf| z_var(jf - k),
            &mut nv_combined,
        );
    }
    if rule_v_state == sat_z_middle::BoundaryRuleState::DeferredToMiddle {
        sat_z_middle::add_rule_v_middle_clauses(
            &mut solver,
            m,
            k,
            &w_boundary,
            |pf| w_var(pf - k),
            &mut nv_combined,
        );
    }

    // Combined per-lag autocorrelation: for each lag s,
    //   N_Z(s) + N_W(s) ∈ [-(n-s), n-s]  (Turyn identity coupling)
    //
    // Expressed as a quadratic PB range on the combined W+Z
    // agree terms.  Each "pair agrees" is encoded as a quad
    // term x AND y (with coeff 1) — bnd×mid terms use a
    // pinned true_var so that `lit_a AND true_var = lit_a`;
    // mid×mid terms add TWO quad terms `(a,b)` and `(-a,-b)`
    // (matching the XNOR definition `a==b ⇔ ab ∨ ¬a¬b`).
    //
    // This replaces the older encoding that built an
    // explicit auxiliary var per mid×mid pair via
    // `encode_xnor_agree` + `add_pb_atleast`.  Using
    // `add_quad_pb_range` directly matches the encoding in
    // SolveZ's `fill_z_solver_quad_pb` — the quad_pb
    // propagator prunes much earlier than the XNOR-aux
    // formulation, cutting conflicts-per-solve roughly by
    // half at n=26 k=5.
    {
        // Pin a "true" helper variable for the bnd×mid
        // terms' second literal.  Allocated as the very
        // next var after the existing W/Z middles and the
        // rules (iv)/(v) aux vars (counted in nv_combined).
        let true_var = nv_combined;
        solver.add_clause([true_var]);

        for s in 1..n {
            let max_nzw = (n - s) as i32;
            let nw_pairs = if s < m { (m - s) as i32 } else { 0 };
            let nz_pairs = (n - s) as i32;
            let total_pairs = nw_pairs + nz_pairs;
            let combined_lo = ((total_pairs - max_nzw) / 2).max(0) as u32;
            let combined_hi = ((total_pairs + max_nzw) / 2).min(total_pairs) as u32;

            let mut agree_const = 0u32;
            let mut lits_a: Vec<i32> = Vec::new();
            let mut lits_b: Vec<i32> = Vec::new();
            // W pairs
            if s < m {
                let w_lag = &ctx.w_tmpl.lags[s - 1];
                for &(i, j) in &w_lag.bnd_bnd {
                    if w_boundary[i] == w_boundary[j] {
                        agree_const += 1;
                    }
                }
                for &(bnd_pos, mid_idx) in &w_lag.bnd_mid {
                    let lit = if w_boundary[bnd_pos] == 1 {
                        w_var(mid_idx)
                    } else {
                        -w_var(mid_idx)
                    };
                    lits_a.push(lit);
                    lits_b.push(true_var);
                }
                for &(i, j) in &w_lag.mid_mid {
                    // agree(a,b) = (a AND b) OR (-a AND -b)
                    lits_a.push(w_var(i));
                    lits_b.push(w_var(j));
                    lits_a.push(-w_var(i));
                    lits_b.push(-w_var(j));
                }
            }
            // Z pairs
            if s < n {
                let z_lag = &ctx.z_tmpl.lags[s - 1];
                for &(i, j) in &z_lag.bnd_bnd {
                    if z_boundary[i] == z_boundary[j] {
                        agree_const += 1;
                    }
                }
                for &(bnd_pos, mid_idx) in &z_lag.bnd_mid {
                    let lit = if z_boundary[bnd_pos] == 1 {
                        z_var(mid_idx)
                    } else {
                        -z_var(mid_idx)
                    };
                    lits_a.push(lit);
                    lits_b.push(true_var);
                }
                for &(i, j) in &z_lag.mid_mid {
                    lits_a.push(z_var(i));
                    lits_b.push(z_var(j));
                    lits_a.push(-z_var(i));
                    lits_b.push(-z_var(j));
                }
            }

            let max_variable = lits_a.len() as u32;
            let adj_lo = combined_lo.saturating_sub(agree_const);
            let adj_hi = combined_hi.saturating_sub(agree_const);
            if adj_lo > max_variable {
                solver.add_clause(std::iter::empty::<i32>());
                break;
            }
            if adj_lo == 0 && adj_hi >= max_variable {
                continue;
            }
            if lits_a.is_empty() {
                // No variable-dependent terms; agree_const
                // alone must already satisfy the range
                // (checked by the adj_lo/adj_hi guards above).
                continue;
            }
            let coeffs: Vec<u32> = vec![1; lits_a.len()];
            solver.add_quad_pb_range(&lits_a, &lits_b, &coeffs, adj_lo, adj_hi);
        }
    }

    // Combined WZ spectral: 2|W(ω)|² + 2|Z(ω)|² ≤ pair_bound.
    // Uses two-sequence SpectralConstraint with separate DFT tracking.
    {
        let nf = SPECTRAL_FREQS;
        let total_mid = ctx.middle_m + ctx.middle_n;
        let mut cos_table = vec![0.0f32; total_mid * nf];
        let mut sin_table = vec![0.0f32; total_mid * nf];
        let mut amplitudes = vec![0.0f32; total_mid * nf];
        let mut re1_bnd = vec![0.0f64; nf]; // W boundary DFT
        let mut im1_bnd = vec![0.0f64; nf];
        let mut re2_bnd = vec![0.0f64; nf]; // Z boundary DFT
        let mut im2_bnd = vec![0.0f64; nf];
        let mut mr1 = vec![0.0f64; nf]; // max reduction seq1 (W)
        let mut mr2 = vec![0.0f64; nf]; // max reduction seq2 (Z)

        for fi in 0..nf {
            let omega = (fi as f64 + 1.0) / (nf as f64 + 1.0) * std::f64::consts::PI;
            for pos in 0..m {
                if pos >= k && pos < m - k {
                    continue;
                }
                let val = w_boundary[pos] as f64;
                re1_bnd[fi] += val * (omega * pos as f64).cos();
                im1_bnd[fi] += val * (omega * pos as f64).sin();
            }
            for pos in 0..n {
                if pos >= k && pos < n - k {
                    continue;
                }
                let val = z_boundary[pos] as f64;
                re2_bnd[fi] += val * (omega * pos as f64).cos();
                im2_bnd[fi] += val * (omega * pos as f64).sin();
            }
            for vi in 0..ctx.middle_m {
                let pos = k + vi;
                let c = (omega * pos as f64).cos() as f32;
                let s = (omega * pos as f64).sin() as f32;
                cos_table[vi * nf + fi] = c;
                sin_table[vi * nf + fi] = s;
                let amp = (c * c + s * s).sqrt();
                amplitudes[vi * nf + fi] = amp;
                mr1[fi] += amp as f64;
            }
            for vi in 0..ctx.middle_n {
                let pos = k + vi;
                let c = (omega * pos as f64).cos() as f32;
                let s = (omega * pos as f64).sin() as f32;
                let idx = (ctx.middle_m + vi) * nf + fi;
                cos_table[idx] = c;
                sin_table[idx] = s;
                let amp = (c * c + s * s).sqrt();
                amplitudes[idx] = amp;
                mr2[fi] += amp as f64;
            }
        }
        // Dummy combined re/im (not used in seq2 mode conflict check)
        let re_dummy = vec![0.0f64; nf];
        let im_dummy = vec![0.0f64; nf];
        solver.spectral = Some(radical::SpectralConstraint {
            num_seq_vars: total_mid,
            cos_table: std::sync::Arc::new(cos_table),
            sin_table: std::sync::Arc::new(sin_table),
            num_freqs: nf,
            re: re_dummy.clone(),
            im: im_dummy.clone(),
            re_boundary: re_dummy.clone(),
            im_boundary: im_dummy,
            bound: ctx.problem.target_energy() as f64, // 6n-2: full energy budget for 2|W|²+2|Z|²+|X|²+|Y|²
            per_freq_bound: None,
            max_reduction: vec![0.0; nf],
            amplitudes: std::sync::Arc::new(amplitudes),
            assigned: vec![false; total_mid],
            values: vec![0i8; total_mid],
            seq2: Some(radical::Seq2Config {
                seq2_start: ctx.middle_m,
                weight1: 2.0,
                weight2: 2.0,
                individual_bound: ctx.individual_bound,
                re1: re1_bnd.clone(),
                im1: im1_bnd.clone(),
                re1_boundary: re1_bnd,
                im1_boundary: im1_bnd,
                max_reduction1: mr1,
                re2: re2_bnd.clone(),
                im2: im2_bnd.clone(),
                re2_boundary: re2_bnd,
                im2_boundary: im2_bnd,
                max_reduction2: mr2,
            }),
        });
    }

    // Snapshot search stats for the combined SAT enumeration.
    // Combined WZ does the work of both the W and Z stages, so
    // we credit its decisions/propagations to BOTH stage
    // counters — each stage's "per-solve average" stays
    // interpretable, at the cost of a small overcount in the
    // grand total.
    // --outfix middle pins: force Z/W middle positions to
    // the canonical values via unit clauses.  Let the SAT
    // decide the remaining middle bits.
    for &(mid, val) in &ctx.outfix_z_mid_pins {
        if mid < ctx.middle_n {
            let lit = if val > 0 { z_var(mid) } else { -z_var(mid) };
            solver.add_clause([lit]);
        }
    }
    for &(mid, val) in &ctx.outfix_w_mid_pins {
        if mid < ctx.middle_m {
            let lit = if val > 0 { w_var(mid) } else { -w_var(mid) };
            solver.add_clause([lit]);
        }
    }

    // Inject blocking clauses accumulated from earlier
    // attempts on this boundary.  Each block rules out
    // one previously-enumerated (W, Z) middle; they use
    // stable W/Z middle var IDs (1..=total_vars) so
    // they remain valid in this freshly-built solver.
    // Persisting these across re-queues is what makes
    // the search eventually reach SAT's Some(false)
    // rather than redundantly re-enumerating the same
    // (W, Z) orbits with different phase RNG each
    // attempt.
    for block in &swz.prior_blocks {
        solver.add_clause(block.iter().copied());
    }

    let wz_d0 = solver.num_decisions();
    let wz_p0 = solver.num_propagations();
    let wz_l0 = solver.num_level0_vars();
    let wz_nv = solver.num_vars();

    // Enumerate WZ solutions.
    //
    // Re-queue strategy: rather than burning a large
    // conflict budget on one boundary (which monopolises
    // a worker and slows space coverage), use a modest
    // budget per attempt and push the item back into the
    // queue when the budget is exhausted.  Exponential
    // backoff: attempt 0 gets 5k conflicts, attempt 1
    // gets 10k, etc., capped at 50k.  Re-queued items
    // sit at priority −1 (below fresh boundaries and
    // first-attempt SolveWZ), so the MDD is covered
    // once before we retry hard boundaries.
    let mut wz_count = 0usize;
    // Per-attempt conflict budget doubles each retry so
    // hard boundaries eventually get enough SAT effort to
    // reach a decisive result (UNSAT or SAT).  Cap at 1M
    // per attempt to bound memory; re-queue beyond that
    // still happens (see below) so we defer but never
    // cancel.
    let conflict_budget: u64 = (5_000u64 << swz.attempt.min(7)).min(1_000_000);
    solver.set_conflict_limit(conflict_budget);
    // Tracks whether the enumeration was cut off with
    // more WZ solutions possibly remaining (None from
    // solve() = conflict limit, or hit max_z cap),
    // vs. fully exhausted (Some(false) = UNSAT proved).
    let mut more_possible = false;
    // New blocking clauses produced in THIS attempt.
    // If the attempt is deferred via re-queue, these
    // plus the prior_blocks get passed forward so the
    // next attempt skips already-found (W, Z) pairs.
    let mut new_blocks: Vec<Vec<i32>> = Vec::new();
    loop {
        if !ctx.continue_after_sat && ctx.found.load(AtomicOrdering::Relaxed) {
            break;
        }
        if wz_count >= ctx.max_z {
            more_possible = true;
            break;
        }
        // Random phases for both W and Z.  Mix the
        // attempt number into the RNG so re-queued
        // items explore a different region of the
        // phase space than their first attempt.
        let mut attempt_rng = *rng ^ (swz.attempt as u64).wrapping_mul(0x9e3779b97f4a7c15);
        let phases: Vec<bool> = (0..total_vars)
            .map(|_| {
                attempt_rng ^= attempt_rng << 13;
                attempt_rng ^= attempt_rng >> 7;
                attempt_rng ^= attempt_rng << 17;
                attempt_rng & 1 == 1
            })
            .collect();
        *rng = attempt_rng;
        solver.set_phase(&phases);
        metrics
            .flow_wz_sat_calls
            .fetch_add(1, AtomicOrdering::Relaxed);
        let sat_res = solver.solve();
        if sat_res == None {
            // Conflict limit hit — more solutions may exist.
            more_possible = true;
            metrics
                .flow_wz_budget_hit
                .fetch_add(1, AtomicOrdering::Relaxed);
            // Don't bump flow_wz_first_unsat here: the field name
            // means "first iteration reported UNSAT", and a
            // conflict-budget timeout is not UNSAT. Mirrors the
            // round-28 fix for the analogous flow_w_unsat /
            // flow_w_timeout mutual exclusion.
            break;
        }
        if sat_res == Some(false) {
            // Fully enumerated: every assignment has been
            // blocked.  No point re-queuing.
            metrics
                .flow_wz_exhausted
                .fetch_add(1, AtomicOrdering::Relaxed);
            if wz_count == 0 {
                metrics
                    .flow_wz_first_unsat
                    .fetch_add(1, AtomicOrdering::Relaxed);
            }
            break;
        }
        wz_count += 1;
        metrics
            .flow_wz_solutions
            .fetch_add(1, AtomicOrdering::Relaxed);

        // Extract W middle
        let w_mid: Vec<i8> = (0..ctx.middle_m)
            .map(|i| {
                if solver.value(w_var(i)).unwrap() {
                    1
                } else {
                    -1
                }
            })
            .collect();
        let mut w_vals = w_boundary.clone();
        w_vals[k..k + ctx.middle_m].copy_from_slice(&w_mid);

        // Extract Z middle
        let z_mid: Vec<i8> = (0..ctx.middle_n)
            .map(|i| {
                if solver.value(z_var(i)).unwrap() {
                    1
                } else {
                    -1
                }
            })
            .collect();
        let mut z_vals = Vec::with_capacity(n);
        z_vals.extend_from_slice(&z_boundary[..k]);
        z_vals.extend_from_slice(&z_mid);
        z_vals.extend_from_slice(&z_boundary[n - k..]);

        // Block this (W,Z) pair.  Also stash the clause
        // in new_blocks so it survives re-queue: the
        // next attempt's fresh solver will re-add it
        // together with swz.prior_blocks.
        let block: Vec<i32> = (0..total_vars as i32 + 1)
            .skip(1)
            .map(|v| if solver.value(v) == Some(true) { -v } else { v })
            .collect();
        solver.reset();
        solver.add_clause(block.iter().copied());
        new_blocks.push(block);

        // Got a valid (W,Z) pair — proceed to XY
        metrics
            .flow_z_solutions
            .fetch_add(1, AtomicOrdering::Relaxed);
        let z_seq = PackedSeq::from_values(&z_vals);
        let w_seq = PackedSeq::from_values(&w_vals);
        let zw_autocorr = compute_zw_autocorr(ctx.problem, &z_seq, &w_seq);

        // Multi-tuple XY template: the SolveWZ boundary is
        // compatible with *all* candidate_tuples.  Use
        // build_multi so the XY SAT's V_x/V_y cover every
        // compatible |σ_X|/|σ_Y| across those tuples, and
        // narrow post-hoc by the W+Z sums we just decoded
        // (via zw_autocorr → lag PB ranges) and by the
        // candidate magnitudes.
        let mut tuple_key: Vec<(i32, i32, i32, i32)> = swz
            .candidate_tuples
            .iter()
            .map(|t| (t.x, t.y, t.z, t.w))
            .collect();
        tuple_key.sort_unstable();
        let template = template_cache.entry(tuple_key).or_insert_with(|| {
            SatXYTemplate::build_multi_opts(
                ctx.problem,
                &swz.candidate_tuples,
                &sat_config,
                ctx.conj_xy_product,
            )
            .unwrap()
        });
        let candidate = CandidateZW { zw_autocorr };
        if let Some(mut xy_solver) = template.prepare_candidate_solver(&candidate) {
            if n > 30 {
                xy_solver.set_conflict_limit(5000);
            }
            // Snapshot before the walk so only the per-(W,Z) SAT
            // work is attributed. `prepare_candidate_solver`
            // clones the template and injects candidate-specific
            // constraints; the resulting solver's prop counters
            // start at the cloned base, so snapshotting-then-diff
            // is needed to isolate this call's work.
            let xy_plk0: Vec<[u64; radical::PropKind::COUNT]> =
                xy_solver.propagations_by_kind_level().to_vec();
            let (xy_root, xy_nodes) = resolve_xy_graph(&swz.xy_graph, &ctx.mdd.nodes);
            walk_xy_sub_mdd(
                xy_root,
                0,
                ctx.xy_zw_depth,
                0,
                0,
                &ctx.xy_pos_order,
                xy_nodes,
                ctx.max_bnd_sum,
                ctx.middle_n as i32,
                &swz.candidate_tuples,
                &mut |x_bits, y_bits| {
                    if !ctx.continue_after_sat && ctx.found.load(AtomicOrdering::Relaxed) {
                        return;
                    }
                    if let Some((fx, fy)) = ctx.outfix_xy {
                        if x_bits != fx || y_bits != fy {
                            return;
                        }
                    }
                    if ctx.conj_zw_bound
                        && !check_conj_zw_bound(n, k, x_bits, y_bits, &z_seq, &w_seq)
                    {
                        metrics
                            .flow_xy_zw_bound_rej
                            .fetch_add(1, AtomicOrdering::Relaxed);
                        return;
                    }
                    metrics.stage_enter[3].fetch_add(1, AtomicOrdering::Relaxed);
                    let x_var = |i: usize| -> i32 { (i + 1) as i32 };
                    let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };
                    let mut assumptions = Vec::with_capacity(
                        4 * k + ctx.outfix_x_mid_pins.len() + ctx.outfix_y_mid_pins.len(),
                    );
                    for i in 0..k {
                        assumptions.push(if (x_bits >> i) & 1 == 1 {
                            x_var(i)
                        } else {
                            -x_var(i)
                        });
                        assumptions.push(if (x_bits >> (k + i)) & 1 == 1 {
                            x_var(n - k + i)
                        } else {
                            -x_var(n - k + i)
                        });
                        assumptions.push(if (y_bits >> i) & 1 == 1 {
                            y_var(i)
                        } else {
                            -y_var(i)
                        });
                        assumptions.push(if (y_bits >> (k + i)) & 1 == 1 {
                            y_var(n - k + i)
                        } else {
                            -y_var(n - k + i)
                        });
                    }
                    // --outfix middle pins for X/Y: force middle positions too.
                    for &(mid, val) in &ctx.outfix_x_mid_pins {
                        if mid < ctx.middle_n {
                            let lit = if val > 0 {
                                x_var(k + mid)
                            } else {
                                -x_var(k + mid)
                            };
                            assumptions.push(lit);
                        }
                    }
                    for &(mid, val) in &ctx.outfix_y_mid_pins {
                        if mid < ctx.middle_n {
                            let lit = if val > 0 {
                                y_var(k + mid)
                            } else {
                                -y_var(k + mid)
                            };
                            assumptions.push(lit);
                        }
                    }
                    // Snapshot search stats around the SAT call.
                    let xy_d0 = xy_solver.num_decisions();
                    let xy_p0 = xy_solver.num_propagations();
                    let xy_l0 = xy_solver.num_level0_vars();
                    let xy_nv = xy_solver.num_vars();
                    let result = xy_solver.solve_with_assumptions(&assumptions);
                    metrics
                        .items_completed
                        .fetch_add(1, AtomicOrdering::Relaxed);
                    metrics.stage_exit[3].fetch_add(1, AtomicOrdering::Relaxed);

                    let xy_decisions = xy_solver.num_decisions().saturating_sub(xy_d0);
                    let xy_propagations = xy_solver.num_propagations().saturating_sub(xy_p0);
                    let xy_pre_forced = xy_l0 as u64;
                    let xy_free_vars = xy_nv.saturating_sub(xy_l0) as u64;
                    metrics.flow_xy_solves.fetch_add(1, AtomicOrdering::Relaxed);
                    metrics
                        .flow_xy_decisions
                        .fetch_add(xy_decisions, AtomicOrdering::Relaxed);
                    metrics
                        .flow_xy_propagations
                        .fetch_add(xy_propagations, AtomicOrdering::Relaxed);
                    metrics
                        .flow_xy_root_forced
                        .fetch_add(xy_pre_forced, AtomicOrdering::Relaxed);
                    metrics
                        .flow_xy_free_sum
                        .fetch_add(xy_free_vars, AtomicOrdering::Relaxed);

                    match result {
                        Some(true) => metrics.flow_xy_sat.fetch_add(1, AtomicOrdering::Relaxed),
                        Some(false) => metrics.flow_xy_unsat.fetch_add(1, AtomicOrdering::Relaxed),
                        None => {
                            let cover = xy_cover_micro(result, xy_decisions, xy_free_vars);
                            metrics
                                .flow_xy_timeout_cov_micro
                                .fetch_add(cover, AtomicOrdering::Relaxed);
                            *cov_micro_out = cov_micro_out.saturating_add(cover);
                            metrics
                                .flow_xy_timeout
                                .fetch_add(1, AtomicOrdering::Relaxed)
                        }
                    };
                    if result == Some(true) {
                        let (x, y) = template.extract_xy(&xy_solver);
                        if verify_tt(ctx.problem, &x, &y, &z_seq, &w_seq) {
                            if !ctx.continue_after_sat {
                                ctx.found.store(true, AtomicOrdering::Relaxed);
                            }
                            let _ = result_tx.send((x, y, z_seq.clone(), w_seq.clone()));
                        }
                    }
                },
            );
            // Drain the XY solver's propagation delta into the
            // stage's forcing sink so `StageOutcome::forcings`
            // reflects the actual inline XY work alongside the
            // outer combined solver.
            forcings_out.extend(forcing_delta_triples(&xy_solver, &xy_plk0));
        }
    }

    // Aggregate combined-WZ stats into both W and Z stage
    // counters (see comment at snapshot site above).
    let wz_decisions = solver.num_decisions().saturating_sub(wz_d0);
    let wz_propagations = solver.num_propagations().saturating_sub(wz_p0);
    let wz_pre_forced = wz_l0 as u64;
    let wz_free_vars = wz_nv.saturating_sub(wz_l0) as u64;
    metrics.flow_w_solves.fetch_add(1, AtomicOrdering::Relaxed);
    metrics
        .flow_w_decisions
        .fetch_add(wz_decisions, AtomicOrdering::Relaxed);
    metrics
        .flow_w_propagations
        .fetch_add(wz_propagations, AtomicOrdering::Relaxed);
    metrics
        .flow_w_root_forced
        .fetch_add(wz_pre_forced, AtomicOrdering::Relaxed);
    metrics
        .flow_w_free_sum
        .fetch_add(wz_free_vars, AtomicOrdering::Relaxed);
    metrics.flow_z_solves.fetch_add(1, AtomicOrdering::Relaxed);
    metrics
        .flow_z_decisions
        .fetch_add(wz_decisions, AtomicOrdering::Relaxed);
    metrics
        .flow_z_propagations
        .fetch_add(wz_propagations, AtomicOrdering::Relaxed);
    metrics
        .flow_z_root_forced
        .fetch_add(wz_pre_forced, AtomicOrdering::Relaxed);
    metrics
        .flow_z_free_sum
        .fetch_add(wz_free_vars, AtomicOrdering::Relaxed);
    // `solver` is the combined W+Z middle solver built fresh in
    // this call; empty baseline gives full attribution. Inline
    // per-(W,Z) XY solvers (`xy_solver`) are drained into the same
    // sink inside the walk loop above, so `forcings_out` now
    // covers both the outer middle solver and every per-pair XY
    // solve.
    forcings_out.extend(forcing_delta_triples(&solver, &[]));

    metrics.stage_exit[1].fetch_add(1, AtomicOrdering::Relaxed);

    // Re-queue: if the enumeration was cut short (conflict
    // limit hit, or max_z cap reached) and we haven't
    // found a TT, push this item back with attempt+1 at
    // a lower priority.  NO CAP on attempts — we defer
    // hard boundaries to lower priority slots but never
    // abandon them.  The per-attempt budget doubles each
    // retry (see conflict_budget above) so every boundary
    // eventually gets enough effort for SAT/UNSAT.
    if more_possible && (ctx.continue_after_sat || !ctx.found.load(AtomicOrdering::Relaxed)) {
        // Priority: re-queued SolveWZ items must sit
        // BELOW stage 0 (fresh MDD boundaries, priority
        // 0.0) so fresh boundaries are always preferred
        // over retries.  Without this, re-queued items
        // at attempt=0's priority 0.9 starve the walker:
        // we'd cycle 18 boundaries forever instead of
        // covering the whole space.
        //
        // Each retry drops priority by 0.001 so retries
        // within themselves are FIFO by fewest attempts
        // (gentler retries get priority over harder
        // ones).  This implements "defer but never
        // cancel": we walk every fresh boundary first,
        // then work through retries in order of
        // accumulated budget.
        let priority = -0.001 * (swz.attempt + 1) as f64;
        metrics.stage_enter[1].fetch_add(1, AtomicOrdering::Relaxed);
        // Carry prior blocks forward, appending the ones
        // produced this attempt.  Without this, the next
        // attempt would rebuild a fresh solver that
        // doesn't know which (W, Z) pairs have already
        // been tried, and would redundantly re-enumerate
        // the same orbits with different phase RNG.
        let mut carried_blocks = swz.prior_blocks;
        carried_blocks.extend(new_blocks);
        deferred = Some((
            PipelineWork::SolveWZ(SolveWZWork {
                tuple: swz.tuple,
                z_bits: swz.z_bits,
                w_bits: swz.w_bits,
                xy_graph: swz.xy_graph.clone(),
                candidate_tuples: swz.candidate_tuples.clone(),
                attempt: swz.attempt + 1,
                prior_blocks: carried_blocks,
            }),
            priority,
        ));
    }
    deferred
}

/// Build a `PhaseBContext` populated from the given problem / tuple
/// list / search config. Duplicates the setup block at the top of
/// `run_mdd_sat_search` so the framework `MddStagesAdapter` can own
/// an identical context without invoking the legacy worker loop.
///
/// Panics / exits if no usable MDD file is available (matches
/// `run_mdd_sat_search`'s exit behavior).
pub(crate) fn build_phase_b_context(
    problem: Problem,
    tuples: &[SumTuple],
    cfg: &SearchConfig,
    verbose: bool,
    k: usize,
) -> Arc<PhaseBContext> {
    let n = problem.n;
    let m = problem.m();
    let try_k = k.min((n - 1) / 2);
    let mdd = match load_best_mdd(try_k, verbose) {
        Some(m) => {
            if m.k != try_k {
                eprintln!(
                    "error: requested --mdd-k={} but only mdd-{}.bin found (k={})",
                    k, m.k, m.k
                );
                eprintln!("Generate the exact MDD: target/release/gen_mdd {}", try_k);
                std::process::exit(1);
            }
            Arc::new(m)
        }
        None => {
            // No `mdd-<k>.bin` available — build one in memory via
            // `mdd_bfs::build_bfs_mdd`. Fast for small k; identical
            // structure to what `target/release/gen_mdd` writes. Prevents
            // the PR-review-flagged regression where `--wz=cross`
            // aborted on small n whenever the repo lacked a precomputed
            // MDD file. For larger `k` (n ≥ 26 territory) the user
            // should still precompute for performance, but it's no
            // longer a hard requirement.
            if verbose {
                eprintln!(
                    "No mdd-{}.bin file; building in-memory MDD via BFS (one-shot)...",
                    try_k
                );
            }
            Arc::new(mdd_bfs::build_bfs_mdd(try_k))
        }
    };
    let k = mdd.k;
    assert!(2 * k <= n, "k={} too large for n={}: need 2k <= n", k, n);
    assert!(2 * k <= m, "k={} too large for m={}: need 2k <= m", k, m);
    let middle_n = n - 2 * k;
    let middle_m = m - 2 * k;
    let max_bnd_sum = (2 * k) as i32;
    let zw_depth = 2 * k;
    let full_pos_order: Vec<usize> = {
        let mut v = Vec::with_capacity(2 * k);
        for t in 0..k {
            v.push(t);
            v.push(2 * k - 1 - t);
        }
        v
    };
    Arc::new(PhaseBContext {
        mdd: Arc::clone(&mdd),
        xy_pos_order: full_pos_order,
        tuples: tuples.to_vec(),
        w_tmpl: sat_z_middle::LagTemplate::new(m, k),
        z_tmpl: sat_z_middle::LagTemplate::new(n, k),
        problem,
        k,
        zw_depth,
        xy_zw_depth: zw_depth,
        middle_n,
        middle_m,
        max_bnd_sum,
        max_z: cfg.max_z.min(16),
        individual_bound: problem.spectral_bound(),
        pair_bound: cfg.max_spectral.unwrap_or(problem.spectral_bound()),
        theta: cfg.theta_samples,
        mdd_extend: cfg.mdd_extend,
        conj_xy_product: cfg.conj_xy_product,
        conj_zw_bound: cfg.conj_zw_bound,
        continue_after_sat: cfg.continue_after_sat || cfg.bench_cover_log2.is_some(),
        xy_mdd_mode: std::env::var("XY_MDD").ok().as_deref() == Some("1"),
        structural_xy_runtime: std::env::var("MDD_XY_RAW").ok().as_deref() != Some("1"),
        structural_xy_cache: Arc::new(Mutex::new(HashMap::default())),
        w_mid_vars: (0..middle_m).map(|i| (i + 1) as i32).collect(),
        z_mid_vars: (0..middle_n).map(|i| (i + 1) as i32).collect(),
        z_spectral_tables: if middle_n >= 8 {
            Some(radical::SpectralTables::new(n, k, SPECTRAL_FREQS))
        } else {
            None
        },
        w_spectral_tables: if middle_m >= 8 {
            Some(radical::SpectralTables::new(m, k, SPECTRAL_FREQS))
        } else {
            None
        },
        found: Arc::new(AtomicBool::new(false)),
        outfix_xy: cfg.test_outfix.as_ref().and_then(|o| o.xy_bits),
        outfix_z_mid_pins: cfg
            .test_outfix
            .as_ref()
            .map(|o| o.z_middle_pins.clone())
            .unwrap_or_default(),
        outfix_w_mid_pins: cfg
            .test_outfix
            .as_ref()
            .map(|o| o.w_middle_pins.clone())
            .unwrap_or_default(),
        outfix_x_mid_pins: cfg
            .test_outfix
            .as_ref()
            .map(|o| o.x_middle_pins.clone())
            .unwrap_or_default(),
        outfix_y_mid_pins: cfg
            .test_outfix
            .as_ref()
            .map(|o| o.y_middle_pins.clone())
            .unwrap_or_default(),
    })
}

/// Navigate the MDD to a specific `(z_bits, w_bits)` boundary, returning
/// the XY sub-root anchored at that boundary. Returns `None` if the
/// boundary is not live (pruned away during MDD gen).
///
/// Used by the framework `MddStagesAdapter` to seed a single
/// `BoundaryWork` when `--outfix` pins the boundary explicitly —
/// avoids enumerating hundreds of millions of boundaries at large
/// `k` just to find the one the caller wants.
pub(crate) fn mdd_navigate_to_outfix(
    root: u32,
    zw_depth: usize,
    pos_order: &[usize],
    nodes: &[[u32; 4]],
    z_bits: u32,
    w_bits: u32,
) -> Option<u32> {
    let mut nid = root;
    for level in 0..zw_depth {
        if nid == mdd_reorder::DEAD {
            return None;
        }
        let pos = pos_order[level];
        let z_bit = (z_bits >> pos) & 1;
        let w_bit = (w_bits >> pos) & 1;
        let branch = (z_bit | (w_bit << 1)) as usize;
        if nid != mdd_reorder::LEAF {
            nid = nodes[nid as usize][branch];
            if nid == mdd_reorder::DEAD {
                return None;
            }
        }
    }
    Some(nid)
}

/// Enumerate every live boundary path through the first `zw_depth`
/// levels of the MDD, returning a `BoundaryWork` per path. Used by
/// the framework `MddStagesAdapter` to seed its queue upfront; the
/// legacy worker loop instead pulls boundaries on demand via its
/// monitor's LCG path walker.
///
/// A path is "live" iff none of its nodes are `mdd_reorder::DEAD`
/// — i.e. it terminates at some non-DEAD XY-sub-tree root.
pub(crate) fn enumerate_live_boundaries(
    ctx: &PhaseBContext,
    cancelled: &AtomicBool,
) -> Vec<BoundaryWork> {
    let mdd = &*ctx.mdd;
    let zw_depth = ctx.zw_depth;
    let xy_pos_order = &ctx.xy_pos_order;
    let mut out: Vec<BoundaryWork> = Vec::new();

    fn walk(
        nid: u32,
        level: usize,
        z_bits: u32,
        w_bits: u32,
        depth: usize,
        order: &[usize],
        nodes: &[[u32; 4]],
        out: &mut Vec<BoundaryWork>,
        cancelled: &AtomicBool,
    ) {
        // Poll the shared cancel flag once per visited node. At
        // n=26 k=7 this walk visits ~18M nodes; the watchdog set
        // by `--sat-secs` flips this flag and we bail with a
        // partial boundary list. The adapter treats that as a
        // legitimate (if incomplete) seed set so the framework
        // can still print honest telemetry.
        if cancelled.load(AtomicOrdering::Relaxed) {
            return;
        }
        if nid == mdd_reorder::DEAD {
            return;
        }
        if level == depth {
            out.push(BoundaryWork {
                z_bits,
                w_bits,
                xy_graph: loaded_xy_graph(nid),
            });
            return;
        }
        if nid == mdd_reorder::LEAF {
            // A LEAF reached before depth means the full (z,w)
            // prefix is unconstrained at the remaining levels —
            // enumerate all 4 branches.
            let pos = order[level];
            for b in 0..4u32 {
                let z = b & 1;
                let w = (b >> 1) & 1;
                walk(
                    mdd_reorder::LEAF,
                    level + 1,
                    z_bits | (z << pos),
                    w_bits | (w << pos),
                    depth,
                    order,
                    nodes,
                    out,
                    cancelled,
                );
            }
            return;
        }
        let pos = order[level];
        for b in 0..4u32 {
            let child = nodes[nid as usize][b as usize];
            if child == mdd_reorder::DEAD {
                continue;
            }
            let z = b & 1;
            let w = (b >> 1) & 1;
            walk(
                child,
                level + 1,
                z_bits | (z << pos),
                w_bits | (w << pos),
                depth,
                order,
                nodes,
                out,
                cancelled,
            );
        }
    }

    walk(
        mdd.root,
        0,
        0,
        0,
        zw_depth,
        xy_pos_order,
        &mdd.nodes,
        &mut out,
        cancelled,
    );
    out
}

/// Bundle of freshly-constructed `PipelineMetrics` counters. Used
/// by framework callers that run the staged adapter outside the
/// legacy `run_mdd_sat_search` closure.
pub(crate) fn new_pipeline_metrics() -> PipelineMetrics {
    use std::sync::atomic::AtomicU64;
    let z = || Arc::new(AtomicU64::new(0));
    PipelineMetrics {
        flow_bnd_sum_fail: z(),
        stage_enter: (0..4).map(|_| z()).collect(),
        stage_exit: (0..4).map(|_| z()).collect(),
        pending_boundaries: z(),
        flow_w_unsat: z(),
        flow_w_timeout: z(),
        flow_w_solutions: z(),
        flow_w_spec_fail: z(),
        flow_w_spec_pass: z(),
        flow_w_solves: z(),
        flow_w_decisions: z(),
        flow_w_propagations: z(),
        flow_w_root_forced: z(),
        flow_w_free_sum: z(),
        items_completed: z(),
        flow_z_prep_fail: z(),
        flow_xy_zw_bound_rej: z(),
        flow_xy_sat: z(),
        flow_xy_unsat: z(),
        flow_xy_timeout: z(),
        flow_xy_timeout_cov_micro: z(),
        flow_xy_solves: z(),
        flow_xy_decisions: z(),
        flow_xy_propagations: z(),
        flow_xy_root_forced: z(),
        flow_xy_free_sum: z(),
        flow_z_unsat: z(),
        flow_z_timeout: z(),
        flow_z_solutions: z(),
        flow_z_spec_fail: z(),
        flow_z_pair_fail: z(),
        flow_z_solves: z(),
        flow_z_decisions: z(),
        flow_z_propagations: z(),
        flow_z_root_forced: z(),
        flow_z_free_sum: z(),
        extensions_pruned: z(),
        flow_wz_empty_v: z(),
        flow_wz_rule_viol: z(),
        flow_wz_sat_calls: z(),
        flow_wz_first_unsat: z(),
        flow_wz_solutions: z(),
        flow_wz_exhausted: z(),
        flow_wz_budget_hit: z(),
    }
}

/// MDD pipeline search: unified priority queue with stages MDD→W→Z→XY.
/// All workers are identical — they grab the highest-stage item from the queue.
/// Later stages (closer to producing a result) always get processed first.
/// Unified search dispatch.
///
/// All `--wz` modes route through the framework
/// `search_framework::engine` + per-mode adapter. Kept with the
/// legacy signature so existing benchmarks and correctness tests
/// (the `hybrid_finds_ttN` suite in `src/main.rs`) don't need to
/// rewrite their call sites.
pub(crate) fn run_mdd_sat_search(
    problem: Problem,
    tuples: &[SumTuple],
    cfg: &SearchConfig,
    verbose: bool,
    k: usize,
) -> SearchReport {
    use crate::search_framework::engine::{EngineConfig, SearchEngine};
    use crate::search_framework::events::SearchEvent;
    use crate::search_framework::mode_adapters::mdd_stages::{MddPayload, MddStagesAdapter};
    use crate::search_framework::mode_adapters::sync::{SyncAdapter, SyncPayload};
    use crate::search_framework::queue::GoldThenWork;

    let start = std::time::Instant::now();

    // --wz=sync: no MDD, no tuple enumeration. Framework wraps the
    // walker as a single SyncWalkStage; inside it still spins up
    // its own parallel DFS.
    if cfg.effective_wz_mode() == WzMode::Sync {
        let sync_cfg = crate::sync_walker::SyncConfig {
            sat_secs: cfg.sat_secs,
            sat_config: cfg.sat_config.clone(),
            conflict_limit: cfg.conflict_limit,
            random_seed: None,
            cancel: None,
            exchange: None,
            projected_fraction_ppm: None,
            live_sink: None,
        };
        let _ = tuples;
        let (adapter, result_rx) = SyncAdapter::build(problem, sync_cfg, verbose);
        let mut engine = SearchEngine::<SyncPayload>::new(
            EngineConfig::default(),
            Box::new(GoldThenWork::new(32)),
        );
        let cancel_flag = engine.cancel_flag();
        let drain = std::thread::spawn(move || {
            let mut found = None;
            while let Ok(sol) = result_rx.recv() {
                // See comment in the MDD branch below for the
                // cancel-on-first-solution rationale.
                cancel_flag.store(true, AtomicOrdering::Relaxed);
                found = Some(sol);
            }
            found
        });
        engine.run_since(start, &adapter, |_| {});
        drop(adapter);
        let found = drain.join().unwrap_or(None);
        if verbose {
            if let Some((x, y, z, w)) = found.as_ref() {
                println!(
                    "\nFOUND! x={} y={} z={} w={}",
                    colored_pm(x),
                    colored_pm(y),
                    colored_pm(z),
                    colored_pm(w)
                );
            }
        }
        return SearchReport {
            stats: SearchStats::default(),
            elapsed: start.elapsed(),
            found_solution: found.is_some(),
        };
    }

    // MDD-backed modes (cross / apart / together): build staged
    // adapter, run engine, drain solution channel.
    let mode_name: &'static str = match cfg.effective_wz_mode() {
        WzMode::Cross => "cross",
        WzMode::Apart => "apart",
        WzMode::Together => "together",
        WzMode::Sync => unreachable!("sync branched above"),
    };
    let mut engine =
        SearchEngine::<MddPayload>::new(EngineConfig::default(), Box::new(GoldThenWork::new(32)));
    let cancel_flag = engine.cancel_flag();
    let (adapter, result_rx) = MddStagesAdapter::build(
        problem,
        tuples.to_vec(),
        cfg,
        k,
        verbose,
        mode_name,
        &cancel_flag,
    );
    let found_ctx = Arc::clone(&adapter.ctx.found);
    let drain = std::thread::spawn(move || {
        let mut found = false;
        while let Ok(_sol) = result_rx.recv() {
            found_ctx.store(true, AtomicOrdering::Relaxed);
            // Stop the engine on first solution — otherwise the
            // coordinator drains the rest of the queue before
            // `engine.run` returns, wasting work.
            cancel_flag.store(true, AtomicOrdering::Relaxed);
            found = true;
        }
        found
    });
    engine.run_since(start, &adapter, |event| {
        if let SearchEvent::Progress(p) = event {
            if verbose {
                eprintln!(
                    "[framework:{}] elapsed={:.1?} covered={:.3}/{:.3} ttc={:?}",
                    mode_name, p.elapsed, p.covered_mass.0, p.total_mass.0, p.ttc
                );
            }
        }
    });
    drop(adapter);
    let found = drain.join().unwrap_or(false);
    SearchReport {
        stats: SearchStats::default(),
        elapsed: start.elapsed(),
        found_solution: found,
    }
}
