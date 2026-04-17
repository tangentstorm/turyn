//! Unified 4-stage MDD pipeline driver + supporting work items and navigation.

#![allow(unused_imports)]

use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering as AtomicOrdering};
use std::time::Instant;

use rustfft::num_complex::Complex;

use turyn::mdd_reorder;
use turyn::mdd_zw_first;
use turyn::sat_z_middle;

use crate::config::*;
use crate::enumerate::*;
use crate::legacy_search::*;
use crate::spectrum::*;
use crate::stochastic::*;
use crate::types::*;
use crate::xy_sat::*;
use crate::SPECTRAL_FREQS;


/// A fully-specified `(Z, W)` candidate ready for the XY SAT stage.
/// Wrapped in `SolveXYWork` and pushed onto the unified runner's gold
/// queue by the cross-mode producer.
pub(crate) struct SatWorkItem {
    pub(crate) tuple: SumTuple,
    pub(crate) z: PackedSeq,
    pub(crate) w: PackedSeq,
    /// Pre-computed 2·N_Z(s) + 2·N_W(s) for s in 1..n.
    pub(crate) zw_autocorr: Vec<i32>,
    /// Maximum spectral pair power across the realfft frequency grid.
    /// Lower = higher priority (best candidates get solved first).
    pub(crate) priority: f64,
}


pub(crate) fn compute_zw_autocorr(problem: Problem, z: &PackedSeq, w: &PackedSeq) -> Vec<i32> {
    let mut zw = vec![0i32; problem.n];
    for s in 1..problem.n {
        let nz = z.autocorrelation(s);
        let nw = if s < problem.m() { w.autocorrelation(s) } else { 0 };
        zw[s] = 2 * nz + 2 * nw;
    }
    zw
}


/// Generic 4-way MDD walker. Walks from `nid` at `level` down to `depth`,
/// accumulating two bit-packed values (a_acc, b_acc) for branches (low bit, high bit).
/// Calls `emit(a_acc, b_acc, terminal_nid)` at terminal depth.
/// When a LEAF sentinel is reached before depth, enumerates all remaining branches.
pub(crate) fn walk_mdd_4way(
    nid: u32, level: usize, depth: usize,
    a_acc: u32, b_acc: u32,
    pos_order: &[usize], nodes: &[[u32; 4]],
    emit: &mut impl FnMut(u32, u32, u32),
) {
    if nid == mdd_reorder::DEAD { return; }
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
        if child == mdd_reorder::DEAD { continue; }
        let a_val = (branch >> 0) & 1;
        let b_val = (branch >> 1) & 1;
        walk_mdd_4way(child, level + 1, depth,
            a_acc | (a_val << pos), b_acc | (b_val << pos),
            pos_order, nodes, emit);
    }
}


pub(crate) fn walk_mdd_4way_leaf(
    level: usize, depth: usize,
    a_acc: u32, b_acc: u32,
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
        walk_mdd_4way_leaf(level + 1, depth,
            a_acc | (a_val << pos), b_acc | (b_val << pos),
            pos_order, emit);
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
                eprintln!("Loaded MDD from {} (k={}, {} nodes, {:.1} MB, {:.2e} live / {:.2e} total paths, {:.2e} live fraction)",
                    path, m.k, m.nodes.len(), m.nodes.len() as f64 * 16.0 / 1_048_576.0,
                    live, total, live_frac);
            }
            return Some(m);
        }
    }
    None
}


/// Unified pipeline work item. Priority = stage (higher = closer to result).
pub(crate) enum PipelineWork {
    /// Stage 0: Check boundary feasibility + extension filter → emit SolveW.
    Boundary(BoundaryWork),
    /// Stage 1: SAT-solve W given boundary + tuple. Enumerate W with blocking clauses.
    SolveW(SolveWWork),
    /// Stage 1 (alt): SAT-solve W+Z simultaneously in one call.
    SolveWZ(SolveWZWork),
    /// Stage 2: SAT-solve Z given boundary + W. Enumerate Z with blocking clauses.
    SolveZ(SolveZWork),
    /// Stage 3: run the XY SAT fast path for a fully-specified (Z, W)
    /// candidate. Cross mode's producer pushes these directly after
    /// Phase B enumeration + spectral pair filtering.
    SolveXY(SolveXYWork),
    Shutdown,
}


impl PipelineWork {
    pub(crate) fn stage(&self) -> u8 {
        match self {
            PipelineWork::Boundary(_) => 0,
            PipelineWork::SolveW(_) => 1,
            PipelineWork::SolveWZ(_) => 1,
            PipelineWork::SolveZ(_) => 2,
            PipelineWork::SolveXY(_) => 3,
            PipelineWork::Shutdown => 255,
        }
    }
}


pub(crate) struct BoundaryWork {
    pub(crate) z_bits: u32,
    pub(crate) w_bits: u32,
    pub(crate) xy_root: u32,
}


pub(crate) struct SolveWZWork {
    /// Representative tuple (for trace / cache keys).  The real candidate
    /// set is `candidate_tuples`.
    pub(crate) tuple: SumTuple,
    pub(crate) z_bits: u32,
    pub(crate) w_bits: u32,
    pub(crate) xy_root: u32,
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
    pub(crate) xy_root: u32,
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
    pub(crate) xy_root: u32,
    /// Tuples surviving the σ_W narrowing (|σ_W| of candidate matches
    /// the W the solver locked in).  The Z SAT is built with a
    /// `PbSetEq` over the union of their ±|σ_Z| counts.
    pub(crate) candidate_tuples: Vec<SumTuple>,
}


pub(crate) struct SolveXYWork {
    pub(crate) item: SatWorkItem,
}


/// Navigate the MDD to a specific (z_bits, w_bits) boundary, returning
/// the XY sub-root anchored at that boundary.  Returns `None` if the
/// boundary does not exist in the MDD (pruned away during gen).
pub(crate) fn mdd_navigate_to_outfix(
    root: u32, zw_depth: usize, pos_order: &[usize], nodes: &[[u32; 4]],
    z_bits: u32, w_bits: u32,
) -> Option<u32> {
    let mut nid = root;
    for level in 0..zw_depth {
        if nid == mdd_reorder::DEAD { return None; }
        let pos = pos_order[level];
        let z_bit = (z_bits >> pos) & 1;
        let w_bit = (w_bits >> pos) & 1;
        let branch = (z_bit | (w_bit << 1)) as usize;
        if nid != mdd_reorder::LEAF {
            nid = nodes[nid as usize][branch];
            if nid == mdd_reorder::DEAD { return None; }
        }
    }
    Some(nid)
}


/// Navigate the MDD along a deterministic path to reach one boundary.
/// Returns (z_bits, w_bits, xy_root) or None if the path hits DEAD.
pub(crate) fn mdd_navigate_path(
    root: u32, zw_depth: usize, path: u64,
    pos_order: &[usize], nodes: &[[u32; 4]],
) -> Option<(u32, u32, u32)> {
    let mut nid = root;
    let mut z_acc = 0u32;
    let mut w_acc = 0u32;
    for level in 0..zw_depth {
        if nid == mdd_reorder::DEAD { return None; }
        let branch = ((path >> (2 * level)) & 3) as usize;
        let pos = pos_order[level];
        z_acc |= ((branch & 1) as u32) << pos;
        w_acc |= (((branch >> 1) & 1) as u32) << pos;
        if nid != mdd_reorder::LEAF {
            nid = nodes[nid as usize][branch];
            if nid == mdd_reorder::DEAD { return None; }
        }
    }
    Some((z_acc, w_acc, nid))
}


/// Read-only context shared across all workers (via Arc). Populated
/// once in `run_mdd_sat_search` before spawning workers and read-only
/// thereafter.
pub(crate) struct PhaseBContext {
    pub(crate) mdd: Arc<mdd_reorder::Mdd4>,
    pub(crate) xy_pos_order: Vec<usize>,  // full pos_order for XY sub-MDD walk
    pub(crate) tuples: Vec<SumTuple>,
    pub(crate) w_tmpl: sat_z_middle::LagTemplate,
    pub(crate) z_tmpl: sat_z_middle::LagTemplate,
    pub(crate) problem: Problem,
    pub(crate) k: usize,
    pub(crate) zw_depth: usize,         // full 2*k — matches the MDD's ZW half depth
    pub(crate) xy_zw_depth: usize,      // full 2*k for XY sub-MDD walk
    pub(crate) middle_n: usize,
    pub(crate) middle_m: usize,
    pub(crate) max_bnd_sum: i32,
    pub(crate) max_z: usize,
    pub(crate) individual_bound: f64,
    pub(crate) pair_bound: f64,
    pub(crate) theta: usize,
    pub(crate) mdd_extend: usize,
    /// Use the combined SolveWZ stage instead of the default SolveW →
    /// SolveZ two-stage pipeline. Plumbed from cfg.wz_together.
    pub(crate) wz_together: bool,
    /// Prototype: replace the per-leaf walk_xy_sub_mdd fan-out with a
    /// single `try_candidate_via_mdd` call that uses radical's native
    /// `MddConstraint` propagator. Gated by env `XY_MDD=1`. Only the
    /// `--wz=apart` SolveZ stage is wired in this prototype.
    pub(crate) xy_mdd_mode: bool,
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



/// MDD pipeline search: unified priority queue with stages MDD→W→Z→XY.
/// All workers are identical — they grab the highest-stage item from the queue.
/// Later stages (closer to producing a result) always get processed first.
pub(crate) fn run_mdd_sat_search(
    problem: Problem,
    tuples: &[SumTuple],
    cfg: &SearchConfig,
    verbose: bool,
    k: usize,
) -> SearchReport {
    let n = problem.n;
    let m = problem.m();

    // --wz=sync: no pre-built MDD, no tuple enumeration. Walker runs the
    // full bouncing boundary DFS against a persistent SAT solver.
    if cfg.effective_wz_mode() == WzMode::Sync {
        let sync_cfg = crate::sync_walker::SyncConfig {
            sat_secs: cfg.sat_secs,
            sat_config: cfg.sat_config.clone(),
            conflict_limit: cfg.conflict_limit,
        };
        let _ = tuples;  // unused by sync
        let (found, stats, elapsed) = crate::sync_walker::search_sync(problem, &sync_cfg, verbose);
        if verbose {
            eprintln!(
                "\n--wz=sync: nodes={} memo_hits={} cap_rejects={} sat_unsat={} leaves={} elapsed={:?}",
                stats.nodes_visited, stats.memo_hits,
                stats.capacity_rejects, stats.sat_unsat, stats.leaves_reached, elapsed,
            );
        }
        if let Some((x, y, z, w)) = found.as_ref() {
            if verbose {
                println!("\nFOUND! x={} y={} z={} w={}",
                    colored_pm(x), colored_pm(y), colored_pm(z), colored_pm(w));
            }
        }
        return SearchReport {
            stats: SearchStats::default(),
            elapsed,
            found_solution: found.is_some(),
        };
    }

    let try_k = k.min((n - 1) / 2);
    let mdd = match load_best_mdd(try_k, verbose) {
        Some(m) => {
            if m.k != try_k {
                eprintln!("error: requested --mdd-k={} but only mdd-{}.bin found (k={})", k, m.k, m.k);
                eprintln!("Generate the exact MDD: target/release/gen_mdd {}", try_k);
                std::process::exit(1);
            }
            Arc::new(m)
        }
        None => {
            eprintln!("No MDD file found (tried mdd-1.bin through mdd-{}.bin)", try_k);
            eprintln!("Generate one with: cargo build --release --bin gen_mdd && target/release/gen_mdd {}", k);
            std::process::exit(1);
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
        for t in 0..k { v.push(t); v.push(2 * k - 1 - t); }
        v
    };

    // --wz=xyzw: skip the boundary→W→Z→XY pipeline entirely. Build a
    // single SAT problem covering all 4 sequences with the full ZW+XY
    // MDD as a native constraint, and solve once (or once per tuple if
    // --wz-xyzw-tuples=each).
    let early_wz_mode = cfg.effective_wz_mode();
    if early_wz_mode == WzMode::Xyzw {
        let run_start = Instant::now();
        let conflict_limit: u64 = cfg.conflict_limit;
        // Tuple control:
        //   --wz-xyzw-tuples=all     (default) — single solve, no sum PB;
        //     energy identity is implied by the Turyn quad PB. Any tuple
        //     found is accepted, with learnt clauses transferring across tuples.
        //   --wz-xyzw-tuples=each    — legacy loop, per-tuple sum PB.
        //     Useful for debugging or comparison.
        let tuple_mode = cfg.xyzw_tuple_mode.clone();
        if verbose {
            eprintln!("--wz=xyzw: mode={} {} tuples, k={} (depth={}) conflict_limit={}",
                tuple_mode, tuples.len(), k, mdd.depth, conflict_limit);
        }
        let mut found: Option<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)> = None;
        let mut total_decisions = 0u64;
        let mut total_propagations = 0u64;
        let sat_secs = cfg.sat_secs;
        if tuple_mode == "each" {
            for (i, &tuple) in tuples.iter().enumerate() {
                if sat_secs > 0 && run_start.elapsed().as_secs() >= sat_secs { break; }
                let (xyzw, stats) = solve_xyzw(
                    problem, Some(tuple), k, &mdd.nodes, mdd.root, mdd.depth,
                    &full_pos_order, &cfg.sat_config, &[], conflict_limit,
                );
                total_decisions += stats.decisions;
                total_propagations += stats.propagations;
                if verbose {
                    eprintln!("  tuple {}/{} {:?}: {} dec, {} prop, {}",
                        i + 1, tuples.len(), tuple, stats.decisions, stats.propagations,
                        if xyzw.is_some() { "SAT" } else { "UNSAT/timeout" });
                }
                if let Some((x, y, z, w)) = xyzw {
                    if verify_tt(problem, &x, &y, &z, &w) {
                        found = Some((x, y, z, w));
                        break;
                    } else if verbose {
                        eprintln!("    SAT but verify_tt failed for tuple {:?}", tuple);
                    }
                }
            }
        } else {
            // tuple_mode == "all": one solve covers all tuples.
            let (xyzw, stats) = solve_xyzw(
                problem, None, k, &mdd.nodes, mdd.root, mdd.depth,
                &full_pos_order, &cfg.sat_config, &[], conflict_limit,
            );
            total_decisions += stats.decisions;
            total_propagations += stats.propagations;
            if verbose {
                eprintln!("  all-tuples solve: {} dec, {} prop, {}",
                    stats.decisions, stats.propagations,
                    if xyzw.is_some() { "SAT" } else { "UNSAT/timeout" });
            }
            if let Some((x, y, z, w)) = xyzw {
                if verify_tt(problem, &x, &y, &z, &w) {
                    found = Some((x, y, z, w));
                } else if verbose {
                    eprintln!("    SAT but verify_tt failed — likely a solver bug");
                }
            }
        }
        let elapsed = run_start.elapsed();
        if verbose {
            println!("\n--wz=xyzw summary: {} total decisions, {} propagations, elapsed={:?}",
                total_decisions, total_propagations, elapsed);
        }
        let found_solution = found.is_some();
        if let Some((x, y, z, w)) = found {
            if verbose {
                println!("\nFOUND! x={} y={} z={} w={}",
                    colored_pm(&x), colored_pm(&y), colored_pm(&z), colored_pm(&w));
            }
        }
        return SearchReport {
            stats: SearchStats::default(),
            elapsed,
            found_solution,
        };
    }

    // Pull-based MDD feeding: monitor navigates paths on demand.
    let total_paths: u64 = 4u64.pow(zw_depth as u32);
    let lcg_mult: u64 = 0x5851F42D4C957F2D; // odd, full-period LCG for power-of-2
    let lcg_mask: u64 = total_paths - 1;
    let path_counter = std::sync::atomic::AtomicU64::new(0);

    // Count live ZW paths for progress estimation
    let live_zw_paths = {
        let mut memo = std::collections::HashMap::new();
        fn count_zw(nid: u32, level: usize, depth: usize, nodes: &[[u32; 4]],
                    memo: &mut std::collections::HashMap<u32, f64>) -> f64 {
            if nid == mdd_reorder::DEAD as u32 { return 0.0; }
            if nid == mdd_reorder::LEAF { return 4.0f64.powi((depth - level) as i32); }
            if level >= depth { return 1.0; }
            if let Some(&c) = memo.get(&nid) { return c; }
            let mut s = 0.0;
            for b in 0..4 { s += count_zw(nodes[nid as usize][b], level + 1, depth, nodes, memo); }
            memo.insert(nid, s);
            s
        }
        count_zw(mdd.root, 0, zw_depth, &mdd.nodes, &mut memo)
    };
    if verbose {
        eprintln!("  {:.0} live ZW paths of {} total ({:.4}% live)",
            live_zw_paths, total_paths, live_zw_paths / total_paths as f64 * 100.0);
    }

    // Shared read-only context for all workers
    let ctx = Arc::new(PhaseBContext {
        mdd: Arc::clone(&mdd),
        xy_pos_order: full_pos_order.clone(),
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
        // Cap Z enumeration per SolveZ item. The post-hoc FFT pair check
        // rejects >99.99% of Z solutions at small k; trying more than a
        // handful per item wastes SAT time without improving coverage.
        // Measured sweep at n=26 k=3 (boundaries walked in 20s):
        //   max_z=1:  14   max_z=10: 15   max_z=100: 11   max_z=200000: 9
        // A small cap lets workers move on to fresh (z_boundary, W) pairs
        // faster, which matters more than exhaustively enumerating Z for
        // one pair.
        // The cap used to be 1: old PbEq-based SolveZ happened to pick
        // a Z whose (Z, W) pair passed the external spectral filter by
        // luck of decision ordering.  Under PbSetEq the decision order
        // changes and 1 Z per pair isn't reliable — the in-SAT and
        // external spectral filters are on different frequency grids
        // by design, so the SAT may legitimately pick a Z that passes
        // its own in-SAT spectral but fails the external pair check.
        // Enumerate up to 16 Zs per (Z boundary, W middle) to recover.
        // User can still override via `--max-z`.
        max_z: cfg.max_z.min(16),
        individual_bound: problem.spectral_bound(),
        pair_bound: cfg.max_spectral.unwrap_or(problem.spectral_bound()),
        theta: cfg.theta_samples,
        mdd_extend: cfg.mdd_extend,
        wz_together: cfg.wz_together,
        xy_mdd_mode: std::env::var("XY_MDD").ok().as_deref() == Some("1"),
        w_mid_vars: (0..middle_m).map(|i| (i + 1) as i32).collect(),
        z_mid_vars: (0..middle_n).map(|i| (i + 1) as i32).collect(),
        z_spectral_tables: if middle_n >= 8 {
            Some(radical::SpectralTables::new(n, k, SPECTRAL_FREQS))
        } else { None },
        w_spectral_tables: if middle_m >= 8 {
            Some(radical::SpectralTables::new(m, k, SPECTRAL_FREQS))
        } else { None },
        found: Arc::new(AtomicBool::new(false)),
        outfix_xy: cfg.test_outfix.as_ref().and_then(|o| o.xy_bits),
        outfix_z_mid_pins: cfg.test_outfix.as_ref().map(|o| o.z_middle_pins.clone()).unwrap_or_default(),
        outfix_w_mid_pins: cfg.test_outfix.as_ref().map(|o| o.w_middle_pins.clone()).unwrap_or_default(),
        outfix_x_mid_pins: cfg.test_outfix.as_ref().map(|o| o.x_middle_pins.clone()).unwrap_or_default(),
        outfix_y_mid_pins: cfg.test_outfix.as_ref().map(|o| o.y_middle_pins.clone()).unwrap_or_default(),
    });

    let run_start = Instant::now();
    let workers = std::env::var("TURYN_THREADS")
        .ok().and_then(|s| s.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism()
            .map(|n| n.get()).unwrap_or(1).max(1));
    let sat_secs = cfg.sat_secs;

    if verbose {
        eprintln!("TT({}): MDD pipeline k={}, {} workers, 4^{}={:.0e} paths",
            n, k, workers, zw_depth, total_paths as f64);
    }

    // Shared priority queue: workers push and pop. Higher stage = higher priority.
    use std::collections::BinaryHeap;
    // Two-queue system:
    // - work: stages 0-2 (Boundary, SolveW, SolveZ) — higher stage first
    // - gold: stage 3 (SolveXY) — lower spectral power first (best candidates)
    // Workers check gold first; if empty, take from work to generate more gold.
    struct PqEntry { priority: f64, work: PipelineWork }
    impl PartialEq for PqEntry { fn eq(&self, o: &Self) -> bool { self.priority == o.priority } }
    impl Eq for PqEntry {}
    impl PartialOrd for PqEntry { fn partial_cmp(&self, o: &Self) -> Option<Ordering> { Some(self.cmp(o)) } }
    impl Ord for PqEntry {
        fn cmp(&self, o: &Self) -> Ordering {
            self.priority.partial_cmp(&o.priority).unwrap_or(Ordering::Equal)
        }
    }

    struct DualQueue {
        work: std::sync::Mutex<BinaryHeap<PqEntry>>,  // stages 0-2
        gold: std::sync::Mutex<BinaryHeap<PqEntry>>,  // stage 3, ranked by quality
        condvar: std::sync::Condvar,
        pair_bound: f64,
        best_quality: std::sync::atomic::AtomicU64,    // f64 bits of best quality seen
    }
    impl DualQueue {
        /// Push a non-XY work item with an explicit priority (e.g. for
        /// re-queued SolveWZ items that should sit below fresh work).
        fn push_with_priority(&self, item: PipelineWork, priority: f64) {
            self.work.lock().unwrap().push(PqEntry { priority, work: item });
            self.condvar.notify_one();
        }

        fn push(&self, item: PipelineWork) {
            match &item {
                PipelineWork::SolveXY(xy) => {
                    // Gold queue: lower spectral power = higher priority (inverted)
                    let quality = (1.0 - xy.item.priority / self.pair_bound.max(1.0)).max(0.0);
                    // Track best quality seen
                    let prev = f64::from_bits(self.best_quality.load(AtomicOrdering::Relaxed));
                    if quality > prev {
                        self.best_quality.store(quality.to_bits(), AtomicOrdering::Relaxed);
                    }
                    self.gold.lock().unwrap().push(PqEntry { priority: quality, work: item });
                }
                _ => {
                    let priority = item.stage() as f64;
                    self.work.lock().unwrap().push(PqEntry { priority, work: item });
                }
            }
            self.condvar.notify_one();
        }
        fn pop_blocking(&self, found: &AtomicBool, rng: &mut u64) -> Option<PipelineWork> {
            loop {
                if found.load(AtomicOrdering::Relaxed) { return None; }
                // Check gold queue: accept based on quality (weighted coinflip).
                // Top item has priority = quality (0.0 = bad, 1.0 = excellent).
                // Accept with probability = quality^2 (strongly favor the best).
                // If rejected, do work-queue stuff to generate more gold.
                {
                    let mut gq = self.gold.lock().unwrap();
                    if let Some(_top) = gq.peek() {
                        // Always accept if gold queue is well-stocked (>=100 items).
                        // If <100 items, 50/50 between processing and generating more.
                        let well_stocked = gq.len() >= 100;
                        let accept = well_stocked || {
                            *rng ^= *rng << 13; *rng ^= *rng >> 7; *rng ^= *rng << 17;
                            *rng & 1 == 0
                        };
                        if accept {
                            return Some(gq.pop().unwrap().work);
                        }
                    }
                }
                // Work queue (generate more gold candidates)
                if let Some(e) = self.work.lock().unwrap().pop() { return Some(e.work); }
                // Both empty or gold not accepted — wait briefly
                let guard = self.work.lock().unwrap();
                let (_guard, _) = self.condvar.wait_timeout(guard, std::time::Duration::from_millis(50)).unwrap();
            }
        }
        fn push_batch(&self, items: Vec<PipelineWork>) {
            if items.is_empty() { return; }
            // Separate gold (XY) vs work items
            let mut gold_items = Vec::new();
            let mut work_items = Vec::new();
            for item in items {
                match &item {
                    PipelineWork::SolveXY(xy) => {
                        let quality = (1.0 - xy.item.priority / self.pair_bound.max(1.0)).max(0.0);
                        let prev = f64::from_bits(self.best_quality.load(AtomicOrdering::Relaxed));
                        if quality > prev {
                            self.best_quality.store(quality.to_bits(), AtomicOrdering::Relaxed);
                        }
                        gold_items.push(PqEntry { priority: quality, work: item });
                    }
                    _ => {
                        let priority = item.stage() as f64;
                        work_items.push(PqEntry { priority, work: item });
                    }
                }
            }
            if !gold_items.is_empty() {
                let mut gq = self.gold.lock().unwrap();
                for e in gold_items { gq.push(e); }
            }
            if !work_items.is_empty() {
                let mut wq = self.work.lock().unwrap();
                for e in work_items { wq.push(e); }
            }
            self.condvar.notify_all();
        }
        fn gold_len(&self) -> usize { self.gold.lock().unwrap().len() }
        fn work_len(&self) -> usize { self.work.lock().unwrap().len() }
    }

    let work_queue = Arc::new(DualQueue {
        work: std::sync::Mutex::new(BinaryHeap::new()),
        gold: std::sync::Mutex::new(BinaryHeap::new()),
        condvar: std::sync::Condvar::new(),
        pair_bound: ctx.pair_bound,
        best_quality: std::sync::atomic::AtomicU64::new(0.0f64.to_bits()),
    });
    let (result_tx, result_rx) =
        std::sync::mpsc::channel::<(PackedSeq, PackedSeq, PackedSeq, PackedSeq)>();

    // Shared counters
    let items_completed = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let boundaries_walked = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let extensions_pruned = Arc::new(std::sync::atomic::AtomicU64::new(0));
    // SolveXY items currently being processed by a worker (not sub-candidate walks).
    // Used by cross mode to detect completion: when the producer has
    // enumerated every tuple and this counter is zero with both queues
    // empty, the pipeline is drained.
    let xy_item_in_flight = Arc::new(std::sync::atomic::AtomicU64::new(0));
    // Pipeline flow counters for Sankey visualization
    let flow_bnd_sum_fail = Arc::new(std::sync::atomic::AtomicU64::new(0));      // boundaries failing sum feasibility
    let flow_w_unsat = Arc::new(std::sync::atomic::AtomicU64::new(0));            // W SAT: no solutions found
    let flow_w_solutions = Arc::new(std::sync::atomic::AtomicU64::new(0));        // W solutions found (pre-spectral)
    let flow_w_spec_fail = Arc::new(std::sync::atomic::AtomicU64::new(0));        // W solutions failing spectral
    let flow_w_spec_pass = Arc::new(std::sync::atomic::AtomicU64::new(0));        // W solutions passing spectral → SolveZ
    let flow_z_unsat = Arc::new(std::sync::atomic::AtomicU64::new(0));            // Z SAT: no solutions found
    let flow_z_solutions = Arc::new(std::sync::atomic::AtomicU64::new(0));        // Z solutions found (pre-spectral)
    let flow_z_spec_fail = Arc::new(std::sync::atomic::AtomicU64::new(0));        // Z solutions failing individual spectral
    let flow_z_pair_fail = Arc::new(std::sync::atomic::AtomicU64::new(0));        // Z solutions failing pair check
    let flow_z_prep_fail = Arc::new(std::sync::atomic::AtomicU64::new(0));        // Z solutions failing prepare_candidate (infeasible/GJ)
    let flow_xy_ext_pruned = Arc::new(std::sync::atomic::AtomicU64::new(0));      // XY candidates pruned by extension
    let flow_xy_sat = Arc::new(std::sync::atomic::AtomicU64::new(0));             // XY SAT result = SAT
    let flow_xy_unsat = Arc::new(std::sync::atomic::AtomicU64::new(0));           // XY SAT result = UNSAT (proved)
    let flow_xy_timeout = Arc::new(std::sync::atomic::AtomicU64::new(0));         // XY SAT result = None (conflict limit)
    // Per-stage SAT search stats: aggregate decisions/propagations/forced/free over all solves.
    // Incremented by workers via diffing radical::Solver counters before/after each solve.
    let flow_w_solves = Arc::new(std::sync::atomic::AtomicU64::new(0));           // count of W SAT solves
    let flow_w_decisions = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let flow_w_propagations = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let flow_w_root_forced = Arc::new(std::sync::atomic::AtomicU64::new(0));      // sum of vars newly forced at level 0
    let flow_w_free_sum = Arc::new(std::sync::atomic::AtomicU64::new(0));         // sum of "free vars after forcing"
    let flow_z_solves = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let flow_z_decisions = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let flow_z_propagations = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let flow_z_root_forced = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let flow_z_free_sum = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let flow_xy_solves = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let flow_xy_decisions = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let flow_xy_propagations = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let flow_xy_root_forced = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let flow_xy_free_sum = Arc::new(std::sync::atomic::AtomicU64::new(0));
    // Sum of `cover_frac × 1_000_000` across XY timeout solves only.
    // Used to derive effective coverage from aggregate counters in the TTC
    // formula: a timeout that explored fraction f contributes f instead of 1.0
    // to the boundary's coverage. (W and Z solves don't time out today, so
    // partial-credit machinery applies only to XY.)
    let flow_xy_timeout_cov_micro = Arc::new(std::sync::atomic::AtomicU64::new(0));
    // SolveWZ-specific flow counters: diagnose where combined WZ items are lost.
    let flow_wz_empty_v = Arc::new(std::sync::atomic::AtomicU64::new(0));           // V_w or V_z was empty
    let flow_wz_rule_viol = Arc::new(std::sync::atomic::AtomicU64::new(0));         // rule (iv)/(v) violated at boundary
    let flow_wz_sat_calls = Arc::new(std::sync::atomic::AtomicU64::new(0));         // number of solver.solve() calls
    let flow_wz_first_unsat = Arc::new(std::sync::atomic::AtomicU64::new(0));       // first solve returned UNSAT (no (W,Z) at all)
    let flow_wz_solutions = Arc::new(std::sync::atomic::AtomicU64::new(0));         // WZ pairs produced (total, across enum)
    let flow_wz_exhausted = Arc::new(std::sync::atomic::AtomicU64::new(0));         // SolveWZ attempts that ran to SAT-UNSAT (not budget-hit)
    let flow_wz_budget_hit = Arc::new(std::sync::atomic::AtomicU64::new(0));        // SolveWZ attempts whose solve() returned None (conflict-limit)
    // Per-stage enter/exit counters: depth = enter - exit.
    let stage_enter: [Arc<std::sync::atomic::AtomicU64>; 4] = std::array::from_fn(|_| Arc::new(std::sync::atomic::AtomicU64::new(0)));
    let stage_exit: [Arc<std::sync::atomic::AtomicU64>; 4] = std::array::from_fn(|_| Arc::new(std::sync::atomic::AtomicU64::new(0)));
    // Count of Boundary items pending in the work queue OR being processed
    // by a worker (not yet converted to SolveW/SolveWZ).  Used by the MDD
    // walker to throttle the push rate — without this it'd either flood
    // the queue upfront (memory) or (worse) stall when the queue fills
    // with deferred re-queued SolveWZ items at negative priority, never
    // making room for fresh boundaries.
    let pending_boundaries = Arc::new(std::sync::atomic::AtomicU64::new(0));

    let sat_config = cfg.sat_config.clone();
    // SAT config: use defaults (EMA restarts/vivification/chrono BT tested and regressed)

    // No seed — monitor feeds MDD boundaries inline on demand.

    // Spawn workers — all identical, they grab highest-stage item
    let mut handles = Vec::new();
    for tid in 0..workers {
        let ctx = Arc::clone(&ctx);
        let wq = Arc::clone(&work_queue);
        let result_tx = result_tx.clone();
        let items_completed = Arc::clone(&items_completed);
        let _boundaries_walked = Arc::clone(&boundaries_walked);
        let extensions_pruned = Arc::clone(&extensions_pruned);
        let xy_item_in_flight = Arc::clone(&xy_item_in_flight);
        let flow_bnd_sum_fail = Arc::clone(&flow_bnd_sum_fail);
        let flow_w_unsat = Arc::clone(&flow_w_unsat);
        let flow_w_solutions = Arc::clone(&flow_w_solutions);
        let flow_w_spec_fail = Arc::clone(&flow_w_spec_fail);
        let flow_w_spec_pass = Arc::clone(&flow_w_spec_pass);
        let flow_z_unsat = Arc::clone(&flow_z_unsat);
        let flow_z_solutions = Arc::clone(&flow_z_solutions);
        let flow_z_spec_fail = Arc::clone(&flow_z_spec_fail);
        let flow_z_pair_fail = Arc::clone(&flow_z_pair_fail);
        let flow_z_prep_fail = Arc::clone(&flow_z_prep_fail);
        let _flow_xy_ext_pruned = Arc::clone(&flow_xy_ext_pruned);
        let flow_xy_sat = Arc::clone(&flow_xy_sat);
        let flow_xy_unsat = Arc::clone(&flow_xy_unsat);
        let flow_xy_timeout = Arc::clone(&flow_xy_timeout);
        let flow_w_solves = Arc::clone(&flow_w_solves);
        let flow_w_decisions = Arc::clone(&flow_w_decisions);
        let flow_w_propagations = Arc::clone(&flow_w_propagations);
        let flow_w_root_forced = Arc::clone(&flow_w_root_forced);
        let flow_w_free_sum = Arc::clone(&flow_w_free_sum);
        let flow_z_solves = Arc::clone(&flow_z_solves);
        let flow_z_decisions = Arc::clone(&flow_z_decisions);
        let flow_z_propagations = Arc::clone(&flow_z_propagations);
        let flow_z_root_forced = Arc::clone(&flow_z_root_forced);
        let flow_z_free_sum = Arc::clone(&flow_z_free_sum);
        let flow_xy_solves = Arc::clone(&flow_xy_solves);
        let flow_xy_decisions = Arc::clone(&flow_xy_decisions);
        let flow_xy_propagations = Arc::clone(&flow_xy_propagations);
        let flow_xy_root_forced = Arc::clone(&flow_xy_root_forced);
        let flow_xy_free_sum = Arc::clone(&flow_xy_free_sum);
        let flow_xy_timeout_cov_micro = Arc::clone(&flow_xy_timeout_cov_micro);
        let flow_wz_empty_v = Arc::clone(&flow_wz_empty_v);
        let flow_wz_rule_viol = Arc::clone(&flow_wz_rule_viol);
        let flow_wz_sat_calls = Arc::clone(&flow_wz_sat_calls);
        let flow_wz_first_unsat = Arc::clone(&flow_wz_first_unsat);
        let flow_wz_solutions = Arc::clone(&flow_wz_solutions);
        let flow_wz_exhausted = Arc::clone(&flow_wz_exhausted);
        let flow_wz_budget_hit = Arc::clone(&flow_wz_budget_hit);
        let stage_enter: Vec<_> = stage_enter.iter().map(Arc::clone).collect();
        let stage_exit: Vec<_> = stage_exit.iter().map(Arc::clone).collect();
        let pending_boundaries = Arc::clone(&pending_boundaries);
        let sat_config = sat_config.clone();

        handles.push(std::thread::spawn(move || {
            // Keyed by the sorted tuple list (each entry = signed tuple);
            // templates differ only in their `V_x`/`V_y` PbSetEq values,
            // which are derived from this list.
            let mut template_cache: HashMap<Vec<(i32, i32, i32, i32)>, SatXYTemplate> = HashMap::new();
            let mut warm = WarmStartState { phase: None, inject_phase: true };
            let mut w_bases: HashMap<i32, radical::Solver> = HashMap::new();
            let mut z_bases: HashMap<i32, radical::Solver> = HashMap::new();
            let mut ext_cache: HashMap<u128, bool> = HashMap::new();
            let spectral_w = SpectralFilter::new(ctx.problem.m(), ctx.theta);
            let spectral_z = SpectralFilter::new(ctx.problem.n, ctx.theta);
            let mut fft_buf_w = FftScratch::new(&spectral_w);
            let mut fft_buf_z = FftScratch::new(&spectral_z);
            // Reusable spectrum output buffer for the post-hoc Z pair check.
            // Avoids allocating a fresh Vec<f64> per Z solution.
            let mut z_spectrum_buf: Vec<f64> = Vec::new();
            // Single-slot cache for the z_boundary-dependent fill prep.
            // SolveZ items that share z_bits (all items from the same SolveW
            // batch) reuse this precomputed per-lag data: agree_const + the
            // lits_a/lits_b/coeffs templates. On a cache miss we rebuild in
            // place — reusing the per-lag Vec allocations so a miss is not
            // more expensive than the old per-item fill path.
            let mut z_prep = sat_z_middle::ZBoundaryPrep::with_template(&ctx.z_tmpl);
            let mut z_prep_z_bits: Option<u32> = None;
            // Also cache the z_boundary DFT at the SAT frequency grid
            // alongside the prep. Recomputing it per SolveZ item loops over
            // (2k boundary positions × num_freqs) — not huge, but it's also
            // not changing across the SolveW's batch. The cache key is the
            // same z_bits used for `z_prep`.
            let nf_z = ctx.z_spectral_tables.as_ref().map(|t| t.num_freqs).unwrap_or(0);
            let mut z_re_boundary: Vec<f64> = vec![0.0; nf_z];
            let mut z_im_boundary: Vec<f64> = vec![0.0; nf_z];
            let mut rng: u64 = 0x517cc1b727220a95 ^ (tid as u64 * 0x9e3779b97f4a7c15);
            macro_rules! next_rng { () => {{ rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; rng }} }
            let k = ctx.k;
            let n = ctx.problem.n;
            let m = ctx.problem.m();
            let use_wz_mode = ctx.wz_together;

            loop {
                let Some(work) = wq.pop_blocking(&ctx.found, &mut rng) else { break; };
                if ctx.found.load(AtomicOrdering::Relaxed) { break; }
                if matches!(work, PipelineWork::Shutdown) { break; }

                match work {
                    PipelineWork::Boundary(bnd) => {
                        // TRACE: check if this is the known solution's boundary
                        let trace_bnd = bnd.z_bits == 43 && bnd.w_bits == 47;
                        if trace_bnd { eprintln!("TRACE: found target boundary z=43 w=47 xy_root={}", bnd.xy_root); }
                        // Boundary dequeued — the walker is free to push another.
                        pending_boundaries.fetch_sub(1, AtomicOrdering::Relaxed);
                        // Check sum feasibility for each tuple, emit SolveW items
                        let z_bnd_sum = 2 * (bnd.z_bits.count_ones() as i32) - ctx.max_bnd_sum;
                        let w_bnd_sum = 2 * (bnd.w_bits.count_ones() as i32) - ctx.max_bnd_sum;
                        // Collect all tuples this boundary is compatible with
                        // (at least one sign of σ_W, σ_Z in range + right parity,
                        // and the XY sub-MDD has a matching leaf).  Emit ONE
                        // SolveW (or SolveWZ) carrying the whole candidate
                        // list — the stage builds V_w as the union of
                        // ±|σ_W|-counts over candidate tuples and lets the
                        // SAT pick any of them.  Downstream stages narrow
                        // the list by the decoded σ.
                        let mut candidate_tuples: Vec<SumTuple> = Vec::with_capacity(ctx.tuples.len());
                        for &tuple in &ctx.tuples {
                            // Both ±|σ_W|, ±|σ_Z| allowed — feasible if AT
                            // LEAST ONE sign of each is in range and parity.
                            let z_feas = [tuple.z.abs(), -tuple.z.abs()].iter().any(|&s| {
                                sigma_full_to_cnt(s, z_bnd_sum, ctx.middle_n).is_some()
                            });
                            let w_feas = [tuple.w.abs(), -tuple.w.abs()].iter().any(|&s| {
                                sigma_full_to_cnt(s, w_bnd_sum, ctx.middle_m).is_some()
                            });
                            if !z_feas || !w_feas {
                                flow_bnd_sum_fail.fetch_add(1, AtomicOrdering::Relaxed); continue;
                            }
                            // MDD-guided fail-fast on XY sub-tree compatibility.
                            if !any_valid_xy(
                                bnd.xy_root, 0, ctx.xy_zw_depth, 0, 0,
                                &ctx.xy_pos_order, &ctx.mdd.nodes,
                                ctx.max_bnd_sum, ctx.middle_n as i32, tuple,
                            ) {
                                flow_bnd_sum_fail.fetch_add(1, AtomicOrdering::Relaxed);
                                continue;
                            }
                            candidate_tuples.push(tuple);
                        }
                        if candidate_tuples.is_empty() {
                            stage_exit[0].fetch_add(1, AtomicOrdering::Relaxed);
                            continue;
                        }
                        // Use the first candidate as the representative for
                        // legacy fields (z_mid_sum, w_mid_sum, tuple).
                        let rep = candidate_tuples[0];
                        stage_enter[1].fetch_add(1, AtomicOrdering::Relaxed);
                        let work = if use_wz_mode {
                            PipelineWork::SolveWZ(SolveWZWork {
                                tuple: rep, z_bits: bnd.z_bits, w_bits: bnd.w_bits,
                                xy_root: bnd.xy_root,
                                candidate_tuples,
                                attempt: 0,
                                prior_blocks: Vec::new(),
                            })
                        } else {
                            PipelineWork::SolveW(SolveWWork {
                                tuple: rep, z_bits: bnd.z_bits, w_bits: bnd.w_bits,
                                xy_root: bnd.xy_root,
                                candidate_tuples,
                            })
                        };
                        if trace_bnd { eprintln!("TRACE: emitting ONE SolveW for canonical TT(18) boundary"); }
                        wq.push_batch(vec![work]);
                        stage_exit[0].fetch_add(1, AtomicOrdering::Relaxed);
                    }

                    PipelineWork::SolveW(sw) => {
                        let trace_w = sw.z_bits == 43 && sw.w_bits == 47 && sw.tuple.z == 8 && sw.tuple.w == 1;
                        if trace_w { eprintln!("TRACE: SolveW for target boundary, |σ_W|={}", sw.tuple.w); }
                        let (w_prefix, w_suffix) = expand_boundary_bits(sw.w_bits, k);
                        let mut w_boundary = vec![0i8; m];
                        w_boundary[..k].copy_from_slice(&w_prefix);
                        w_boundary[m-k..].copy_from_slice(&w_suffix);

                        // BDKR rule (v) boundary pre-filter.  Skip this
                        // SolveW if the W boundary already fails rule (v).
                        let rule_v_state = sat_z_middle::check_w_boundary_rule_v(m, k, &w_boundary);
                        if rule_v_state == sat_z_middle::BoundaryRuleState::ViolatedAtBoundary {
                            continue;
                        }

                        // Compute V_w = union over `sw.candidate_tuples` of
                        // {cnt(+|σ_W|), cnt(-|σ_W|)}.  One SAT call per
                        // boundary finds any W middle landing on any valid
                        // σ_W — the decoded count then narrows the tuple
                        // list for SolveZ.
                        let w_bnd_sum_local: i32 = w_boundary.iter().map(|&v| v as i32).sum();
                        let w_counts: Vec<u32> = {
                            let mut cs: Vec<u32> = Vec::new();
                            for t in &sw.candidate_tuples {
                                let abs_w = t.w.abs();
                                let signs: &[i32] = if abs_w == 0 { &[0] } else { &[1, -1] };
                                for &sg in signs {
                                    if let Some(c) = sigma_full_to_cnt(sg * abs_w, w_bnd_sum_local, ctx.middle_m) {
                                        if !cs.contains(&c) { cs.push(c); }
                                    }
                                }
                            }
                            cs.sort_unstable();
                            cs
                        };
                        if w_counts.is_empty() {
                            stage_exit[1].fetch_add(1, AtomicOrdering::Relaxed);
                            continue;
                        }

                        // For small middle: brute-force W enumeration (proven to find solutions).
                        // For large middle: SAT-based W generation (handles big search spaces).
                        let mut w_found_any = false;
                        let mut trace_w_total = 0u64;
                        let mut trace_w_pass = 0u64;
                        if ctx.middle_m <= 20 {
                            // Collect all passing W candidates into a batch so we push
                            // them to the queue with a single lock. This eliminates
                            // per-W mutex contention when middle_m is small and many
                            // W candidates pass the spectral filter.
                            let mut batch: Vec<PipelineWork> = Vec::new();
                            // Reusable spectrum buffer; we only materialize an
                            // owned Vec at push time, so failed candidates (~85%)
                            // never allocate a Vec<f64>.
                            let mut spec_buf: Vec<f64> = Vec::new();
                            // Iterate each count in V_w (one per feasible sign of σ_W).
                            // generate_sequences_permuted takes a signed mid_sum
                            // target — decode it from the count as 2·cnt − middle_m.
                            for &cnt in &w_counts {
                              let mid_sum_iter = 2 * cnt as i32 - ctx.middle_m as i32;
                              generate_sequences_permuted(ctx.middle_m, mid_sum_iter, false, false, 200_000, |w_mid| {
                                if ctx.found.load(AtomicOrdering::Relaxed) { return false; }
                                let mut w_vals = w_boundary.clone();
                                w_vals[k..k+ctx.middle_m].copy_from_slice(w_mid);
                                flow_w_solutions.fetch_add(1, AtomicOrdering::Relaxed);
                                if trace_w { trace_w_total += 1; }
                                // BDKR rule (v): check the full W sequence.
                                // `check_w_boundary_rule_v` works for any
                                // prefix extent; using the full m here
                                // catches violations in the middle too.
                                if sat_z_middle::check_w_boundary_rule_v(m, m, &w_vals)
                                    == sat_z_middle::BoundaryRuleState::ViolatedAtBoundary
                                {
                                    return true; // skip non-canonical w_mid
                                }
                                if spectrum_into_if_ok(&w_vals, &spectral_w, ctx.individual_bound, &mut fft_buf_w, &mut spec_buf) {
                                    if trace_w { trace_w_pass += 1; }
                                    flow_w_spec_pass.fetch_add(1, AtomicOrdering::Relaxed);
                                    w_found_any = true;
                                    // Decode σ_W and narrow the tuple list.
                                    let sigma_w_full: i32 = w_vals.iter().map(|&v| v as i32).sum();
                                    let narrowed: Vec<SumTuple> = sw.candidate_tuples.iter()
                                        .copied()
                                        .filter(|t| t.w.abs() == sigma_w_full.abs())
                                        .collect();
                                    if narrowed.is_empty() { return true; }
                                    stage_enter[2].fetch_add(1, AtomicOrdering::Relaxed);
                                    let rep = narrowed[0];
                                    batch.push(PipelineWork::SolveZ(SolveZWork {
                                        tuple: rep, z_bits: sw.z_bits, w_bits: sw.w_bits,
                                        w_vals, w_spectrum: spec_buf.clone(), xy_root: sw.xy_root,
                                        candidate_tuples: narrowed,
                                    }));
                                } else {
                                    flow_w_spec_fail.fetch_add(1, AtomicOrdering::Relaxed);
                                }
                                true
                              });
                            } // end for &cnt
                            if !batch.is_empty() {
                                wq.push_batch(batch);
                            }
                        } else {
                            // SAT-based W generation.  Build with a PbSetEq
                            // so the SAT may pick any count in V_w (i.e.,
                            // either sign of σ_W).  Cache key is 0 — we
                            // don't reuse the solver across boundaries
                            // because V_w depends on the boundary.
                            let mut w_solver = w_bases.remove(&0i32).unwrap_or_else(||
                                ctx.w_tmpl.build_base_solver_pb_set(ctx.middle_m, &w_counts)
                            );
                            let w_cp = w_solver.save_checkpoint();
                            sat_z_middle::fill_w_solver(&mut w_solver, &ctx.w_tmpl, m, &w_boundary);
                            // Rule (v) middle clauses when boundary left
                            // the rule DeferredToMiddle.
                            if rule_v_state == sat_z_middle::BoundaryRuleState::DeferredToMiddle {
                                let mut nv = (w_solver.num_vars() + 1) as i32;
                                sat_z_middle::add_rule_v_middle_clauses(
                                    &mut w_solver, m, k, &w_boundary,
                                    |pf| (pf - k + 1) as i32,
                                    &mut nv,
                                );
                            }
                            if let Some(ref wtab) = ctx.w_spectral_tables {
                                w_solver.spectral = Some(radical::SpectralConstraint::from_tables(
                                    wtab, &w_boundary, ctx.individual_bound,
                                ));
                            }

                            // Snapshot solver search stats before the enumeration
                            // loop. We diff against post-loop values to get this
                            // boundary's contribution to the W-stage diagnostics
                            // (decisions, propagations, level-0 forced, free vars).
                            let w_d0 = w_solver.num_decisions();
                            let w_p0 = w_solver.num_propagations();
                            let w_l0 = w_solver.num_level0_vars();
                            let w_nv = w_solver.num_vars();

                            // Collect passing W candidates into a batch to reduce
                            // queue lock contention, same as the brute-force path above.
                            let mut batch: Vec<PipelineWork> = Vec::new();
                            loop {
                                if ctx.found.load(AtomicOrdering::Relaxed) { break; }
                                let phases: Vec<bool> = (0..ctx.middle_m)
                                    .map(|_| next_rng!() & 1 == 1).collect();
                                w_solver.set_phase(&phases);
                                if w_solver.solve() != Some(true) { break; }
                                flow_w_solutions.fetch_add(1, AtomicOrdering::Relaxed);

                                let w_mid = extract_vals(&w_solver, |i| ctx.w_mid_vars[i], ctx.middle_m);
                                let mut w_vals = w_boundary.clone();
                                w_vals[k..k+ctx.middle_m].copy_from_slice(&w_mid);

                                let w_block: Vec<i32> = ctx.w_mid_vars.iter().map(|&v| {
                                    if w_solver.value(v) == Some(true) { -v } else { v }
                                }).collect();
                                w_solver.reset(); // backtrack before blocking clause
                                w_solver.add_clause(w_block);

                                let w_spectrum = match spectrum_if_ok(&w_vals, &spectral_w, ctx.individual_bound, &mut fft_buf_w) {
                                    Some(s) => s,
                                    None => {
                                        flow_w_spec_fail.fetch_add(1, AtomicOrdering::Relaxed);
                                        if std::env::var("TRACE_SPEC").is_ok() && flow_w_spec_fail.load(AtomicOrdering::Relaxed) <= 3 {
                                            // Direct re-compute both: in-SAT-style DFT on the full W
                                            // and external FFT, report peak |W|² at aligned ω.
                                            let mut external = vec![0.0; 129];
                                            compute_spectrum_into(&w_vals, &spectral_w, &mut fft_buf_w, &mut external);
                                            use std::f64::consts::PI;
                                            let mut insat = vec![0.0; 129];
                                            for fi in 0..129 {
                                                let om = fi as f64 * PI / 128.0;
                                                let mut re = 0.0; let mut im = 0.0;
                                                for (pos, &wv) in w_vals.iter().enumerate() {
                                                    re += wv as f64 * (om * pos as f64).cos();
                                                    im += wv as f64 * (om * pos as f64).sin();
                                                }
                                                insat[fi] = re*re + im*im;
                                            }
                                            let max_ext = external.iter().cloned().fold(0.0, f64::max);
                                            let max_ins = insat.iter().cloned().fold(0.0, f64::max);
                                            let ext_violating: Vec<usize> = (0..129).filter(|&i| external[i] > ctx.individual_bound).collect();
                                            eprintln!("[TRACE_SPEC] W failed: {} chars, max_ext={:.4}, max_insat={:.4}, bound={:.1}",
                                                w_vals.iter().map(|&v| if v>0 {'+'} else {'-'}).collect::<String>(),
                                                max_ext, max_ins, ctx.individual_bound);
                                            eprintln!("  external violates at bins: {:?}", ext_violating);
                                            for &fi in ext_violating.iter().take(3) {
                                                eprintln!("  bin {fi} (ω={:.4}π): external={:.4}, in-SAT-style={:.4}",
                                                    fi as f64 / 128.0, external[fi], insat[fi]);
                                            }
                                        }
                                        continue;
                                    }
                                };
                                flow_w_spec_pass.fetch_add(1, AtomicOrdering::Relaxed);
                                w_found_any = true;

                                let sigma_w_full: i32 = w_vals.iter().map(|&v| v as i32).sum();
                                let narrowed: Vec<SumTuple> = sw.candidate_tuples.iter()
                                    .copied()
                                    .filter(|t| t.w.abs() == sigma_w_full.abs())
                                    .collect();
                                if narrowed.is_empty() { continue; }
                                stage_enter[2].fetch_add(1, AtomicOrdering::Relaxed);
                                let rep = narrowed[0];
                                batch.push(PipelineWork::SolveZ(SolveZWork {
                                    tuple: rep, z_bits: sw.z_bits, w_bits: sw.w_bits,
                                    w_vals, w_spectrum, xy_root: sw.xy_root,
                                    candidate_tuples: narrowed,
                                }));
                            }
                            if !batch.is_empty() {
                                wq.push_batch(batch);
                            }

                            // Aggregate W-stage SAT search stats for this boundary.
                            // Record level-0 forced count from the pre-solve snapshot
                            // (constraint propagation pruning) — this is what gets
                            // displayed as "vars forced before SAT runs".
                            let w_decisions    = w_solver.num_decisions().saturating_sub(w_d0);
                            let w_propagations = w_solver.num_propagations().saturating_sub(w_p0);
                            let w_pre_forced   = w_l0 as u64;
                            let w_free_vars    = w_nv.saturating_sub(w_l0) as u64;
                            flow_w_solves.fetch_add(1, AtomicOrdering::Relaxed);
                            flow_w_decisions.fetch_add(w_decisions, AtomicOrdering::Relaxed);
                            flow_w_propagations.fetch_add(w_propagations, AtomicOrdering::Relaxed);
                            flow_w_root_forced.fetch_add(w_pre_forced, AtomicOrdering::Relaxed);
                            flow_w_free_sum.fetch_add(w_free_vars, AtomicOrdering::Relaxed);

                            w_solver.spectral = None;
                            w_solver.restore_checkpoint(w_cp);
                            w_bases.insert(0i32, w_solver);
                        }
                        if !w_found_any { flow_w_unsat.fetch_add(1, AtomicOrdering::Relaxed); }
                        if trace_w { eprintln!("TRACE: SolveW done: {} W middles checked, {} passed spectral", trace_w_total, trace_w_pass); }
                        stage_exit[1].fetch_add(1, AtomicOrdering::Relaxed);
                    }

                    PipelineWork::SolveWZ(swz) => {
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
                        w_boundary[m-k..].copy_from_slice(&w_suffix);
                        let mut z_boundary = vec![0i8; n];
                        for i in 0..k {
                            z_boundary[i] = if (swz.z_bits >> i) & 1 == 1 { 1 } else { -1 };
                            z_boundary[n-k+i] = if (swz.z_bits >> (k+i)) & 1 == 1 { 1 } else { -1 };
                        }

                        // Sum constraints via PbSetEq: union of ±|σ_W| (resp. ±|σ_Z|)
                        // counts across all `candidate_tuples`.
                        let w_bnd_sum_local: i32 = w_boundary.iter().map(|&v| v as i32).sum();
                        let z_bnd_sum_local: i32 = z_boundary.iter().map(|&v| v as i32).sum();
                        let mut w_counts: Vec<u32> = Vec::new();
                        let mut z_counts: Vec<u32> = Vec::new();
                        for t in &swz.candidate_tuples {
                            let abs_w = t.w.abs();
                            for &sg in if abs_w == 0 { &[0i32] as &[i32] } else { &[1, -1] } {
                                if let Some(c) = sigma_full_to_cnt(sg * abs_w, w_bnd_sum_local, ctx.middle_m) {
                                    if !w_counts.contains(&c) { w_counts.push(c); }
                                }
                            }
                            let abs_z = t.z.abs();
                            for &sg in if abs_z == 0 { &[0i32] as &[i32] } else { &[1, -1] } {
                                if let Some(c) = sigma_full_to_cnt(sg * abs_z, z_bnd_sum_local, ctx.middle_n) {
                                    if !z_counts.contains(&c) { z_counts.push(c); }
                                }
                            }
                        }
                        w_counts.sort_unstable();
                        z_counts.sort_unstable();
                        if w_counts.is_empty() || z_counts.is_empty() {
                            flow_wz_empty_v.fetch_add(1, AtomicOrdering::Relaxed);
                            stage_exit[1].fetch_add(1, AtomicOrdering::Relaxed);
                            continue;
                        }
                        let w_lits: Vec<i32> = (0..ctx.middle_m).map(|i| w_var(i)).collect();
                        let z_lits: Vec<i32> = (0..ctx.middle_n).map(|i| z_var(i)).collect();
                        solver.add_pb_set_eq(&w_lits, &w_counts);
                        solver.add_pb_set_eq(&z_lits, &z_counts);

                        // BDKR rules (iv)/(v) boundary pre-filter.
                        let rule_iv_state = sat_z_middle::check_z_boundary_rule_iv(n, k, &z_boundary);
                        let rule_v_state  = sat_z_middle::check_w_boundary_rule_v(m, k, &w_boundary);
                        if rule_iv_state == sat_z_middle::BoundaryRuleState::ViolatedAtBoundary
                           || rule_v_state == sat_z_middle::BoundaryRuleState::ViolatedAtBoundary
                        {
                            flow_wz_rule_viol.fetch_add(1, AtomicOrdering::Relaxed);
                            stage_exit[1].fetch_add(1, AtomicOrdering::Relaxed);
                            continue;
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
                                &mut solver, n, k,
                                |jf| z_var(jf - k),
                                &mut nv_combined,
                            );
                        }
                        if rule_v_state == sat_z_middle::BoundaryRuleState::DeferredToMiddle {
                            sat_z_middle::add_rule_v_middle_clauses(
                                &mut solver, m, k, &w_boundary,
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
                                        if w_boundary[i] == w_boundary[j] { agree_const += 1; }
                                    }
                                    for &(bnd_pos, mid_idx) in &w_lag.bnd_mid {
                                        let lit = if w_boundary[bnd_pos] == 1 { w_var(mid_idx) } else { -w_var(mid_idx) };
                                        lits_a.push(lit);
                                        lits_b.push(true_var);
                                    }
                                    for &(i, j) in &w_lag.mid_mid {
                                        // agree(a,b) = (a AND b) OR (-a AND -b)
                                        lits_a.push( w_var(i)); lits_b.push( w_var(j));
                                        lits_a.push(-w_var(i)); lits_b.push(-w_var(j));
                                    }
                                }
                                // Z pairs
                                if s < n {
                                    let z_lag = &ctx.z_tmpl.lags[s - 1];
                                    for &(i, j) in &z_lag.bnd_bnd {
                                        if z_boundary[i] == z_boundary[j] { agree_const += 1; }
                                    }
                                    for &(bnd_pos, mid_idx) in &z_lag.bnd_mid {
                                        let lit = if z_boundary[bnd_pos] == 1 { z_var(mid_idx) } else { -z_var(mid_idx) };
                                        lits_a.push(lit);
                                        lits_b.push(true_var);
                                    }
                                    for &(i, j) in &z_lag.mid_mid {
                                        lits_a.push( z_var(i)); lits_b.push( z_var(j));
                                        lits_a.push(-z_var(i)); lits_b.push(-z_var(j));
                                    }
                                }

                                let max_variable = lits_a.len() as u32;
                                let adj_lo = combined_lo.saturating_sub(agree_const);
                                let adj_hi = combined_hi.saturating_sub(agree_const);
                                if adj_lo > max_variable { solver.add_clause(std::iter::empty::<i32>()); break; }
                                if adj_lo == 0 && adj_hi >= max_variable { continue; }
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
                                    if pos >= k && pos < m - k { continue; }
                                    let val = w_boundary[pos] as f64;
                                    re1_bnd[fi] += val * (omega * pos as f64).cos();
                                    im1_bnd[fi] += val * (omega * pos as f64).sin();
                                }
                                for pos in 0..n {
                                    if pos >= k && pos < n - k { continue; }
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
                                re: re_dummy.clone(), im: im_dummy.clone(),
                                re_boundary: re_dummy.clone(), im_boundary: im_dummy,
                                bound: ctx.problem.target_energy() as f64, // 6n-2: full energy budget for 2|W|²+2|Z|²+|X|²+|Y|²
                                per_freq_bound: None,
                                max_reduction: vec![0.0; nf],
                                amplitudes: std::sync::Arc::new(amplitudes),
                                assigned: vec![false; total_mid],
                                values: vec![0i8; total_mid],
                                seq2: Some(radical::Seq2Config {
                                    seq2_start: ctx.middle_m,
                                    weight1: 2.0, weight2: 2.0,
                                    individual_bound: ctx.individual_bound,
                                    re1: re1_bnd.clone(), im1: im1_bnd.clone(),
                                    re1_boundary: re1_bnd, im1_boundary: im1_bnd,
                                    max_reduction1: mr1,
                                    re2: re2_bnd.clone(), im2: im2_bnd.clone(),
                                    re2_boundary: re2_bnd, im2_boundary: im2_bnd,
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
                            if ctx.found.load(AtomicOrdering::Relaxed) { break; }
                            if wz_count >= ctx.max_z {
                                more_possible = true;
                                break;
                            }
                            // Random phases for both W and Z.  Mix the
                            // attempt number into the RNG so re-queued
                            // items explore a different region of the
                            // phase space than their first attempt.
                            let mut attempt_rng = rng ^ (swz.attempt as u64).wrapping_mul(0x9e3779b97f4a7c15);
                            let phases: Vec<bool> = (0..total_vars)
                                .map(|_| {
                                    attempt_rng ^= attempt_rng << 13;
                                    attempt_rng ^= attempt_rng >> 7;
                                    attempt_rng ^= attempt_rng << 17;
                                    attempt_rng & 1 == 1
                                }).collect();
                            rng = attempt_rng;
                            solver.set_phase(&phases);
                            flow_wz_sat_calls.fetch_add(1, AtomicOrdering::Relaxed);
                            let sat_res = solver.solve();
                            if sat_res == None {
                                // Conflict limit hit — more solutions may exist.
                                more_possible = true;
                                flow_wz_budget_hit.fetch_add(1, AtomicOrdering::Relaxed);
                                if wz_count == 0 {
                                    flow_wz_first_unsat.fetch_add(1, AtomicOrdering::Relaxed);
                                }
                                break;
                            }
                            if sat_res == Some(false) {
                                // Fully enumerated: every assignment has been
                                // blocked.  No point re-queuing.
                                flow_wz_exhausted.fetch_add(1, AtomicOrdering::Relaxed);
                                if wz_count == 0 {
                                    flow_wz_first_unsat.fetch_add(1, AtomicOrdering::Relaxed);
                                }
                                break;
                            }
                            wz_count += 1;
                            flow_wz_solutions.fetch_add(1, AtomicOrdering::Relaxed);

                            // Extract W middle
                            let w_mid: Vec<i8> = (0..ctx.middle_m).map(|i| {
                                if solver.value(w_var(i)).unwrap() { 1 } else { -1 }
                            }).collect();
                            let mut w_vals = w_boundary.clone();
                            w_vals[k..k+ctx.middle_m].copy_from_slice(&w_mid);

                            // Extract Z middle
                            let z_mid: Vec<i8> = (0..ctx.middle_n).map(|i| {
                                if solver.value(z_var(i)).unwrap() { 1 } else { -1 }
                            }).collect();
                            let mut z_vals = Vec::with_capacity(n);
                            z_vals.extend_from_slice(&z_boundary[..k]);
                            z_vals.extend_from_slice(&z_mid);
                            z_vals.extend_from_slice(&z_boundary[n-k..]);

                            // Block this (W,Z) pair.  Also stash the clause
                            // in new_blocks so it survives re-queue: the
                            // next attempt's fresh solver will re-add it
                            // together with swz.prior_blocks.
                            let block: Vec<i32> = (0..total_vars as i32 + 1).skip(1).map(|v| {
                                if solver.value(v) == Some(true) { -v } else { v }
                            }).collect();
                            solver.reset();
                            solver.add_clause(block.iter().copied());
                            new_blocks.push(block);

                            // Combined spectral in solver guarantees pair bound.
                            // Compute spectra only for downstream use.
                            let w_spectrum = compute_spectrum(&w_vals, &spectral_w, &mut fft_buf_w);
                            let _ = &w_spectrum; // used by pair_power below

                            // Got a valid (W,Z) pair — proceed to XY
                            flow_z_solutions.fetch_add(1, AtomicOrdering::Relaxed);
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
                            let mut tuple_key: Vec<(i32, i32, i32, i32)> = swz.candidate_tuples.iter()
                                .map(|t| (t.x, t.y, t.z, t.w)).collect();
                            tuple_key.sort_unstable();
                            let template = template_cache.entry(tuple_key).or_insert_with(||
                                SatXYTemplate::build_multi(problem, &swz.candidate_tuples, &sat_config).unwrap()
                            );
                            let candidate = CandidateZW { zw_autocorr };
                            if let Some(mut xy_solver) = template.prepare_candidate_solver(&candidate) {
                                if n > 30 { xy_solver.set_conflict_limit(5000); }
                                walk_xy_sub_mdd(
                                    swz.xy_root, 0, ctx.xy_zw_depth, 0, 0,
                                    &ctx.xy_pos_order, &ctx.mdd.nodes, ctx.max_bnd_sum,
                                    ctx.middle_n as i32, &swz.candidate_tuples,
                                    &mut |x_bits, y_bits| {
                                        if ctx.found.load(AtomicOrdering::Relaxed) { return; }
                                        if let Some((fx, fy)) = ctx.outfix_xy {
                                            if x_bits != fx || y_bits != fy { return; }
                                        }
                                        stage_enter[3].fetch_add(1, AtomicOrdering::Relaxed);
                                        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
                                        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };
                                        let mut assumptions = Vec::with_capacity(4 * k + ctx.outfix_x_mid_pins.len() + ctx.outfix_y_mid_pins.len());
                                        for i in 0..k {
                                            assumptions.push(if (x_bits >> i) & 1 == 1 { x_var(i) } else { -x_var(i) });
                                            assumptions.push(if (x_bits >> (k + i)) & 1 == 1 { x_var(n - k + i) } else { -x_var(n - k + i) });
                                            assumptions.push(if (y_bits >> i) & 1 == 1 { y_var(i) } else { -y_var(i) });
                                            assumptions.push(if (y_bits >> (k + i)) & 1 == 1 { y_var(n - k + i) } else { -y_var(n - k + i) });
                                        }
                                        // --outfix middle pins for X/Y: force middle positions too.
                                        for &(mid, val) in &ctx.outfix_x_mid_pins {
                                            if mid < ctx.middle_n {
                                                let lit = if val > 0 { x_var(k + mid) } else { -x_var(k + mid) };
                                                assumptions.push(lit);
                                            }
                                        }
                                        for &(mid, val) in &ctx.outfix_y_mid_pins {
                                            if mid < ctx.middle_n {
                                                let lit = if val > 0 { y_var(k + mid) } else { -y_var(k + mid) };
                                                assumptions.push(lit);
                                            }
                                        }
                                        // Snapshot search stats around the SAT call.
                                        let xy_d0 = xy_solver.num_decisions();
                                        let xy_p0 = xy_solver.num_propagations();
                                        let xy_l0 = xy_solver.num_level0_vars();
                                        let xy_nv = xy_solver.num_vars();
                                        let result = xy_solver.solve_with_assumptions(&assumptions);
                                        items_completed.fetch_add(1, AtomicOrdering::Relaxed);
                                        stage_exit[3].fetch_add(1, AtomicOrdering::Relaxed);

                                        let xy_decisions    = xy_solver.num_decisions().saturating_sub(xy_d0);
                                        let xy_propagations = xy_solver.num_propagations().saturating_sub(xy_p0);
                                        let xy_pre_forced   = xy_l0 as u64;
                                        let xy_free_vars    = xy_nv.saturating_sub(xy_l0) as u64;
                                        flow_xy_solves.fetch_add(1, AtomicOrdering::Relaxed);
                                        flow_xy_decisions.fetch_add(xy_decisions, AtomicOrdering::Relaxed);
                                        flow_xy_propagations.fetch_add(xy_propagations, AtomicOrdering::Relaxed);
                                        flow_xy_root_forced.fetch_add(xy_pre_forced, AtomicOrdering::Relaxed);
                                        flow_xy_free_sum.fetch_add(xy_free_vars, AtomicOrdering::Relaxed);

                                        match result {
                                            Some(true) => flow_xy_sat.fetch_add(1, AtomicOrdering::Relaxed),
                                            Some(false) => flow_xy_unsat.fetch_add(1, AtomicOrdering::Relaxed),
                                            None => {
                                                let cover = xy_cover_micro(result, xy_decisions, xy_free_vars);
                                                flow_xy_timeout_cov_micro.fetch_add(cover, AtomicOrdering::Relaxed);
                                                flow_xy_timeout.fetch_add(1, AtomicOrdering::Relaxed)
                                            }
                                        };
                                        if result == Some(true) {
                                            let (x, y) = template.extract_xy(&xy_solver);
                                            if verify_tt(problem, &x, &y, &z_seq, &w_seq) {
                                                ctx.found.store(true, AtomicOrdering::Relaxed);
                                                let _ = result_tx.send((x, y, z_seq.clone(), w_seq.clone()));
                                            }
                                        }
                                    },
                                );
                            }
                        }

                        // Aggregate combined-WZ stats into both W and Z stage
                        // counters (see comment at snapshot site above).
                        let wz_decisions    = solver.num_decisions().saturating_sub(wz_d0);
                        let wz_propagations = solver.num_propagations().saturating_sub(wz_p0);
                        let wz_pre_forced   = wz_l0 as u64;
                        let wz_free_vars    = wz_nv.saturating_sub(wz_l0) as u64;
                        flow_w_solves.fetch_add(1, AtomicOrdering::Relaxed);
                        flow_w_decisions.fetch_add(wz_decisions, AtomicOrdering::Relaxed);
                        flow_w_propagations.fetch_add(wz_propagations, AtomicOrdering::Relaxed);
                        flow_w_root_forced.fetch_add(wz_pre_forced, AtomicOrdering::Relaxed);
                        flow_w_free_sum.fetch_add(wz_free_vars, AtomicOrdering::Relaxed);
                        flow_z_solves.fetch_add(1, AtomicOrdering::Relaxed);
                        flow_z_decisions.fetch_add(wz_decisions, AtomicOrdering::Relaxed);
                        flow_z_propagations.fetch_add(wz_propagations, AtomicOrdering::Relaxed);
                        flow_z_root_forced.fetch_add(wz_pre_forced, AtomicOrdering::Relaxed);
                        flow_z_free_sum.fetch_add(wz_free_vars, AtomicOrdering::Relaxed);

                        stage_exit[1].fetch_add(1, AtomicOrdering::Relaxed);

                        // Re-queue: if the enumeration was cut short (conflict
                        // limit hit, or max_z cap reached) and we haven't
                        // found a TT, push this item back with attempt+1 at
                        // a lower priority.  NO CAP on attempts — we defer
                        // hard boundaries to lower priority slots but never
                        // abandon them.  The per-attempt budget doubles each
                        // retry (see conflict_budget above) so every boundary
                        // eventually gets enough effort for SAT/UNSAT.
                        if more_possible
                            && !ctx.found.load(AtomicOrdering::Relaxed)
                        {
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
                            stage_enter[1].fetch_add(1, AtomicOrdering::Relaxed);
                            // Carry prior blocks forward, appending the ones
                            // produced this attempt.  Without this, the next
                            // attempt would rebuild a fresh solver that
                            // doesn't know which (W, Z) pairs have already
                            // been tried, and would redundantly re-enumerate
                            // the same orbits with different phase RNG.
                            let mut carried_blocks = swz.prior_blocks;
                            carried_blocks.extend(new_blocks);
                            wq.push_with_priority(
                                PipelineWork::SolveWZ(SolveWZWork {
                                    tuple: swz.tuple,
                                    z_bits: swz.z_bits,
                                    w_bits: swz.w_bits,
                                    xy_root: swz.xy_root,
                                    candidate_tuples: swz.candidate_tuples.clone(),
                                    attempt: swz.attempt + 1,
                                    prior_blocks: carried_blocks,
                                }),
                                priority,
                            );
                        }
                    }

                    PipelineWork::SolveZ(sz) => {
                        let trace_z = sz.z_bits == 43 && sz.w_bits == 47 && sz.tuple.z == 8;
                        // SAT-solve for Z with spectral constraint, enumerate multiple Z
                        let mut z_boundary = vec![0i8; n];
                        for i in 0..k {
                            z_boundary[i] = if (sz.z_bits >> i) & 1 == 1 { 1 } else { -1 };
                            z_boundary[n - k + i] = if (sz.z_bits >> (k + i)) & 1 == 1 { 1 } else { -1 };
                        }

                        // BDKR rule (iv) boundary pre-filter.  If the
                        // first palindromic pair falls inside the Z
                        // boundary with the wrong sign, no middle Z
                        // can fix it — skip building the SAT entirely.
                        let rule_iv_state = sat_z_middle::check_z_boundary_rule_iv(n, k, &z_boundary);
                        if rule_iv_state == sat_z_middle::BoundaryRuleState::ViolatedAtBoundary {
                            continue;
                        }

                        // Compute V_z = union of ±|σ_Z|-counts over the
                        // tuples surviving the σ_W-narrowing in SolveW.
                        let z_bnd_sum_local: i32 = z_boundary.iter().map(|&v| v as i32).sum();
                        let z_counts: Vec<u32> = {
                            let mut cs: Vec<u32> = Vec::new();
                            for t in &sz.candidate_tuples {
                                let abs_z = t.z.abs();
                                let signs: &[i32] = if abs_z == 0 { &[0] } else { &[1, -1] };
                                for &sg in signs {
                                    if let Some(c) = sigma_full_to_cnt(sg * abs_z, z_bnd_sum_local, ctx.middle_n) {
                                        if !cs.contains(&c) { cs.push(c); }
                                    }
                                }
                            }
                            cs.sort_unstable();
                            cs
                        };
                        if z_counts.is_empty() {
                            stage_exit[2].fetch_add(1, AtomicOrdering::Relaxed);
                            continue;
                        }

                        let mut z_solver = z_bases.remove(&0i32).unwrap_or_else(||
                            ctx.z_tmpl.build_base_solver_quad_pb_pb_set(ctx.middle_n, &z_counts)
                        );
                        let z_cp = z_solver.save_checkpoint();
                        // Reuse z_boundary-dependent fill prep across SolveZ items
                        // that share z_bits (every item from the same SolveW batch).
                        if z_prep_z_bits != Some(sz.z_bits) {
                            z_prep.rebuild(&ctx.z_tmpl, ctx.middle_n, &z_boundary);
                            // Also refresh the cached z_boundary DFT at the
                            // SAT frequency grid — boundary DFT depends only
                            // on z_bits, so it can be reused across this
                            // SolveW's batch of SolveZ items.
                            if let Some(ref ztab) = ctx.z_spectral_tables {
                                let nf = ztab.num_freqs;
                                z_re_boundary.iter_mut().for_each(|v| *v = 0.0);
                                z_im_boundary.iter_mut().for_each(|v| *v = 0.0);
                                for pos in 0..n {
                                    if pos >= k && pos < n - k { continue; }
                                    let val = z_boundary[pos] as f64;
                                    let base = pos * nf;
                                    for fi in 0..nf {
                                        z_re_boundary[fi] += val * ztab.pos_cos[base + fi];
                                        z_im_boundary[fi] += val * ztab.pos_sin[base + fi];
                                    }
                                }
                            }
                            z_prep_z_bits = Some(sz.z_bits);
                        }
                        // Attach spectral BEFORE fill_z_solver_quad_pb so that
                        // any level-0 middle-var assignments forced by quad_pb
                        // propagation feed through the normal propagate path
                        // (which calls spec.assign).  Setting spectral AFTER
                        // fill was a long-standing bug: those level-0 assignments
                        // bypassed spectral, leaving re/im incomplete and
                        // causing the in-SAT check to pass Z's that the
                        // external FFT pair filter correctly rejected.
                        if let Some(ref ztab) = ctx.z_spectral_tables {
                            // Build the SpectralConstraint manually, reusing
                            // the cached z_boundary DFT instead of recomputing
                            // it from scratch in from_tables.
                            let num_freqs = ztab.num_freqs;
                            let middle_len = ztab.middle_len;
                            let mut z_spec = radical::SpectralConstraint {
                                num_seq_vars: middle_len,
                                cos_table: std::sync::Arc::clone(&ztab.cos_table),
                                sin_table: std::sync::Arc::clone(&ztab.sin_table),
                                num_freqs,
                                re: z_re_boundary.clone(),
                                im: z_im_boundary.clone(),
                                re_boundary: z_re_boundary.clone(),
                                im_boundary: z_im_boundary.clone(),
                                bound: ctx.pair_bound,
                                per_freq_bound: None,
                                max_reduction: ztab.max_reduction_total.clone(),
                                amplitudes: std::sync::Arc::clone(&ztab.amplitudes),
                                assigned: vec![false; middle_len],
                                values: vec![0i8; middle_len],
                                seq2: None,
                            };
                            // Compute per-frequency W DFT using the precomputed
                            // pos_cos/pos_sin tables from ztab. Loop order:
                            // outer j (position in W), inner fi (frequency).
                            // The pos tables are laid out as [j*nf + fi], so the
                            // inner loop is sequential in memory (good cache).
                            let nf = z_spec.num_freqs;
                            let mut w_re = vec![0.0f64; nf];
                            let mut w_im = vec![0.0f64; nf];
                            // Inner loop is 25 × 167 fmadds per SolveZ item. Since
                            // w_vals are ±1, replace the multiply with a conditional
                            // add/sub. Lets the compiler emit one SIMD add/sub per
                            // cache line rather than a vector multiply + add.
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
                                pfb[fi] = (ctx.pair_bound - w_re[fi]*w_re[fi] - w_im[fi]*w_im[fi]).max(0.0);
                            }
                            z_spec.per_freq_bound = Some(pfb);
                            z_solver.spectral = Some(z_spec);
                        }

                        sat_z_middle::fill_z_solver_quad_pb(&mut z_solver, &ctx.z_tmpl, n, m, ctx.middle_n, &z_prep, &sz.w_vals);
                        // Rule (iv) middle clauses — only needed when
                        // the boundary left the rule DeferredToMiddle.
                        if rule_iv_state == sat_z_middle::BoundaryRuleState::DeferredToMiddle {
                            let mut nv = (z_solver.num_vars() + 1) as i32;
                            sat_z_middle::add_rule_iv_middle_clauses(
                                &mut z_solver, n, k,
                                |jf| (jf - k + 1) as i32,
                                &mut nv,
                            );
                        }
                        // Retroactively feed middle vars that fill_z_solver
                        // forced at level 0 into the spectral constraint.
                        // `add_quad_pb_eq` / `add_pb_atleast` inside fill
                        // enqueue lits via their own propagators, bypassing
                        // main propagate() — so spectral never saw them.
                        // The `!spec.assigned[v]` guard in propagate's
                        // spectral block prevents double-counting when these
                        // same vars later pass through the main loop.
                        // Need to split borrow: read assignments from solver,
                        // then mutate spectral.
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

                        // Snapshot Z-stage SAT search stats. Diff against
                        // post-loop values for this (Z,W) pair's contribution
                        // to the Z-stage diagnostics.
                        let z_d0 = z_solver.num_decisions();
                        let z_p0 = z_solver.num_propagations();
                        let z_l0 = z_solver.num_level0_vars();
                        let z_nv = z_solver.num_vars();

                        let mut z_count = 0usize;
                        loop {
                            if ctx.found.load(AtomicOrdering::Relaxed) { break; }
                            if z_count >= ctx.max_z { break; }
                            let z_phases: Vec<bool> = (0..ctx.middle_n)
                                .map(|_| next_rng!() & 1 == 1).collect();
                            z_solver.set_phase(&z_phases);
                            let z_result = z_solver.solve();
                            if z_result != Some(true) {
                                if z_count == 0 { flow_z_unsat.fetch_add(1, AtomicOrdering::Relaxed); }
                                break;
                            }
                            z_count += 1;
                            flow_z_solutions.fetch_add(1, AtomicOrdering::Relaxed);

                            let z_mid = extract_vals(&z_solver, |i| ctx.z_mid_vars[i], ctx.middle_n);

                            // BEFORE reset: capture spectral state for diagnostics.
                            let _spec_snap = if std::env::var("TRACE_SPEC").is_ok() {
                                z_solver.spectral.as_ref().map(|sp| (sp.re.clone(), sp.im.clone(), sp.per_freq_bound.clone(), sp.values.clone(), sp.assigned.clone()))
                            } else { None };

                            let mut z_vals = Vec::with_capacity(n);
                            z_vals.extend_from_slice(&z_boundary[..k]);
                            z_vals.extend_from_slice(&z_mid);
                            z_vals.extend_from_slice(&z_boundary[n-k..]);

                            // Only add the blocking clause if we'll loop again.
                            // With max_z=1 we exit the loop immediately after
                            // this iteration, so building + adding the blocker
                            // would be pure wasted work (the restore_checkpoint
                            // below throws it away anyway).
                            if z_count < ctx.max_z {
                                let z_block: Vec<i32> = ctx.z_mid_vars.iter().map(|&v| {
                                    if z_solver.value(v) == Some(true) { -v } else { v }
                                }).collect();
                                z_solver.reset(); // backtrack before adding blocking clause
                                z_solver.add_clause(z_block);
                            }

                            // Individual spectral already enforced by solver (167 freqs).
                            // Just compute spectrum for pair check, into a reusable
                            // buffer (the spectrum is only consumed by the bool-valued
                            // pair check below — no need to allocate a fresh Vec per
                            // Z solution).
                            compute_spectrum_into(&z_vals, &spectral_z, &mut fft_buf_z, &mut z_spectrum_buf);

                            if ctx.middle_n <= 20 {
                                if !spectral_pair_ok(&z_spectrum_buf, &sz.w_spectrum, ctx.pair_bound) {
                                    flow_z_pair_fail.fetch_add(1, AtomicOrdering::Relaxed);
                                    if trace_z { eprintln!("TRACE:   Z solution #{} FAILED pair check", z_count); }
                                    if std::env::var("TRACE_SPEC").is_ok()
                                        && flow_z_pair_fail.load(AtomicOrdering::Relaxed) <= 1
                                    {
                                        // In-SAT's spectral state just before the SAT returned
                                        // `sat` for this Z.  Compare to external.
                                        let (insat_re, insat_im, insat_pfb, insat_values, insat_assigned): (Vec<f64>, Vec<f64>, Vec<f64>, Vec<i8>, Vec<bool>) =
                                            if let Some((ref re, ref im, ref pfb, ref vals, ref asgn)) = _spec_snap {
                                                (re.clone(), im.clone(),
                                                 pfb.clone().unwrap_or_default(),
                                                 vals.clone(), asgn.clone())
                                            } else { (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new()) };
                                        let insat_mid_str: String = insat_values.iter()
                                            .map(|&v| if v == 1 { '+' } else if v == -1 { '-' } else { '0' })
                                            .collect();
                                        let insat_assigned_count = insat_assigned.iter().filter(|&&b| b).count();
                                        eprintln!(
                                            "  SpectralConstraint's internal middle: {:?} ({}/{} assigned)",
                                            insat_mid_str, insat_assigned_count, insat_values.len()
                                        );
                                        eprintln!(
                                            "  Actual extracted z_mid:               {:?}",
                                            z_mid.iter().map(|&v| if v>0 {'+'} else {'-'}).collect::<String>()
                                        );
                                        let fail_bins: Vec<usize> = (0..z_spectrum_buf.len())
                                            .filter(|&i| z_spectrum_buf[i] + sz.w_spectrum[i] > ctx.pair_bound)
                                            .collect();
                                        eprintln!("[TRACE_SPEC] Z pair fail: z_mid={} bound={}",
                                            z_mid.iter().map(|&v| if v>0 {'+'} else {'-'}).collect::<String>(),
                                            ctx.pair_bound);
                                        for &fi in fail_bins.iter().take(3) {
                                            let insat_zmag2 = if fi < insat_re.len() {
                                                insat_re[fi]*insat_re[fi] + insat_im[fi]*insat_im[fi]
                                            } else { f64::NAN };
                                            let pfb_fi = if fi < insat_pfb.len() { insat_pfb[fi] } else { f64::NAN };
                                            eprintln!(
                                                "  bin {fi} (ω={:.4}π): ext |Z|²={:.4} + |W|²={:.4} = {:.4} > bound={}; \
                                                 in-SAT |Z|²={:.4} vs pfb[{fi}]={:.4}  → should have triggered conflict",
                                                fi as f64 / 128.0,
                                                z_spectrum_buf[fi], sz.w_spectrum[fi],
                                                z_spectrum_buf[fi] + sz.w_spectrum[fi], ctx.pair_bound,
                                                insat_zmag2, pfb_fi);
                                        }
                                    }
                                    continue;
                                }
                            }
                            if trace_z { eprintln!("TRACE:   Z solution #{} REACHED XY!", z_count); }

                            let z_seq = PackedSeq::from_values(&z_vals);
                            let zw_autocorr = compute_zw_autocorr(ctx.problem, &z_seq, &w_seq);

                            // Solve XY inline using solve_with_assumptions for each boundary.
                            // This reuses the same solver across boundaries: learnt clauses
                            // from one boundary transfer to the next, and no clone per boundary.
                            // Cache key: the sorted list of candidate (σ_X, σ_Y, σ_Z, σ_W)
                            // — same set of tuples ⇒ same XY template (rule clauses +
                            // V_x/V_y are derived from the tuple list).
                            let mut tuple_key: Vec<(i32, i32, i32, i32)> = sz.candidate_tuples.iter()
                                .map(|t| (t.x, t.y, t.z, t.w)).collect();
                            tuple_key.sort_unstable();
                            let template = template_cache.entry(tuple_key).or_insert_with(||
                                SatXYTemplate::build_multi(problem, &sz.candidate_tuples, &sat_config).unwrap()
                            );
                            let candidate = CandidateZW { zw_autocorr };
                            // Shared XY SAT fast path: clone the per-tuple
                            // template, attach GJ/lag pre-filters and quad
                            // PB term-state injection, then walk the XY
                            // sub-MDD running `try_candidate` for each
                            // surviving (x_bits, y_bits). The extension
                            // pre-filter is interleaved inside the walk
                            // callback.
                            if ctx.xy_mdd_mode {
                                // PROTOTYPE XY_MDD=1: one SAT call per (Z, W)
                                // using the native MDD propagator. Replaces
                                // the per-leaf walk_xy_sub_mdd fan-out for
                                // this boundary. UNSAT here = every (x,y)
                                // leaf in the sub-MDD is infeasible, which
                                // is equivalent to the enumeration path
                                // getting UNSAT (or Pruned) for every leaf.
                                let conflict_limit = if n > 30 { 5000 } else { 0 };
                                let (xy_res, stats) = try_candidate_via_mdd(
                                    problem, &candidate, template, k,
                                    sz.xy_root, &ctx.mdd.nodes, &ctx.xy_pos_order,
                                    conflict_limit,
                                );
                                stage_enter[3].fetch_add(1, AtomicOrdering::Relaxed);
                                items_completed.fetch_add(1, AtomicOrdering::Relaxed);
                                stage_exit[3].fetch_add(1, AtomicOrdering::Relaxed);
                                flow_xy_solves.fetch_add(1, AtomicOrdering::Relaxed);
                                flow_xy_decisions.fetch_add(stats.decisions, AtomicOrdering::Relaxed);
                                flow_xy_propagations.fetch_add(stats.propagations, AtomicOrdering::Relaxed);
                                flow_xy_root_forced.fetch_add(stats.vars_pre_forced, AtomicOrdering::Relaxed);
                                flow_xy_free_sum.fetch_add(stats.free_vars, AtomicOrdering::Relaxed);
                                match xy_res {
                                    Some((x, y)) => {
                                        flow_xy_sat.fetch_add(1, AtomicOrdering::Relaxed);
                                        if verify_tt(problem, &x, &y, &z_seq, &w_seq) {
                                            ctx.found.store(true, AtomicOrdering::Relaxed);
                                            let _ = result_tx.send((x, y, z_seq.clone(), w_seq.clone()));
                                        }
                                    }
                                    None => {
                                        // Can't distinguish UNSAT from timeout
                                        // without threading the raw result back;
                                        // count as unsat for now (cover_micro
                                        // = 1.0 for SAT/UNSAT, fractional for
                                        // timeout — handled inside stats).
                                        flow_xy_unsat.fetch_add(1, AtomicOrdering::Relaxed);
                                    }
                                }
                            } else if let Some(mut state) = SolveXyPerCandidate::new(
                                problem, &candidate, template, k,
                            ) {
                                if n > 30 { state.solver.set_conflict_limit(5000); }
                                if warm.inject_phase {
                                    if let Some(ref ph) = warm.phase { state.solver.set_phase(ph); }
                                }

                                walk_xy_sub_mdd(
                                    sz.xy_root, 0, ctx.xy_zw_depth, 0, 0,
                                    &ctx.xy_pos_order, &ctx.mdd.nodes, ctx.max_bnd_sum,
                                    ctx.middle_n as i32, &sz.candidate_tuples,
                                    &mut |x_bits, y_bits| {
                                        if ctx.found.load(AtomicOrdering::Relaxed) { return; }
                                        // --outfix XY filter: skip everything except the
                                        // pinned (x_bits, y_bits) when the flag is set.
                                        if let Some((fx, fy)) = ctx.outfix_xy {
                                            if x_bits != fx || y_bits != fy { return; }
                                        }
                                        // E1: Extension filter with cache.
                                        if ctx.mdd_extend > 0 {
                                            let cache_key = (sz.z_bits as u128) | ((sz.w_bits as u128) << 32)
                                                          | ((x_bits as u128) << 64) | ((y_bits as u128) << 96);
                                            let ext_ok = *ext_cache.entry(cache_key).or_insert_with(||
                                                mdd_zw_first::has_extension(
                                                    k, k + ctx.mdd_extend,
                                                    sz.z_bits, sz.w_bits, x_bits, y_bits,
                                                )
                                            );
                                            if !ext_ok {
                                                extensions_pruned.fetch_add(1, AtomicOrdering::Relaxed);
                                                return;
                                            }
                                        }
                                        stage_enter[3].fetch_add(1, AtomicOrdering::Relaxed);
                                        let (result, stats) = state.try_candidate(x_bits, y_bits);
                                        items_completed.fetch_add(1, AtomicOrdering::Relaxed);
                                        stage_exit[3].fetch_add(1, AtomicOrdering::Relaxed);
                                        match &result {
                                            XyTryResult::Sat(_, _) => { flow_xy_sat.fetch_add(1, AtomicOrdering::Relaxed); }
                                            XyTryResult::Unsat | XyTryResult::Pruned => { flow_xy_unsat.fetch_add(1, AtomicOrdering::Relaxed); }
                                            XyTryResult::Timeout => {
                                                flow_xy_timeout.fetch_add(1, AtomicOrdering::Relaxed);
                                                flow_xy_timeout_cov_micro.fetch_add(stats.cover_micro, AtomicOrdering::Relaxed);
                                            }
                                        };
                                        // Pruned candidates skip the SAT solver, so their stats are zero —
                                        // don't pollute per-stage averages with an extra "0-decision" sample.
                                        if !matches!(result, XyTryResult::Pruned) {
                                            flow_xy_solves.fetch_add(1, AtomicOrdering::Relaxed);
                                            flow_xy_decisions.fetch_add(stats.decisions, AtomicOrdering::Relaxed);
                                            flow_xy_propagations.fetch_add(stats.propagations, AtomicOrdering::Relaxed);
                                            flow_xy_root_forced.fetch_add(stats.vars_pre_forced, AtomicOrdering::Relaxed);
                                            flow_xy_free_sum.fetch_add(stats.free_vars, AtomicOrdering::Relaxed);
                                        }
                                        if let XyTryResult::Sat(x, y) = result {
                                            if verify_tt(problem, &x, &y, &z_seq, &w_seq) {
                                                ctx.found.store(true, AtomicOrdering::Relaxed);
                                                let _ = result_tx.send((x, y, z_seq.clone(), w_seq.clone()));
                                            }
                                        }
                                    },
                                );
                                warm.phase = Some(state.solver.get_phase());
                            } else {
                                flow_z_prep_fail.fetch_add(1, AtomicOrdering::Relaxed);
                            }
                        }
                        if trace_z {
                            let z_sf = flow_z_spec_fail.load(AtomicOrdering::Relaxed);
                            let z_pf = flow_z_pair_fail.load(AtomicOrdering::Relaxed);
                            eprintln!("TRACE: SolveZ done for target: {} Z found (global z_spec_fail={}, z_pair_fail={})", z_count, z_sf, z_pf);
                        }

                        // Aggregate Z-stage SAT search stats for this (Z,W) pair.
                        // Pre-solve level-0 count captures vars forced by constraint
                        // setup (post fill_z_solver, pre solve()) — the meaningful
                        // "constraint pruning" measurement for the Z stage.
                        let z_decisions    = z_solver.num_decisions().saturating_sub(z_d0);
                        let z_propagations = z_solver.num_propagations().saturating_sub(z_p0);
                        let z_pre_forced   = z_l0 as u64;
                        let z_free_vars    = z_nv.saturating_sub(z_l0) as u64;
                        flow_z_solves.fetch_add(1, AtomicOrdering::Relaxed);
                        flow_z_decisions.fetch_add(z_decisions, AtomicOrdering::Relaxed);
                        flow_z_propagations.fetch_add(z_propagations, AtomicOrdering::Relaxed);
                        flow_z_root_forced.fetch_add(z_pre_forced, AtomicOrdering::Relaxed);
                        flow_z_free_sum.fetch_add(z_free_vars, AtomicOrdering::Relaxed);

                        z_solver.spectral = None;
                        z_solver.restore_checkpoint(z_cp);
                        z_bases.insert(0i32, z_solver);
                        stage_exit[2].fetch_add(1, AtomicOrdering::Relaxed);
                    }

                    PipelineWork::SolveXY(xy) => {
                        xy_item_in_flight.fetch_add(1, AtomicOrdering::Relaxed);
                        // Cross-mode XY stage: (Z, W) pair already fully known.
                        // Navigate the MDD to the xy_root for this (z_bits,
                        // w_bits), build a SolveXyPerCandidate, then walk the
                        // XY sub-MDD running the shared fast path.
                        let item = xy.item;
                        let z_seq = item.z.clone();
                        let w_seq = item.w.clone();
                        let candidate = CandidateZW { zw_autocorr: item.zw_autocorr.clone() };

                        // Extract (z_bits, w_bits) from the boundary of each
                        // sequence and navigate the ZW half of the MDD to the
                        // xy_root node anchoring the XY sub-tree.
                        let mut z_bits = 0u32;
                        let mut w_bits = 0u32;
                        for i in 0..k {
                            if z_seq.get(i) == 1 { z_bits |= 1 << i; }
                            if z_seq.get(n - k + i) == 1 { z_bits |= 1 << (k + i); }
                            if w_seq.get(i) == 1 { w_bits |= 1 << i; }
                            if w_seq.get(m - k + i) == 1 { w_bits |= 1 << (k + i); }
                        }
                        let mut nid = ctx.mdd.root;
                        let mut live = true;
                        for level in 0..ctx.zw_depth {
                            if nid == mdd_reorder::DEAD { live = false; break; }
                            let pos = ctx.xy_pos_order[level];
                            let z_val = (z_bits >> pos) & 1;
                            let w_val = (w_bits >> pos) & 1;
                            let branch = (z_val | (w_val << 1)) as usize;
                            if nid != mdd_reorder::LEAF {
                                nid = ctx.mdd.nodes[nid as usize][branch];
                            }
                        }
                        if !live || nid == mdd_reorder::DEAD {
                            // Boundary not live in the MDD — no candidates.
                            flow_z_prep_fail.fetch_add(1, AtomicOrdering::Relaxed);
                            items_completed.fetch_add(1, AtomicOrdering::Relaxed);
                            stage_exit[3].fetch_add(1, AtomicOrdering::Relaxed);
                            xy_item_in_flight.fetch_sub(1, AtomicOrdering::Relaxed);
                            continue;
                        }
                        let xy_root = nid;

                        let tuple_key: Vec<(i32, i32, i32, i32)> = vec![(
                            item.tuple.x, item.tuple.y, item.tuple.z, item.tuple.w)];
                        let template = template_cache.entry(tuple_key).or_insert_with(||
                            SatXYTemplate::build(ctx.problem, item.tuple, &sat_config).unwrap()
                        );

                        if let Some(mut state) = SolveXyPerCandidate::new(
                            ctx.problem, &candidate, template, k,
                        ) {
                            if n > 30 { state.solver.set_conflict_limit(5000); }
                            if warm.inject_phase {
                                if let Some(ref ph) = warm.phase { state.solver.set_phase(ph); }
                            }

                            walk_xy_sub_mdd(
                                xy_root, 0, ctx.xy_zw_depth, 0, 0,
                                &ctx.xy_pos_order, &ctx.mdd.nodes, ctx.max_bnd_sum,
                                ctx.middle_n as i32, std::slice::from_ref(&item.tuple),
                                &mut |x_bits, y_bits| {
                                    if ctx.found.load(AtomicOrdering::Relaxed) { return; }
                                    if let Some((fx, fy)) = ctx.outfix_xy {
                                        if x_bits != fx || y_bits != fy { return; }
                                    }
                                    stage_enter[3].fetch_add(1, AtomicOrdering::Relaxed);
                                    let (result, stats) = state.try_candidate(x_bits, y_bits);
                                    items_completed.fetch_add(1, AtomicOrdering::Relaxed);
                                    stage_exit[3].fetch_add(1, AtomicOrdering::Relaxed);
                                    match &result {
                                        XyTryResult::Sat(_, _) => { flow_xy_sat.fetch_add(1, AtomicOrdering::Relaxed); }
                                        XyTryResult::Unsat | XyTryResult::Pruned => { flow_xy_unsat.fetch_add(1, AtomicOrdering::Relaxed); }
                                        XyTryResult::Timeout => {
                                            flow_xy_timeout.fetch_add(1, AtomicOrdering::Relaxed);
                                            flow_xy_timeout_cov_micro.fetch_add(stats.cover_micro, AtomicOrdering::Relaxed);
                                        }
                                    };
                                    if !matches!(result, XyTryResult::Pruned) {
                                        flow_xy_solves.fetch_add(1, AtomicOrdering::Relaxed);
                                        flow_xy_decisions.fetch_add(stats.decisions, AtomicOrdering::Relaxed);
                                        flow_xy_propagations.fetch_add(stats.propagations, AtomicOrdering::Relaxed);
                                        flow_xy_root_forced.fetch_add(stats.vars_pre_forced, AtomicOrdering::Relaxed);
                                        flow_xy_free_sum.fetch_add(stats.free_vars, AtomicOrdering::Relaxed);
                                    }
                                    if let XyTryResult::Sat(x, y) = result {
                                        if verify_tt(ctx.problem, &x, &y, &z_seq, &w_seq) {
                                            ctx.found.store(true, AtomicOrdering::Relaxed);
                                            let _ = result_tx.send((x, y, z_seq.clone(), w_seq.clone()));
                                        }
                                    }
                                },
                            );
                            warm.phase = Some(state.solver.get_phase());
                        } else {
                            flow_z_prep_fail.fetch_add(1, AtomicOrdering::Relaxed);
                        }
                        xy_item_in_flight.fetch_sub(1, AtomicOrdering::Relaxed);
                    }

                    PipelineWork::Shutdown => break,
                }
            }
        }));
    }
    drop(result_tx);

    // Monitor loop: feed the queue on demand + check for solution/time limit.
    //
    // In cross mode, the monitor runs the hybrid Z × W enumeration
    // directly and pushes SolveXY items as it finds surviving pairs.
    // In apart/together modes, the monitor walks MDD paths and pushes
    // Boundary items (the traditional MDD path).
    let wz_mode = cfg.effective_wz_mode();
    let queue_target = 200; // quality buffer: accumulate XY items for spectral sorting
    let mut found_solution = false;
    let mut last_progress = Instant::now();
    let mut last_counts = [0u64; 4];
    let mut rates = [0.0f64; 4];
    let mut last_snap = Instant::now();

    // Cross-mode enumeration state: built up lazily as tuples are
    // processed. w_cache maps (tuple.w sum) → (w_candidates, SpectralIndex)
    // so repeated tuples sharing the same w sum only build W once.
    let mut cross_w_cache: HashMap<i32, (Vec<SeqWithSpectrum>, SpectralIndex)> = HashMap::new();
    let mut cross_tuple_idx: usize = 0;
    let cross_spectral_z = SpectralFilter::new(n, cfg.theta_samples);
    let cross_spectral_w = SpectralFilter::new(n, cfg.theta_samples);
    let mut cross_stats = SearchStats::default();
    let mut cross_seen_zw: std::collections::HashSet<Vec<i32>> = std::collections::HashSet::new();
    let mut cross_done = false;

    loop {
        // Feed the queue when depth is low.
        let gold_depth = work_queue.gold_len();
        let pending_bnd = pending_boundaries.load(AtomicOrdering::Relaxed) as usize;
        if wz_mode == WzMode::Cross {
            // Cross: process the next tuple and stream its (Z, W) pairs as
            // SolveXY items. Apply backpressure via gold queue depth so we
            // don't blow up memory on large n.
            const CROSS_GOLD_CAP: usize = 4096;
            if !cross_done && gold_depth < CROSS_GOLD_CAP && cross_tuple_idx < tuples.len() {
                let tuple = tuples[cross_tuple_idx];
                cross_tuple_idx += 1;

                let b_start = Instant::now();
                if !cross_w_cache.contains_key(&tuple.w) {
                    let w_candidates = build_w_candidates(
                        problem, tuple.w, cfg, &cross_spectral_w, &mut cross_stats, &ctx.found);
                    let w_index = SpectralIndex::build(&w_candidates);
                    cross_w_cache.insert(tuple.w, (w_candidates, w_index));
                }
                if !ctx.found.load(AtomicOrdering::Relaxed) {
                    let (w_candidates, w_index) = cross_w_cache.get(&tuple.w).unwrap();
                    let before = (
                        cross_stats.z_generated,
                        cross_stats.z_spectral_ok,
                        cross_stats.candidate_pair_spectral_ok,
                    );
                    let mut pushed = 0usize;
                    for_each_zw_pair(
                        problem, tuple.z, w_candidates, w_index, cfg, &cross_spectral_z,
                        &mut cross_stats, &ctx.found,
                        |z_seq, w_seq, zw, z_spectrum, w_spectrum| {
                            let max_power = spectral_pair_max_power(z_spectrum, w_spectrum);
                            if cross_seen_zw.insert(zw.clone()) {
                                let item = SatWorkItem {
                                    tuple,
                                    z: z_seq.clone(),
                                    w: w_seq.clone(),
                                    zw_autocorr: zw,
                                    priority: max_power,
                                };
                                work_queue.push(PipelineWork::SolveXY(SolveXYWork { item }));
                                pushed += 1;
                            }
                            true
                        },
                    );
                    cross_stats.phase_b_nanos += b_start.elapsed().as_nanos() as u64;
                    let z_gen = cross_stats.z_generated - before.0;
                    let z_ok = cross_stats.z_spectral_ok - before.1;
                    let pairs = cross_stats.candidate_pair_spectral_ok - before.2;
                    if verbose {
                        eprintln!("  tuple {}/{} (sums {} {} {} {}): z_gen={} z_ok={} w={} pairs={} pushed={}",
                            cross_tuple_idx, tuples.len(), tuple.x, tuple.y, tuple.z, tuple.w,
                            z_gen, z_ok, w_candidates.len(), pairs, pushed);
                    }
                }
                if cross_tuple_idx >= tuples.len() {
                    cross_done = true;
                }
            }
        } else if pending_bnd < queue_target {
            // Apart/Together: walk MDD paths and push Boundary items when
            // the *pending boundary* count is low.  (We can't gate on the
            // whole work_queue depth because deferred SolveWZ re-queues at
            // negative priority pile up and would otherwise starve the
            // walker of its queue budget, stranding the search on a handful
            // of boundaries that just cycle through re-queue forever.)
            if let Some(ref outfix) = cfg.test_outfix {
                // --outfix: restrict the search to one specific boundary.
                // Navigate directly to it (no MDD path walk), emit once,
                // then exhaust the walker so the search terminates when
                // the pipeline finishes this single boundary.
                if path_counter.load(AtomicOrdering::Relaxed) == 0 {
                    if let Some(xy_root) = mdd_navigate_to_outfix(
                        mdd.root, zw_depth, &full_pos_order, &mdd.nodes,
                        outfix.z_bits, outfix.w_bits,
                    ) {
                        boundaries_walked.fetch_add(1, AtomicOrdering::Relaxed);
                        pending_boundaries.fetch_add(1, AtomicOrdering::Relaxed);
                        work_queue.push(PipelineWork::Boundary(BoundaryWork {
                            z_bits: outfix.z_bits, w_bits: outfix.w_bits, xy_root,
                        }));
                        eprintln!("--outfix: emitted one boundary (z_bits=0x{:x}, w_bits=0x{:x}, xy_root={})",
                            outfix.z_bits, outfix.w_bits, xy_root);
                    } else {
                        eprintln!("--outfix: boundary (z_bits=0x{:x}, w_bits=0x{:x}) not present in the MDD (pruned during gen or rule pre-filter)",
                            outfix.z_bits, outfix.w_bits);
                    }
                    // Mark the walker as fully exhausted: we've emitted
                    // all we plan to.
                    path_counter.store(total_paths, AtomicOrdering::Relaxed);
                }
            } else {
                let batch = queue_target;
                let mut fed = 0;
                while fed < batch {
                    let idx = path_counter.fetch_add(1, AtomicOrdering::Relaxed);
                    if idx >= total_paths { break; } // exhausted all paths
                    let path = idx.wrapping_mul(lcg_mult) & lcg_mask;
                    let bnd = mdd_navigate_path(mdd.root, zw_depth, path, &full_pos_order, &mdd.nodes);
                    if let Some((z_bits, w_bits, xy_root)) = bnd {
                        boundaries_walked.fetch_add(1, AtomicOrdering::Relaxed);
                        pending_boundaries.fetch_add(1, AtomicOrdering::Relaxed);
                        work_queue.push(PipelineWork::Boundary(BoundaryWork { z_bits, w_bits, xy_root }));
                        fed += 1;
                    }
                }
            }
        }

        // Cross mode: the monitor IS the producer, so a long sleep
        // directly delays enumeration. Use a much shorter pause so the
        // next tuple is streamed promptly. MDD monitor's sleep stays
        // at 10ms because it only feeds batches when the work queue
        // drops below `queue_target`.
        if wz_mode == WzMode::Cross {
            std::thread::sleep(std::time::Duration::from_micros(500));
        } else {
            std::thread::sleep(std::time::Duration::from_millis(10));
        }

        // Check for solution
        match result_rx.try_recv() {
            Ok(sol) => {
                if verbose {
                    print_solution(&format!("TT({}) SOLUTION", n), &sol.0, &sol.1, &sol.2, &sol.3);
                }
                found_solution = true;
                ctx.found.store(true, AtomicOrdering::Relaxed);
                break;
            }
            Err(std::sync::mpsc::TryRecvError::Disconnected) => break,
            Err(std::sync::mpsc::TryRecvError::Empty) => {}
        }

        // Time limit
        if sat_secs > 0 && run_start.elapsed().as_secs() >= sat_secs {
            if verbose { eprintln!("  Time limit reached ({}s)", sat_secs); }
            ctx.found.store(true, AtomicOrdering::Relaxed);
            break;
        }

        // Cross-mode exhaustion: producer finished enumerating every
        // tuple, the dual queue is empty, and no worker has a SolveXY
        // item in flight. Signal `found` so workers unblock, then exit.
        if wz_mode == WzMode::Cross && cross_done
            && work_queue.work_len() == 0
            && work_queue.gold_len() == 0
            && xy_item_in_flight.load(AtomicOrdering::Relaxed) == 0
        {
            if verbose { eprintln!("  Cross enumeration exhausted, no solution found"); }
            ctx.found.store(true, AtomicOrdering::Relaxed);
            break;
        }

        // Throughput snapshots
        if last_snap.elapsed().as_secs_f64() >= 2.0 {
            let dt = last_snap.elapsed().as_secs_f64();
            for i in 0..4 {
                let cur = stage_exit[i].load(AtomicOrdering::Relaxed);
                rates[i] = (cur - last_counts[i]) as f64 / dt;
                last_counts[i] = cur;
            }
            last_snap = Instant::now();
        }

        // Progress display
        if verbose && last_progress.elapsed().as_secs() >= 10 {
            let elapsed = run_start.elapsed().as_secs_f64();
            if wz_mode == WzMode::Cross {
                // Cross mode: the MDD-centric depth bars are meaningless
                // (the monitor doesn't walk paths and stages 0-2 stay at
                // zero). Report producer progress instead: how many
                // tuples have been enumerated, the gold queue depth, and
                // the individual-XY-candidate throughput. TTC is
                // extrapolated from tuple progress: estimate the total
                // XY candidates as `pushed × tuples_total / tuples_done`.
                let gold_depth = work_queue.gold_len();
                let xy_pushed  = stage_enter[3].load(AtomicOrdering::Relaxed);
                let xy_done_eff = effective_xy_done(
                    flow_xy_sat.load(AtomicOrdering::Relaxed),
                    flow_xy_unsat.load(AtomicOrdering::Relaxed),
                    flow_xy_timeout.load(AtomicOrdering::Relaxed),
                    flow_xy_timeout_cov_micro.load(AtomicOrdering::Relaxed),
                );
                let est_total = cross_estimated_total_xy(
                    xy_pushed, cross_tuple_idx, tuples.len(), cross_done,
                );
                let rate = if elapsed > 0.0 { xy_done_eff / elapsed } else { 0.0 };
                let ttc = if rate > 0.0 { (est_total - xy_done_eff).max(0.0) / rate } else { f64::INFINITY };
                let ttc_str = if ttc < 60.0 { format!("{:.0}s", ttc) }
                             else if ttc < 3600.0 { format!("{:.0}m", ttc / 60.0) }
                             else if ttc < 86400.0 { format!("{:.1}h", ttc / 3600.0) }
                             else { format!("{:.0}d", ttc / 86400.0) };
                let pct = if est_total > 0.0 { xy_done_eff / est_total * 100.0 } else { 0.0 };
                eprintln!(
                    "[{:>3.0}s] --wz=cross  tuples {}/{}  gold {}  XY {:.0}/{:.0} ({:.1}%)  {:.0}/s  cover:{}",
                    elapsed, cross_tuple_idx, tuples.len(), gold_depth,
                    xy_done_eff, est_total, pct, rate, ttc_str,
                );
            } else {
                // MDD modes: boundary walker drives everything, so the
                // depth bars and boundary-rate metric reflect real work.
                let walked = stage_exit[0].load(AtomicOrdering::Relaxed);
                // Per-stage queue depths
                let mut depths = [0i64; 4];
                for i in 0..4 {
                    depths[i] = (stage_enter[i].load(AtomicOrdering::Relaxed) as i64
                        - stage_exit[i].load(AtomicOrdering::Relaxed) as i64).max(0);
                }
                let fill_chars = [' ', '\u{2581}', '\u{2582}', '\u{2583}', '\u{2584}', '\u{2585}', '\u{2586}', '\u{2587}', '\u{2588}'];
                let max_depth = depths.iter().cloned().max().unwrap_or(1).max(1) as f64;
                let bar = |d: i64| -> char {
                    let idx = ((d as f64 / max_depth) * 8.0).round() as usize;
                    fill_chars[idx.min(8)]
                };
                let bnd_rate = if elapsed > 0.0 { walked as f64 / elapsed } else { 0.0 };
                let pct_done = if live_zw_paths > 0.0 { walked as f64 / live_zw_paths * 100.0 } else { 0.0 };
                // Effective coverage: each fully-resolved boundary counts as 1.0,
                // each XY-timeout shaves off (1 - cover_frac) / xy_per_boundary.
                // See `effective_coverage_metric` for the derivation.
                let eff = effective_coverage_metric(
                    walked,
                    flow_xy_sat.load(AtomicOrdering::Relaxed),
                    flow_xy_unsat.load(AtomicOrdering::Relaxed),
                    flow_xy_timeout.load(AtomicOrdering::Relaxed),
                    flow_xy_timeout_cov_micro.load(AtomicOrdering::Relaxed),
                );
                let cover_rate = if elapsed > 0.0 { eff / elapsed } else { 0.0 };
                let ttc = if cover_rate > 0.0 { (live_zw_paths - eff).max(0.0) / cover_rate } else { f64::INFINITY };
                let ttc_str = if ttc < 60.0 { format!("{:.0}s", ttc) }
                             else if ttc < 3600.0 { format!("{:.0}m", ttc / 60.0) }
                             else if ttc < 86400.0 { format!("{:.1}h", ttc / 3600.0) }
                             else { format!("{:.0}d", ttc / 86400.0) };
                eprintln!("[{:>3.0}s] {}{}{}{} {:>5.0}bnd/s  B:{:<4} W:{:<5} Z:{:<4} XY:{:<5}  {:.2}% cover:{}",
                    elapsed,
                    bar(depths[0]), bar(depths[1]), bar(depths[2]), bar(depths[3]),
                    bnd_rate,
                    depths[0], depths[1], depths[2], depths[3],
                    pct_done, ttc_str);
            }
            last_progress = Instant::now();
        }
    }

    // Signal shutdown
    for _ in 0..workers {
        work_queue.push(PipelineWork::Shutdown);
    }
    work_queue.condvar.notify_all();
    for h in handles {
        let _ = h.join();
    }

    let elapsed = run_start.elapsed();
    let done = items_completed.load(AtomicOrdering::Relaxed);
    // TTC must be based on boundaries actually COMPLETED (stage 0 exit),
    // not boundaries pushed to the queue. The old counter measured pushes,
    // which inflates TTC when the monitor front-loads boundaries but workers
    // can't drain them in the time window. stage_exit[0] is the true count
    // of boundaries whose ZW->W->Z->XY work has finished.
    let completed_bnd = stage_exit[0].load(AtomicOrdering::Relaxed);
    let walked = completed_bnd;
    let pushed = boundaries_walked.load(AtomicOrdering::Relaxed);

    if verbose {
        println!("\n--- MDD pipeline k={} ({} workers) ---", k, workers);
        for (i, name) in ["MDD", "W", "Z", "XY"].iter().enumerate() {
            println!("  Stage {} ({}): {:>10} items", i, name, stage_exit[i].load(AtomicOrdering::Relaxed));
        }
        let _z_done = stage_exit[2].load(AtomicOrdering::Relaxed);
        let ext_pruned = extensions_pruned.load(AtomicOrdering::Relaxed);
        println!("  XY solves:                {:>10}", done);
        println!("  Extensions pruned:        {:>10}", ext_pruned);
        println!("  Boundaries walked:        {:>10} (pushed: {})", walked, pushed);
        // Coverage metrics
        let secs = elapsed.as_secs_f64();
        let xy_timeout_count = flow_xy_timeout.load(AtomicOrdering::Relaxed);
        let xy_unsat_count = flow_xy_unsat.load(AtomicOrdering::Relaxed);
        let xy_sat_count = flow_xy_sat.load(AtomicOrdering::Relaxed);
        let xy_total_solves = xy_timeout_count + xy_unsat_count + xy_sat_count;
        let timeout_frac = if xy_total_solves > 0 { xy_timeout_count as f64 / xy_total_solves as f64 } else { 0.0 };

        // Search progress metric.
        // The MDD at width k partitions the boundary space into 4^(4k) full paths
        // (each fixing 8k bits across Z,W,X,Y). The MDD pre-eliminates dead paths
        // during construction. We count live paths to compute remaining work.
        let total_bits = 4 * n - 1;  // total sign degrees of freedom
        let bnd_bits = 8 * k;        // bits fixed per full MDD path (all 4 seqs × 2k positions)
        let subcube_bits = if total_bits > bnd_bits { total_bits - bnd_bits } else { 0 };
        let live_paths = mdd.count_live_paths();
        let total_paths = 4.0f64.powi(mdd.depth as i32);
        let mdd_pruned_frac = 1.0 - live_paths / total_paths;
        // Each live path is a subcube of 2^subcube_bits configs.
        // MDD already eliminated (total - live) × 2^subcube_bits configs.
        // Runtime resolves walked boundaries: each ZW boundary covers
        // its full XY sub-tree, eliminating multiple full paths.
        let _mdd_elim_log2 = if mdd_pruned_frac > 0.0 {
            (total_paths - live_paths).log2() + subcube_bits as f64
        } else { 0.0 };

        // Headline metric: time to cover. Each fully-resolved boundary
        // contributes 1.0 to `eff`; XY timeouts contribute fractionally
        // based on how much of their sub-problem they actually explored.
        // For a run with no XY timeouts, `eff == walked` exactly, so the
        // formula reduces to the prior path-rate-based TTC.
        let xy_timeout_cov_micro = flow_xy_timeout_cov_micro.load(AtomicOrdering::Relaxed);
        // Pick the right denominator for this mode. Apart/Together walk
        // MDD boundaries — total work = `live_zw_paths`, effective done =
        // `walked × (1 - shortfall_per_xy)`. Cross enumerates (Z, W) pairs
        // and pushes them straight to XY, so total work = total XY
        // candidate solves (extrapolated from tuple progress while the
        // producer is still running).
        let (eff, total_label, total_value, rate_unit) = if wz_mode == WzMode::Cross {
            let xy_pushed = stage_enter[3].load(AtomicOrdering::Relaxed);
            let est_total = cross_estimated_total_xy(
                xy_pushed, cross_tuple_idx, tuples.len(), cross_done,
            );
            let xy_done_eff = effective_xy_done(
                xy_sat_count, xy_unsat_count, xy_timeout_count, xy_timeout_cov_micro,
            );
            (xy_done_eff, "XY candidates", est_total, "XY/s")
        } else {
            let eff = effective_coverage_metric(
                walked, xy_sat_count, xy_unsat_count, xy_timeout_count, xy_timeout_cov_micro,
            );
            (eff, "live ZW paths", live_zw_paths, "eff bnd/s")
        };
        let cover_rate = if secs > 0.0 { eff / secs } else { 0.0 };
        let ttc = if cover_rate > 0.0 { (total_value - eff).max(0.0) / cover_rate } else { f64::INFINITY };
        let ttc_str = if ttc < 60.0 { format!("{:.0}s", ttc) }
                     else if ttc < 3600.0 { format!("{:.1}m", ttc / 60.0) }
                     else if ttc < 86400.0 { format!("{:.1}h", ttc / 3600.0) }
                     else { format!("{:.1}d", ttc / 86400.0) };
        println!("  Time to cover:            {} ({:.2} {}, {:.0} {})",
            ttc_str, cover_rate, rate_unit, total_value, total_label);
        let pct = if total_value > 0.0 { eff / total_value * 100.0 } else { 0.0 };
        if wz_mode == WzMode::Cross {
            println!("  Progress:                 {:.4}% ({:.1} effective of {:.0} estimated; cross_done={})",
                pct, eff, total_value, cross_done);
        } else {
            println!("  Progress:                 {:.4}% ({:.1} effective of {:.0}, {} walked)",
                pct, eff, total_value, walked);
        }
        println!("  XY timeout:               {:.1}%", timeout_frac * 100.0);
        println!("  Wall-clock:               {:>10.3?}", elapsed);

        // Per-stage SAT pruning diagnostics: averages over all SAT solves
        // at each stage, derived from the per-stage flow_*_decisions etc.
        // counters that workers update by diffing radical::Solver counters
        // before/after each solve.
        print_stage_pruning_block(
            ("W", &flow_w_solves, &flow_w_decisions, &flow_w_propagations, &flow_w_root_forced, &flow_w_free_sum, None, None),
            ("Z", &flow_z_solves, &flow_z_decisions, &flow_z_propagations, &flow_z_root_forced, &flow_z_free_sum, None, None),
            ("XY", &flow_xy_solves, &flow_xy_decisions, &flow_xy_propagations, &flow_xy_root_forced, &flow_xy_free_sum, Some(&flow_xy_timeout), Some(&flow_xy_timeout_cov_micro)),
        );

        if !found_solution { println!("No solution found."); }

        // Pipeline flow funnel
        let f = |c: &Arc<std::sync::atomic::AtomicU64>| c.load(AtomicOrdering::Relaxed);
        let w_emitted = stage_enter[1].load(AtomicOrdering::Relaxed);
        let sum_fail = f(&flow_bnd_sum_fail);
        let w_sols = f(&flow_w_solutions);
        let w_sf = f(&flow_w_spec_fail);
        let w_sp = f(&flow_w_spec_pass);
        let z_sols = f(&flow_z_solutions);
        let z_sf = f(&flow_z_spec_fail);
        let z_pf = f(&flow_z_pair_fail);
        let z_gj = f(&flow_z_prep_fail);
        let z_xy = z_sols.saturating_sub(z_sf + z_pf + z_gj);
        let xy_total = ext_pruned + f(&flow_xy_sat) + f(&flow_xy_unsat) + f(&flow_xy_timeout);
        let xy_sat = f(&flow_xy_sat);
        let xy_unsat = f(&flow_xy_unsat);
        let xy_timeout = f(&flow_xy_timeout);
        let pct = |num: u64, den: u64| if den > 0 { format!("{:.1}%", num as f64 / den as f64 * 100.0) } else { "—".into() };

        println!("\n  --- Pipeline Flow ---");
        println!("  Boundaries  {}", walked);
        if sum_fail > 0 {
            println!("    → Tuples    {}  (sum infeasible: {})", walked as u64 * ctx.tuples.len() as u64, sum_fail);
        }
        println!("    → SolveW    {}", w_emitted);
        println!("      → W sols    {}", w_sols);
        if w_sols > 0 {
            println!("        ✗ {} W spectral fail ({})", w_sf, pct(w_sf, w_sols));
        }
        println!("        → {} pass → SolveZ", w_sp);
        println!("          → {} Z solutions", z_sols);
        if z_sols > 0 {
            if z_sf > 0 { println!("            ✗ {} Z spectral fail ({})", z_sf, pct(z_sf, z_sols)); }
            if z_pf > 0 { println!("            ✗ {} Z pair fail ({})", z_pf, pct(z_pf, z_sols)); }
            if z_gj > 0 { println!("            ✗ {} Z prep/GJ fail", z_gj); }
        }
        println!("            → {} reach XY stage", z_xy);
        if z_xy > 0 {
            println!("              → {} XY candidates", xy_total);
            if ext_pruned > 0 { println!("                ✗ {} extension pruned ({})", ext_pruned, pct(ext_pruned, xy_total)); }
            println!("                → {} XY SAT solves", xy_sat + xy_unsat + xy_timeout);
            println!("                  ✗ {} UNSAT proved ({})", xy_unsat, pct(xy_unsat, xy_unsat + xy_timeout + xy_sat));
            if xy_timeout > 0 {
                println!("                  ✗ {} TIMEOUT gave up ({})", xy_timeout, pct(xy_timeout, xy_unsat + xy_timeout + xy_sat));
            }
            if xy_sat > 0 {
                println!("                  ✓ {} SAT!", xy_sat);
            }
        }

        // SolveWZ-specific diagnostics (only populated in --wz=together mode).
        let wz_empty = flow_wz_empty_v.load(AtomicOrdering::Relaxed);
        let wz_rule = flow_wz_rule_viol.load(AtomicOrdering::Relaxed);
        let wz_calls = flow_wz_sat_calls.load(AtomicOrdering::Relaxed);
        let wz_first_unsat = flow_wz_first_unsat.load(AtomicOrdering::Relaxed);
        let wz_sols = flow_wz_solutions.load(AtomicOrdering::Relaxed);
        let wz_exhausted = flow_wz_exhausted.load(AtomicOrdering::Relaxed);
        let wz_budget = flow_wz_budget_hit.load(AtomicOrdering::Relaxed);
        if wz_empty + wz_rule + wz_calls > 0 {
            println!("\n  --- SolveWZ Flow (wz=together) ---");
            println!("    V_w or V_z empty (early skip): {}", wz_empty);
            println!("    Rule (iv)/(v) violated:         {}", wz_rule);
            println!("    solver.solve() calls:           {}", wz_calls);
            println!("      first-call UNSAT:             {} ({})", wz_first_unsat, pct(wz_first_unsat, wz_calls));
            println!("      WZ solutions produced:        {}", wz_sols);
            println!("      attempts exhausted (UNSAT):   {} ({})", wz_exhausted, pct(wz_exhausted, wz_calls));
            println!("      attempts budget-hit (defer):  {} ({})", wz_budget, pct(wz_budget, wz_calls));
            let wz_items = wz_empty + wz_rule + wz_first_unsat;
            if wz_items > 0 {
                let reach_sat = wz_calls.saturating_sub(wz_sols);
                println!("    → {} reached first SAT call; {} returned 0 solutions", reach_sat, wz_first_unsat);
            }
        }
    }

    let all_stats = SearchStats::default(); // TODO: aggregate from workers
    SearchReport { stats: all_stats, elapsed, found_solution }
}

