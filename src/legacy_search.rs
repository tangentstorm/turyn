//! Legacy hybrid search driver (phases A+B+C), verification, and benchmarks.

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

use crate::SPECTRAL_FREQS;
use crate::config::*;
use crate::enumerate::*;
use crate::mdd_pipeline::*;
use crate::spectrum::*;
use crate::stochastic::*;
use crate::types::*;
use crate::xy_sat::*;

#[derive(Default, Clone, Debug)]
pub(crate) struct SearchStats {
    pub(crate) z_generated: usize,
    pub(crate) z_spectral_ok: usize,
    pub(crate) w_generated: usize,
    pub(crate) w_spectral_ok: usize,
    pub(crate) candidate_pair_attempts: usize,
    pub(crate) candidate_pair_spectral_ok: usize,
    pub(crate) xy_nodes: usize,
    pub(crate) phase_b_nanos: u64,
}

impl SearchStats {
    pub(crate) fn merge_from(&mut self, other: &SearchStats) {
        self.z_generated += other.z_generated;
        self.z_spectral_ok += other.z_spectral_ok;
        self.w_generated += other.w_generated;
        self.w_spectral_ok += other.w_spectral_ok;
        self.candidate_pair_attempts += other.candidate_pair_attempts;
        self.candidate_pair_spectral_ok += other.candidate_pair_spectral_ok;
        self.xy_nodes += other.xy_nodes;
        self.phase_b_nanos += other.phase_b_nanos;
    }
}

/// Per-worker warm-start state for phase transfer between SAT solves.
/// Each worker captures the last solver's phase vector and injects it
/// into the next clone-and-solve cycle — a cheap way to preserve value
/// hints across closely-related XY SAT instances.
pub(crate) struct WarmStartState {
    pub(crate) phase: Option<Vec<bool>>,
    pub(crate) inject_phase: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct SearchReport {
    pub(crate) stats: SearchStats,
    pub(crate) elapsed: std::time::Duration,
    pub(crate) found_solution: bool,
}

// ==================== Unified SAT work-item types ====================

pub(crate) fn run_benchmark(cfg: &SearchConfig) {
    if cfg.stochastic {
        run_stochastic_benchmark(cfg);
    } else {
        run_hybrid_benchmark(cfg);
    }
}

pub(crate) fn run_hybrid_benchmark(cfg: &SearchConfig) {
    let repeats = cfg.benchmark_repeats.max(1);
    let warmup = run_hybrid_search(cfg, false);
    println!(
        "benchmark,warmup,elapsed_ms={:.3},found_solution={}",
        warmup.elapsed.as_secs_f64() * 1000.0,
        warmup.found_solution
    );
    println!("benchmark,run,elapsed_ms,found_solution");
    let mut elapsed_ms = Vec::with_capacity(repeats);
    for run in 1..=repeats {
        let report = run_hybrid_search(cfg, false);
        let ms = report.elapsed.as_secs_f64() * 1000.0;
        elapsed_ms.push(ms);
        println!("benchmark,{},{:.3},{}", run, ms, report.found_solution);
    }
    elapsed_ms.sort_by(|a, b| a.partial_cmp(b).unwrap_or(Ordering::Equal));
    let median = elapsed_ms[elapsed_ms.len() / 2];
    let mean = elapsed_ms.iter().sum::<f64>() / elapsed_ms.len() as f64;
    println!(
        "benchmark,summary,mean_ms={:.3},median_ms={:.3},repeats={}",
        mean, median, repeats
    );
}

pub(crate) fn run_stochastic_benchmark(cfg: &SearchConfig) {
    let secs = if cfg.stochastic_seconds > 0 {
        cfg.stochastic_seconds
    } else {
        10
    };
    let repeats = cfg.benchmark_repeats.max(1);
    // Warmup
    let warmup = stochastic_search(cfg.problem, cfg.test_tuple.as_ref(), false, secs);
    let warmup_rate = warmup.stats.xy_nodes as f64 / warmup.elapsed.as_secs_f64();
    println!(
        "benchmark,warmup,elapsed_s={:.3},flips={},flips_per_sec={:.0},found_solution={}",
        warmup.elapsed.as_secs_f64(),
        warmup.stats.xy_nodes,
        warmup_rate,
        warmup.found_solution
    );
    println!("benchmark,run,elapsed_s,flips,flips_per_sec,found_solution");
    let mut rates = Vec::with_capacity(repeats);
    for run in 1..=repeats {
        let report = stochastic_search(cfg.problem, cfg.test_tuple.as_ref(), false, secs);
        let rate = report.stats.xy_nodes as f64 / report.elapsed.as_secs_f64();
        rates.push(rate);
        println!(
            "benchmark,{},{:.3},{},{:.0},{}",
            run,
            report.elapsed.as_secs_f64(),
            report.stats.xy_nodes,
            rate,
            report.found_solution
        );
    }
    rates.sort_by(|a, b| a.partial_cmp(b).unwrap_or(Ordering::Equal));
    let median = rates[rates.len() / 2];
    let mean = rates.iter().sum::<f64>() / rates.len() as f64;
    println!(
        "benchmark,summary,mean_flips_per_sec={:.0},median_flips_per_sec={:.0},repeats={}",
        mean, median, repeats
    );
}

/// Thin wrapper around the unified runner with `wz_mode = Cross`. Kept
/// for tests and benchmarks that were written before the unification;
/// new code should call `run_mdd_sat_search` directly.
pub(crate) fn run_hybrid_search(cfg: &SearchConfig, verbose: bool) -> SearchReport {
    let problem = cfg.problem;
    let mut tuples = phase_a_tuples(problem, cfg.test_tuple.as_ref());
    // Heuristic tuple ordering depends on problem size.
    if problem.n >= 26 {
        tuples.sort_by_key(|t| {
            (
                (t.x - t.y).abs(),
                t.z.abs() + t.w.abs(),
                t.x.abs() + t.y.abs(),
            )
        });
    } else {
        tuples.sort_by_key(|t| {
            (
                t.z.abs() + t.w.abs(),
                (t.x - t.y).abs(),
                t.x.abs() + t.y.abs(),
            )
        });
    }

    let mut cfg = cfg.clone();
    cfg.wz_mode = Some(WzMode::Cross);
    cfg.wz_together = false;
    // Cross mode historically used k=7 for XY enumeration.
    if cfg.mdd_k == SearchConfig::default().mdd_k {
        cfg.mdd_k = 7;
    }
    let mdd_k = cfg.mdd_k.min((problem.n - 1) / 2).min(problem.m() / 2);
    run_mdd_sat_search(problem, &tuples, &cfg, verbose, mdd_k)
}
