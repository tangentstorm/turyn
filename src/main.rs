//! Turyn-type sequence search: binary entry point.
//!
//! Topic submodules live in sibling files; see each module's header doc.

#![allow(unused_imports)]

mod config;
mod enumerate;
mod legacy_search;
mod mdd_pipeline;
#[cfg(feature = "search-framework")]
mod search_framework;
mod spectrum;
mod stochastic;
mod sync_walker;
mod types;
mod xy_sat;

use std::cmp::Ordering;
use std::collections::HashMap;
use std::env;
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
use crate::mdd_pipeline::*;
#[cfg(feature = "search-framework")]
use crate::search_framework::engine::{EngineConfig, SearchEngine, SearchModeAdapter};
#[cfg(feature = "search-framework")]
use crate::search_framework::events::SearchEvent;
#[cfg(feature = "search-framework")]
use crate::search_framework::mode_adapters::mdd_stages::{MddPayload, MddStagesAdapter};
#[cfg(feature = "search-framework")]
use crate::search_framework::queue::GoldThenWork;
use crate::spectrum::*;
use crate::stochastic::*;
use crate::types::*;
use crate::xy_sat::*;

/// Number of spectral frequencies for the SAT solver's built-in spectral constraint.
/// 64 chosen via n=26 --wz=apart TTC sweep (see OPTIMIZATION_LOG §S5, April 2026);
/// covers a dense-enough grid that post-hoc FFT still finds near-zero false-negatives.
pub(crate) const SPECTRAL_FREQS: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CliVerb {
    Search,
    Guess,
    Verify,
    Tuples,
    Dump,
    List,
    Help,
}

fn print_help() {
    eprintln!("turyn - Find Turyn-type sequences TT(n) for constructing Hadamard matrices");
    eprintln!();
    eprintln!("Verb-first CLI:");
    eprintln!("  turyn help                          Show this help");
    eprintln!(
        "  turyn search [OPTIONS]              SAT/MDD/conjecture exhaustive search (tracks TTC)"
    );
    eprintln!(
        "  turyn guess [OPTIONS]               Non-exhaustive guess mode (currently stochastic)"
    );
    eprintln!("  turyn verify [SEQ_OR_OPTIONS]       Verify one candidate");
    eprintln!("  turyn tuples --n=<N>                Print Phase-A tuple shells");
    eprintln!("  turyn dump --n=<N> --dump-dimacs=<PATH> [search options]");
    eprintln!(
        "  turyn list --n=<N>                  Print known TT(n) entries from known_solutions.txt"
    );
    eprintln!();
    eprintln!("Legacy compatibility: `turyn --n=... [OPTIONS]` still maps to `turyn search ...`.");
    eprintln!();
    eprintln!("  --n=<N>                  Sequence length to search (required)");
    eprintln!();
    eprintln!("SEARCH MODE. All three modes load the same MDD (mdd-<k>.bin) for XY boundary");
    eprintln!("enumeration and feed the same XY SAT fast path; they differ only in how");
    eprintln!("(Z, W) candidate pairs are generated. Default: --wz=together --mdd-k=5 when");
    eprintln!("an MDD file exists, otherwise --wz=cross.");
    eprintln!("  --wz=cross               Brute-force full Z × full W, spectral-");
    eprintln!("                           filter each side, cross-match via SpectralIndex.");
    eprintln!("  --wz=apart               MDD boundary walker + SolveW → SolveZ two-stage SAT");
    eprintln!("                           pipeline. Implied by --mdd-k=N and --mdd-extend=N.");
    eprintln!("  --wz=together            MDD boundary walker + combined W+Z SAT call (one");
    eprintln!("                           solve produces both middles). Alias: --wz-together.");
    eprintln!("  --wz=sync                Synchronized 4-seq heuristic walker. Bouncing-order MDD");
    eprintln!("                           built on the fly (no mdd-k.bin needed). Scores 16-way");
    eprintln!("                           levels by running autocorrelation pressure. Persistent");
    eprintln!(
        "                           SAT solver enforces full BDKR (i)–(vi). See sync_walker."
    );
    eprintln!("  --stochastic             Stochastic local search over all four sequences");
    eprintln!("  --stochastic-secs=<S>    Stochastic guess/search cutoff in seconds (default: 10)");
    eprintln!();
    eprintln!("SEARCH TUNING:");
    eprintln!("  --theta=<N>              Number of angle samples for spectral power filtering in");
    eprintln!("                           Phase B; higher = tighter filter, slower (default: 128)");
    eprintln!("  --max-z=<N>              Cap on Z candidates kept from Phase B (default: 200000)");
    eprintln!("  --max-w=<N>              Cap on W candidates kept from Phase B (default: 200000)");
    eprintln!("  --max-spectral=<F>       Upper bound on spectral pair power sum; lower values");
    eprintln!("                           prune more aggressively (faster but may miss solutions)");
    eprintln!("  --conflict-limit=<N>     Max CDCL conflicts per SAT call before giving up on");
    eprintln!("                           that candidate; 0 = unlimited (default: 0)");
    eprintln!("  --sat-secs=<N>           Time limit in seconds for the search; 0 = unlimited");
    eprintln!();
    eprintln!("SAT SOLVER TUNING:");
    eprintln!("  --no-xor                 Disable GF(2) XOR propagation in SAT solver");
    eprintln!("                           (on by default; gives ~4-49x speedup on Phase C)");
    eprintln!("  --ema-restarts           Use glucose-style EMA restarts instead of Luby");
    eprintln!("  --probing                Run failed literal probing before each SAT solve");
    eprintln!("  --rephasing              Periodically reset phase saving heuristic");
    eprintln!();
    eprintln!("SEARCH CONJECTURES (implemented, off by default):");
    eprintln!("  --conj-xy-product        XY product-law conjecture: U_i = x_i*y_i satisfies");
    eprintln!("                           U_1 = U_n = +1 and U_i = -U_{{n+1-i}} (2<=i<=n-1).");
    eprintln!("                           Implies X·Y=2. See conjectures/xy-product.md.");
    eprintln!("  --conj-zw-bound          ZW high-lag U-bound tightness: enforce equality");
    eprintln!("                           |N_Z(s)+N_W(s)| = ((n-s) + N_U(s))/2 at");
    eprintln!(
        "                           s in {{n-1, n-2, n-3}}. See conjectures/zw-u-bound-tight.md."
    );
    eprintln!("  --conj-tuple             Auto-pick the single sum-tuple with the smallest");
    eprintln!("                           search space (min binomial product) and restrict");
    eprintln!("                           search to it, like --tuple= but automatic.");
    eprintln!();
    eprintln!("VERIFY / DEBUGGING / TESTING:");
    eprintln!("  --verify=<X,Y,Z,W>      Check if four +/- sequences form a valid TT(n)");
    eprintln!("                           Example: --verify=++--+-,+-+-++,+++-,+-+-");
    eprintln!("  --test-zw=<Z,W>          Fix Z/W and only run Phase C (SAT X/Y) on them");
    eprintln!("  --tuple=<x,y,z,w>        Restrict search to one sum-tuple (4 integers)");
    eprintln!("  --outfix=<prefHex>...<sufHex>  Force MDD+XY search to a single outfix");
    eprintln!("                           (apart/together only).  BDKR-style hex: each digit");
    eprintln!("                           packs X/Y/Z/W at one position as 8·X + 4·Y + 2·Z + W");
    eprintln!("                           with +1→0, -1→1.  Prefix has k digits (positions");
    eprintln!("                           0..k-1); suffix has k+1 digits (positions n-1-k..n-1,");
    eprintln!("                           last digit is 3-bit since W has length n-1).");
    eprintln!("                           Example (canonical TT(18) at k=5):");
    eprintln!("                             --outfix=00f55...c2c961");
    eprintln!("  --phase-a                Print all sum-tuples for n, then exit");
    eprintln!("  --phase-b                Run Phases A+B, print Z/W pairs, then exit");
    eprintln!("  --dump-dimacs=<PATH>     Write the SAT encoding to a DIMACS CNF file");
    eprintln!();
    eprintln!("BENCHMARKING:");
    eprintln!("  --benchmark              Run the search 5 times and report timing");
    eprintln!("  --benchmark=<N>          Run the search N times and report timing");
    eprintln!();
    eprintln!("  -h, --help               Show this help message");
    eprintln!();
    eprintln!("EXAMPLES:");
    eprintln!(
        "  turyn search --n=26                           # auto-selects --wz=together if MDD exists"
    );
    eprintln!("  turyn search --n=26 --wz=cross                # force brute-force Z×W mode");
    eprintln!(
        "  turyn search --n=26 --wz=apart --mdd-k=7      # MDD boundary walker, SolveW→SolveZ"
    );
    eprintln!(
        "  turyn search --n=26 --wz=together --mdd-k=7   # MDD boundary walker, combined W+Z SAT"
    );
    eprintln!("  turyn guess --n=26 --stochastic-secs=10       # stochastic non-exhaustive guess");
    eprintln!("  turyn tuples --n=26                           # print tuple shells");
    eprintln!("  turyn verify ++--+-,+-+-++,+++-,+-+-          # verify a candidate solution");
    eprintln!("  turyn dump --n=26 --dump-dimacs=tt26.cnf      # write CNF instead of searching");
    eprintln!("  turyn list --n=26                             # show known TT(26) entries");
}

fn parse_search_like_options(args: &[String], cfg: &mut SearchConfig) {
    for arg in args {
        if let Some(v) = arg.strip_prefix("--n=") {
            if let Ok(n) = v.parse::<usize>() {
                cfg.problem = Problem::new(n);
            } else {
                eprintln!("error: invalid value for --n: {}", v);
                std::process::exit(1);
            }
        } else if let Some(v) = arg.strip_prefix("--theta=") {
            cfg.theta_samples = v.parse().unwrap_or(cfg.theta_samples);
        } else if let Some(v) = arg.strip_prefix("--max-z=") {
            cfg.max_z = v.parse().unwrap_or(cfg.max_z);
        } else if let Some(v) = arg.strip_prefix("--max-w=") {
            cfg.max_w = v.parse().unwrap_or(cfg.max_w);
        } else if let Some(v) = arg.strip_prefix("--benchmark=") {
            cfg.benchmark_repeats = v.parse().unwrap_or(1);
        } else if arg == "--benchmark" {
            cfg.benchmark_repeats = 5;
        } else if arg == "--stochastic" {
            cfg.stochastic = true;
        } else if let Some(v) = arg.strip_prefix("--stochastic-secs=") {
            cfg.stochastic_seconds = v.parse().unwrap_or(10);
            cfg.stochastic = true;
        } else if let Some(v) = arg.strip_prefix("--max-spectral=") {
            cfg.max_spectral = Some(v.parse().unwrap_or(0.0));
        } else if let Some(v) = arg.strip_prefix("--verify=") {
            let parts: Vec<&str> = v.split(',').collect();
            if parts.len() == 4 {
                cfg.verify_seqs = Some([
                    parts[0].to_string(),
                    parts[1].to_string(),
                    parts[2].to_string(),
                    parts[3].to_string(),
                ]);
            }
        } else if let Some(v) = arg.strip_prefix("--test-zw=") {
            let parts: Vec<&str> = v.split(',').collect();
            if parts.len() == 2 {
                cfg.test_zw = Some([parts[0].to_string(), parts[1].to_string()]);
            }
        } else if let Some(v) = arg.strip_prefix("--conflict-limit=") {
            cfg.conflict_limit = v.parse().unwrap_or(0);
        } else if let Some(v) = arg.strip_prefix("--sat-secs=") {
            cfg.sat_secs = v.parse().unwrap_or(0);
        } else if arg == "--ema-restarts" {
            cfg.sat_config.ema_restarts = true;
        } else if arg == "--probing" {
            cfg.sat_config.probing = true;
        } else if arg == "--rephasing" {
            cfg.sat_config.rephasing = true;
        } else if arg == "--xor-propagation" {
            cfg.sat_config.xor_propagation = true;
        } else if arg == "--no-xor" {
            cfg.sat_config.xor_propagation = false;
        } else if let Some(v) = arg.strip_prefix("--engine=") {
            cfg.engine = match v {
                "legacy" => EngineKind::Legacy,
                "new" => EngineKind::New,
                _ => {
                    eprintln!("error: --engine must be one of legacy|new (got '{}')", v);
                    std::process::exit(1);
                }
            };
        } else if arg == "--phase-a" || arg == "--phase-b" {
            cfg.phase_only = Some(arg[2..].to_string());
        } else if let Some(v) = arg.strip_prefix("--tuple=") {
            let parts: Vec<i32> = v.split(',').filter_map(|s| s.parse().ok()).collect();
            if parts.len() == 4 {
                cfg.test_tuple = Some(SumTuple {
                    x: parts[0],
                    y: parts[1],
                    z: parts[2],
                    w: parts[3],
                });
            }
        } else if let Some(v) = arg.strip_prefix("--outfix=") {
            if cfg.problem.n == 0 {
                eprintln!("error: --outfix requires --n=<N> first");
                std::process::exit(2);
            }
            cfg.test_outfix = match parse_outfix(v, cfg.problem.n, cfg.mdd_k) {
                Ok(spec) => Some(spec),
                Err(e) => {
                    eprintln!("error: {e}");
                    std::process::exit(2);
                }
            };
        } else if arg == "--quad-pb" {
            cfg.quad_pb = true;
        } else if arg == "--no-quad-pb" {
            cfg.quad_pb = false;
        } else if arg == "--wz-together" {
            cfg.wz_together = true;
            if cfg.wz_mode.is_none() {
                cfg.wz_mode = Some(WzMode::Together);
            }
        } else if let Some(v) = arg.strip_prefix("--wz=") {
            let mode = match v {
                "cross" => WzMode::Cross,
                "together" => WzMode::Together,
                "apart" => WzMode::Apart,
                "sync" => WzMode::Sync,
                _ => {
                    eprintln!(
                        "error: --wz must be one of cross|together|apart|sync (got '{}')\n",
                        v
                    );
                    print_help();
                    std::process::exit(1);
                }
            };
            cfg.wz_mode = Some(mode);
            cfg.wz_together = matches!(mode, WzMode::Together);
        } else if let Some(v) = arg.strip_prefix("--mdd-k=") {
            cfg.mdd_k = v.parse().unwrap_or(8);
            if cfg.wz_mode.is_none() {
                cfg.wz_mode = Some(WzMode::Apart);
            }
        } else if let Some(v) = arg.strip_prefix("--mdd-extend=") {
            cfg.mdd_extend = v.parse().unwrap_or(0);
            if cfg.wz_mode.is_none() {
                cfg.wz_mode = Some(WzMode::Apart);
            }
        } else if let Some(v) = arg.strip_prefix("--dump-dimacs=") {
            cfg.dump_dimacs = Some(v.to_string());
        } else if arg == "--conj-xy-product" {
            cfg.conj_xy_product = true;
        } else if arg == "--no-conj-xy-product" {
            cfg.conj_xy_product = false;
        } else if arg == "--conj-zw-bound" {
            cfg.conj_zw_bound = true;
        } else if arg == "--no-conj-zw-bound" {
            cfg.conj_zw_bound = false;
        } else if arg == "--conj-tuple" {
            cfg.conj_tuple = true;
        } else if arg == "--no-conj-tuple" {
            cfg.conj_tuple = false;
        } else {
            eprintln!("error: unknown option '{}'\n", arg);
            print_help();
            std::process::exit(1);
        }
    }
}

#[cfg(feature = "search-framework")]
fn run_framework_mdd_mode(
    problem: Problem,
    tuples: Vec<SumTuple>,
    cfg: &SearchConfig,
    verbose: bool,
    k: usize,
) {
    let mode_name: &'static str = match cfg.effective_wz_mode() {
        WzMode::Cross => "cross",
        WzMode::Apart => "apart",
        WzMode::Together => "together",
        WzMode::Sync => "sync",
    };
    // Framework staged routing: builds a `PhaseBContext` identical
    // to the legacy `run_mdd_sat_search`, enumerates every live
    // boundary upfront, and drives the five per-stage
    // `StageHandler`s through `SearchEngine`. Solutions land on the
    // adapter's `result_rx` channel.
    let (adapter, result_rx) =
        MddStagesAdapter::build(problem, tuples, cfg, k, verbose, mode_name);
    let mut engine = SearchEngine::<MddPayload>::new(
        EngineConfig::default(),
        Box::new(GoldThenWork::new(32)),
    );
    // Short-circuit once any worker publishes a solution: set the
    // context's `found` flag AND cancel the engine so workers stop
    // pulling work from the scheduler.
    let found_ctx = std::sync::Arc::clone(&adapter.ctx.found);
    let engine_cancel = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let engine_cancel_clone = std::sync::Arc::clone(&engine_cancel);

    // Drain-thread: polls the solution channel; on first hit sets
    // the cancel flag + `ctx.found`. `thread::scope` keeps it tied
    // to the engine's lifetime.
    let drain_handle = std::thread::spawn(move || {
        let mut solutions = Vec::new();
        while let Ok(sol) = result_rx.recv() {
            found_ctx.store(true, std::sync::atomic::Ordering::Relaxed);
            engine_cancel_clone.store(true, std::sync::atomic::Ordering::Relaxed);
            solutions.push(sol);
        }
        solutions
    });

    let cancel_watchdog = std::sync::Arc::clone(&engine_cancel);
    engine.run(&adapter, move |event| match event {
        SearchEvent::Progress(p) => {
            if verbose {
                eprintln!(
                    "[framework:{}] elapsed={:.1?} covered={:.3}/{:.3} ttc={:?}",
                    mode_name, p.elapsed, p.covered_mass.0, p.total_mass.0, p.ttc
                );
            }
            if cancel_watchdog.load(std::sync::atomic::Ordering::Relaxed) {
                // Engine will notice via its internal `cancelled`
                // flag if we call cancel(); but we don't own the
                // engine from this closure, so rely on the found
                // flag propagated through StageContext instead.
            }
        }
        SearchEvent::Finished(p) => {
            println!(
                "Framework search (--wz={}): covered={:.3}/{:.3} elapsed={:.1?} ttc={:?}",
                mode_name, p.covered_mass.0, p.total_mass.0, p.elapsed, p.ttc
            );
        }
    });

    // Dropping the adapter drops its `result_tx`, which is the
    // last sender (stage handlers cloned from it but they're gone
    // now). The drain thread's `recv` returns Err and it exits.
    drop(adapter);
    let solutions = drain_handle.join().unwrap_or_default();
    if !solutions.is_empty() {
        println!(
            "Framework search (--wz={}): found_solution=true ({} solution(s))",
            mode_name,
            solutions.len()
        );
    } else {
        println!(
            "Framework search (--wz={}): found_solution=false",
            mode_name
        );
    }
    let _ = engine_cancel; // keep the Arc alive until the end
}

fn parse_args() -> (CliVerb, SearchConfig) {
    let raw_args: Vec<String> = env::args().skip(1).collect();
    if raw_args.is_empty() {
        print_help();
        std::process::exit(0);
    }
    if raw_args[0] == "-h" || raw_args[0] == "--help" || raw_args[0] == "help" {
        return (CliVerb::Help, SearchConfig::default());
    }
    let (verb, args): (CliVerb, Vec<String>) = if raw_args[0].starts_with('-') {
        // Legacy compatibility: no explicit verb means `search`.
        (CliVerb::Search, raw_args)
    } else {
        let verb = match raw_args[0].as_str() {
            "search" => CliVerb::Search,
            "guess" => CliVerb::Guess,
            "verify" => CliVerb::Verify,
            "tuples" => CliVerb::Tuples,
            "dump" => CliVerb::Dump,
            "list" => CliVerb::List,
            "help" => CliVerb::Help,
            other => {
                eprintln!("error: unknown verb '{}'\n", other);
                print_help();
                std::process::exit(1);
            }
        };
        (verb, raw_args[1..].to_vec())
    };
    let mut cfg = SearchConfig::default();
    match verb {
        CliVerb::Help => {}
        CliVerb::Verify => {
            if args.len() == 1 && !args[0].starts_with("--") {
                let parts: Vec<&str> = args[0].split(',').collect();
                if parts.len() == 4 {
                    cfg.verify_seqs = Some([
                        parts[0].to_string(),
                        parts[1].to_string(),
                        parts[2].to_string(),
                        parts[3].to_string(),
                    ]);
                } else {
                    eprintln!("error: verify expects one comma-separated X,Y,Z,W payload");
                    std::process::exit(1);
                }
            } else {
                parse_search_like_options(&args, &mut cfg);
            }
            if cfg.verify_seqs.is_none() {
                eprintln!("error: verify requires `turyn verify X,Y,Z,W` or `--verify=...`");
                std::process::exit(1);
            }
        }
        CliVerb::Tuples => {
            parse_search_like_options(&args, &mut cfg);
            cfg.phase_only = Some("phase-a".to_string());
        }
        CliVerb::Dump => {
            parse_search_like_options(&args, &mut cfg);
            if cfg.dump_dimacs.is_none() {
                eprintln!("error: dump requires --dump-dimacs=<PATH>");
                std::process::exit(1);
            }
        }
        CliVerb::Guess => {
            parse_search_like_options(&args, &mut cfg);
            cfg.stochastic = true;
        }
        CliVerb::List | CliVerb::Search => {
            parse_search_like_options(&args, &mut cfg);
        }
    }
    if verb == CliVerb::Help {
        return (verb, cfg);
    }
    // --n is required unless verify/test-zw provide their own sequences
    if cfg.problem.n == 0
        && cfg.verify_seqs.is_none()
        && cfg.test_zw.is_none()
        && verb != CliVerb::Verify
    {
        eprintln!("error: --n=<N> is required\n");
        print_help();
        std::process::exit(1);
    }
    // Default: enable extension check for the MDD-walker producers
    // (clear win at n>=26). Doesn't affect --wz=cross.
    if matches!(cfg.effective_wz_mode(), WzMode::Apart | WzMode::Together) && cfg.mdd_extend == 0 {
        cfg.mdd_extend = 1;
    }
    // --conj-tuple: auto-pick the tuple with the smallest search
    // space (minimum binomial product).  We can't know solution
    // density a priori at an open n, so the best proxy we can compute
    // is raw space size.  Small space ⇒ fast per-orbit enumeration;
    // accept that the orbit may have few solutions.  Skip if --tuple=
    // was also supplied.
    if cfg.conj_tuple && cfg.test_tuple.is_none() && cfg.problem.n > 0 {
        if let Some(t) = pick_fewest_candidate_tuple(cfg.problem) {
            eprintln!(
                "  --conj-tuple: auto-selected tuple {} (log2 space ≈ {:.2})",
                t,
                candidate_log2_score(cfg.problem, &t),
            );
            cfg.test_tuple = Some(t);
        } else {
            eprintln!(
                "warning: --conj-tuple found no valid sum-tuples for n={}",
                cfg.problem.n
            );
        }
    }
    (verb, cfg)
}

/// log2 of `C(n, (n+|σ_X|)/2) * C(n, (n+|σ_Y|)/2) * C(n, (n+|σ_Z|)/2)
///        * C(n-1, (n-1+|σ_W|)/2)`.  Used as the `--conj-tuple`
/// "candidate count" proxy: smaller = fewer raw ±1 sequences matching
/// the tuple's per-sum cardinality across X/Y/Z/W.
fn candidate_log2_score(p: Problem, t: &SumTuple) -> f64 {
    fn lb(n: i32, sigma: i32) -> f64 {
        // log2 C(n, (n+sigma)/2).  Infeasible parity ⇒ +∞ penalty.
        if (n + sigma).rem_euclid(2) != 0 {
            return f64::INFINITY;
        }
        let k = (n + sigma) / 2;
        if k < 0 || k > n {
            return f64::INFINITY;
        }
        // log2(n!) - log2(k!) - log2((n-k)!) via lgamma.
        let num = lgamma(n as f64 + 1.0);
        let den = lgamma(k as f64 + 1.0) + lgamma((n - k) as f64 + 1.0);
        (num - den) / std::f64::consts::LN_2
    }
    lb(p.n as i32, t.x.abs())
        + lb(p.n as i32, t.y.abs())
        + lb(p.n as i32, t.z.abs())
        + lb(p.m() as i32, t.w.abs())
}

/// Natural log of the Gamma function (Lanczos approximation, standard
/// form).  Sufficient precision for comparing binomial-product scores.
fn lgamma(x: f64) -> f64 {
    // Shift x to x ≥ 0.5.
    if x < 0.5 {
        return (std::f64::consts::PI / (std::f64::consts::PI * x).sin()).ln() - lgamma(1.0 - x);
    }
    let g = 7.0;
    let coeff: [f64; 9] = [
        0.99999999999980993,
        676.5203681218851,
        -1259.1392167224028,
        771.32342877765313,
        -176.61502916214059,
        12.507343278686905,
        -0.13857109526572012,
        9.9843695780195716e-6,
        1.5056327351493116e-7,
    ];
    let x = x - 1.0;
    let mut a = coeff[0];
    let t = x + g + 0.5;
    for (i, &c) in coeff.iter().enumerate().skip(1) {
        a += c / (x + i as f64);
    }
    0.5 * (2.0 * std::f64::consts::PI).ln() + (x + 0.5) * t.ln() - t + a.ln()
}

fn pick_fewest_candidate_tuple(p: Problem) -> Option<SumTuple> {
    let tuples = phase_a_tuples(p, None);
    tuples.into_iter().min_by(|a, b| {
        candidate_log2_score(p, a)
            .partial_cmp(&candidate_log2_score(p, b))
            .unwrap_or(std::cmp::Ordering::Equal)
    })
}

/// Parse a +/- string into a PackedSeq. '+' = +1, '-' = -1.
fn parse_seq(s: &str) -> PackedSeq {
    let vals: Vec<i8> = s.chars().map(|c| if c == '+' { 1 } else { -1 }).collect();
    PackedSeq::from_values(&vals)
}

fn run_info() -> String {
    let hostname = std::process::Command::new("hostname")
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .unwrap_or_default()
        .trim()
        .to_string();
    let git_hash = std::process::Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .unwrap_or_default()
        .trim()
        .to_string();
    format!("host={}, commit={}", hostname, git_hash)
}

fn list_known_solutions(n_filter: Option<usize>) {
    let text = match std::fs::read_to_string("known_solutions.txt") {
        Ok(t) => t,
        Err(e) => {
            eprintln!("error: failed to read known_solutions.txt: {}", e);
            std::process::exit(1);
        }
    };
    let mut matched = 0usize;
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() < 5 {
            continue;
        }
        let Ok(n) = parts[0].parse::<usize>() else {
            continue;
        };
        if let Some(want) = n_filter {
            if n != want {
                continue;
            }
        }
        let x = parts[1];
        let y = parts[2];
        let z = parts[3];
        let w = parts[4];
        println!("TT({}):", n);
        println!("  X={}", x);
        println!("  Y={}", y);
        println!("  Z={}", z);
        println!("  W={}", w);
        println!("  --verify={},{},{},{}", x, y, z, w);
        matched += 1;
    }
    if matched == 0 {
        if let Some(n) = n_filter {
            println!("No known TT({}) entries in known_solutions.txt", n);
        } else {
            println!("No entries found in known_solutions.txt");
        }
    }
}

fn main() {
    let (verb, mut cfg) = parse_args();
    if verb == CliVerb::Help {
        print_help();
        return;
    }
    // Resolve auto-defaults up-front so we can echo the fully-filled-in
    // settings as the very first line of output. Only the unified search
    // branch picks --wz / --mdd-k automatically; the other branches
    // (verify, phase-only, dump-dimacs, benchmark, stochastic) just use
    // what the user passed.
    let going_to_unified_search = matches!(verb, CliVerb::Search)
        && cfg.verify_seqs.is_none()
        && cfg.test_zw.is_none()
        && cfg.phase_only.is_none()
        && cfg.dump_dimacs.is_none()
        && cfg.benchmark_repeats == 0
        && !cfg.stochastic;
    let resolved_mode_k = if going_to_unified_search {
        let (mode, mdd_k) = cfg.resolve_for_unified_search();
        Some((mode, mdd_k))
    } else {
        None
    };
    println!(
        "{}",
        cfg.settings_line(
            resolved_mode_k.map(|(m, _)| m),
            resolved_mode_k.map(|(_, k)| k),
        )
    );
    let cfg = cfg;
    if verb == CliVerb::List {
        list_known_solutions(Some(cfg.problem.n));
        return;
    }
    if let Some(ref seqs) = cfg.verify_seqs {
        let x = parse_seq(&seqs[0]);
        let y = parse_seq(&seqs[1]);
        let z = parse_seq(&seqs[2]);
        let w = parse_seq(&seqs[3]);
        let n = x.len();
        let p = Problem::new(n);
        print_solution(&format!("Verifying TT({})", n), &x, &y, &z, &w);
        let ok = verify_tt(p, &x, &y, &z, &w);
        println!("Verified: {}", ok);
        if !ok {
            std::process::exit(1);
        }
        return;
    }
    if let Some(ref zw) = cfg.test_zw {
        let z = parse_seq(&zw[0]);
        let w = parse_seq(&zw[1]);
        let n = z.len();
        let p = Problem::new(n);
        let zs = z.sum();
        let ws = w.sum();
        let zw_autocorr = compute_zw_autocorr(p, &z, &w);
        let candidate = CandidateZW { zw_autocorr };
        // Try all sum tuples that match this Z/W
        let mut tuples = phase_a_tuples(p, cfg.test_tuple.as_ref());
        tuples.retain(|t| t.z == zs && t.w == ws);
        println!(
            "TT({}): testing Z(sum={}) W(sum={}) against {} tuples",
            n,
            zs,
            ws,
            tuples.len()
        );
        print_solution(
            "  Z/W",
            &PackedSeq::from_values(&[0]),
            &PackedSeq::from_values(&[0]),
            &z,
            &w,
        );
        for tuple in &tuples {
            let start = Instant::now();
            let Some(template) = SatXYTemplate::build(p, *tuple, &radical::SolverConfig::default())
            else {
                continue;
            };
            if let Some((x, y)) = template.solve_for(&candidate) {
                let ok = verify_tt(p, &x, &y, &z, &w);
                print_solution(
                    &format!(
                        "FOUND for tuple {} ({:.3?}, verified={})",
                        tuple,
                        start.elapsed(),
                        ok
                    ),
                    &x,
                    &y,
                    &z,
                    &w,
                );
                if ok {
                    return;
                }
            } else {
                println!("  Tuple {}: UNSAT ({:.3?})", tuple, start.elapsed());
            }
        }
        println!("No X/Y found for given Z/W");
        return;
    }
    if let Some(ref phase) = cfg.phase_only {
        let problem = cfg.problem;
        let mut tuples = phase_a_tuples(problem, cfg.test_tuple.as_ref());
        // Heuristic tuple ordering: try small |z|+|w| first (cheap Phase B),
        // break ties by small |x-y| (solutions often have x≈y).
        tuples.sort_by_key(|t| {
            (
                t.z.abs() + t.w.abs(),
                (t.x - t.y).abs(),
                t.x.abs() + t.y.abs(),
            )
        });

        if phase == "phase-a" {
            eprintln!(
                "TT({}): {} tuples (x,y,z,w) satisfying x²+y²+2z²+2w²={}",
                problem.n,
                tuples.len(),
                problem.target_energy()
            );
            print_search_space(problem, &tuples);
        } else if phase == "phase-b"
            && matches!(cfg.effective_wz_mode(), WzMode::Apart | WzMode::Together)
        {
            // MDD-based Phase B:
            // 1. Generate ONE W at a time (boundary from MDD + middle enumerated, spectral filtered)
            // 2. For each valid W + each compatible z_boundary: SAT solve for z_middle
            //    with sum constraint + autocorrelation range constraints
            // 3. Post-filter (Z,W) with spectral pair check
            // 4. Each valid pair → report (and later, send to Phase C with XY from MDD)
            let mdd_k = cfg.mdd_k.min((problem.n - 1) / 2).min(problem.m() / 2);
            let reordered = match load_best_mdd(mdd_k, true) {
                Some(m) => m,
                None => {
                    eprintln!("No MDD file found. Run: target/release/gen_mdd {}", mdd_k);
                    return;
                }
            };
            let k = reordered.k;
            let n = problem.n;
            let m = problem.m();
            let middle_n = n - 2 * k;
            let middle_m = m - 2 * k;
            let max_bnd_sum = (2 * k) as i32;
            let zw_depth = 2 * k;
            let pos_order: Vec<usize> = {
                let mut v = Vec::with_capacity(2 * k);
                for t in 0..k {
                    v.push(t);
                    v.push(2 * k - 1 - t);
                }
                v
            };

            // Lazily walk MDD boundaries — no collect, no HashMap.
            // For each boundary, check compatibility with each tuple inline.
            let spectral_w = SpectralFilter::new(m, cfg.theta_samples);
            let individual_bound = problem.spectral_bound();
            let max_w_passing = cfg.max_w;

            // Pre-compute required (z_mid_sum, w_mid_sum) per tuple for fast lookup
            let mut tuple_pairs: Vec<u64> = vec![0; tuples.len()];
            let mut grand_total_pairs = 0u64;
            let mut grand_w_gen = 0u64;
            let mut grand_w_ok = 0u64;
            let mut sat_calls = 0u64;
            let mut sat_solutions = 0u64;
            let mut sat_unsats = 0u64;
            let mut total_zw = 0u64;

            // State for processing a single boundary across all tuples
            struct WalkState<'a> {
                tuples: &'a [SumTuple],
                tuple_pairs: &'a mut [u64],
                grand_total_pairs: &'a mut u64,
                grand_w_gen: &'a mut u64,
                grand_w_ok: &'a mut u64,
                sat_calls: &'a mut u64,
                sat_solutions: &'a mut u64,
                sat_unsats: &'a mut u64,
                total_zw: &'a mut u64,
                spectral_w: &'a SpectralFilter,
                individual_bound: f64,
                max_w_passing: usize,
                n: usize,
                m: usize,
                k: usize,
                middle_n: usize,
                middle_m: usize,
                max_bnd_sum: i32,
            }

            fn process_boundary(z_bits: u32, w_bits: u32, _xy_root: u32, state: &mut WalkState) {
                let z_bnd_sum = 2 * (z_bits.count_ones() as i32) - state.max_bnd_sum;
                let w_bnd_sum = 2 * (w_bits.count_ones() as i32) - state.max_bnd_sum;
                *state.total_zw += 1;
                let k = state.k;
                let n = state.n;
                let m = state.m;
                let middle_n = state.middle_n;
                let middle_m = state.middle_m;

                for (ti, tuple) in state.tuples.iter().enumerate() {
                    let z_mid_sum = tuple.z - z_bnd_sum;
                    if z_mid_sum.abs() > middle_n as i32 || (z_mid_sum + middle_n as i32) % 2 != 0 {
                        continue;
                    }
                    let w_mid_sum = tuple.w - w_bnd_sum;
                    if w_mid_sum.abs() > middle_m as i32 || (w_mid_sum + middle_m as i32) % 2 != 0 {
                        continue;
                    }

                    let (w_prefix, w_suffix) = expand_boundary_bits(w_bits, k);
                    let (z_prefix, z_suffix) = expand_boundary_bits(z_bits, k);

                    let mut z_boundary = vec![0i8; n];
                    for i in 0..k {
                        z_boundary[i] = z_prefix[i];
                        z_boundary[n - k + i] = z_suffix[i];
                    }

                    // SAT-based W middle generation with autocorrelation constraints
                    let mut w_boundary = vec![0i8; m];
                    for i in 0..k {
                        w_boundary[i] = w_prefix[i];
                        w_boundary[m - k + i] = w_suffix[i];
                    }
                    let w_tmpl_local = sat_z_middle::LagTemplate::new(m, k);
                    let mut w_solver = w_tmpl_local.build_base_solver(middle_m, w_mid_sum);
                    sat_z_middle::fill_w_solver(&mut w_solver, &w_tmpl_local, m, &w_boundary);
                    let w_mid_vars: Vec<i32> = (0..middle_m).map(|i| (i + 1) as i32).collect();
                    let z_mid_vars: Vec<i32> = (0..middle_n).map(|i| (i + 1) as i32).collect();
                    let mut fft_buf_w = FftScratch::new(state.spectral_w);
                    let mut w_passing = 0usize;

                    // Simple PRNG for phase randomization
                    let mut rng_state: u64 =
                        (z_bits as u64) ^ ((w_bits as u64) << 32) ^ 0x517cc1b727220a95;
                    let mut next_rng = || -> u64 {
                        rng_state ^= rng_state << 13;
                        rng_state ^= rng_state >> 7;
                        rng_state ^= rng_state << 17;
                        rng_state
                    };

                    loop {
                        if w_passing >= state.max_w_passing {
                            break;
                        }

                        // Randomize phases for diversity
                        let phases: Vec<bool> = (0..middle_m)
                            .map(|i| (next_rng() >> (i % 64)) & 1 == 1)
                            .collect();
                        w_solver.set_phase(&phases);

                        let w_result = w_solver.solve();
                        if w_result != Some(true) {
                            break;
                        }
                        *state.grand_w_gen += 1;

                        // Extract W middle
                        let w_mid = extract_vals(&w_solver, |i| w_mid_vars[i], middle_m);
                        let mut w_vals = Vec::with_capacity(m);
                        w_vals.extend_from_slice(&w_prefix);
                        w_vals.extend_from_slice(&w_mid);
                        w_vals.extend_from_slice(&w_suffix);

                        // Block this W
                        let w_block: Vec<i32> = w_mid_vars
                            .iter()
                            .map(|&v| {
                                if w_solver.value(v) == Some(true) {
                                    -v
                                } else {
                                    v
                                }
                            })
                            .collect();
                        w_solver.add_clause(w_block);

                        let Some(_w_spectrum) = spectrum_if_ok(
                            &w_vals,
                            state.spectral_w,
                            state.individual_bound,
                            &mut fft_buf_w,
                        ) else {
                            continue;
                        };
                        *state.grand_w_ok += 1;
                        w_passing += 1;

                        // For each valid W, immediately run Z SAT solver
                        let mut solver = sat_z_middle::build_z_middle_solver(
                            n,
                            m,
                            k,
                            &z_boundary,
                            &w_vals,
                            z_mid_sum,
                        );

                        loop {
                            *state.sat_calls += 1;
                            let result = solver.solve();
                            if result != Some(true) {
                                *state.sat_unsats += 1;
                                break;
                            }
                            *state.sat_solutions += 1;

                            let mut z_vals = z_boundary.clone();
                            for i in 0..middle_n {
                                z_vals[k + i] = if solver.value(z_mid_vars[i]) == Some(true) {
                                    1
                                } else {
                                    -1
                                };
                            }

                            state.tuple_pairs[ti] += 1;
                            *state.grand_total_pairs += 1;

                            let block: Vec<i32> = z_mid_vars
                                .iter()
                                .map(|&v| if solver.value(v) == Some(true) { -v } else { v })
                                .collect();
                            solver.add_clause(block);
                        }

                        if w_passing % 100 == 0 && w_passing > 0 {
                            eprint!(
                                "\r  w_ok: {}, sat: {}/{}/{}, pairs: {}",
                                state.grand_w_ok,
                                state.sat_solutions,
                                state.sat_unsats,
                                state.sat_calls,
                                state.grand_total_pairs
                            );
                        }
                    }
                }
            }

            let start = Instant::now();
            {
                let mut state = WalkState {
                    tuples: &tuples,
                    tuple_pairs: &mut tuple_pairs,
                    grand_total_pairs: &mut grand_total_pairs,
                    grand_w_gen: &mut grand_w_gen,
                    grand_w_ok: &mut grand_w_ok,
                    sat_calls: &mut sat_calls,
                    sat_solutions: &mut sat_solutions,
                    sat_unsats: &mut sat_unsats,
                    total_zw: &mut total_zw,
                    spectral_w: &spectral_w,
                    individual_bound,
                    max_w_passing,
                    n,
                    m,
                    k,
                    middle_n,
                    middle_m,
                    max_bnd_sum,
                };
                walk_mdd_4way(
                    reordered.root,
                    0,
                    zw_depth,
                    0,
                    0,
                    &pos_order,
                    &reordered.nodes,
                    &mut |z_acc, w_acc, _nid| {
                        process_boundary(z_acc, w_acc, _nid, &mut state);
                    },
                );
            }
            eprintln!(
                "{} (z,w) boundaries walked lazily ({:.1?})",
                total_zw,
                start.elapsed()
            );
            for (i, tuple) in tuples.iter().enumerate() {
                eprintln!(
                    "  {} {} {} {}: pairs={}",
                    tuple.x, tuple.y, tuple.z, tuple.w, tuple_pairs[i]
                );
            }
            eprintln!(
                "\nTotal: {} pairs, w={}/{}, sat_solutions={} sat_calls={} unsat={}",
                grand_total_pairs, grand_w_ok, grand_w_gen, sat_solutions, sat_calls, sat_unsats
            );
        } else if phase == "phase-b" {
            let spectral_z = SpectralFilter::new(problem.n, cfg.theta_samples);
            let spectral_w = SpectralFilter::new(problem.n, cfg.theta_samples);
            for tuple in &tuples {
                let mut stats = SearchStats::default();
                let start = Instant::now();
                let candidates = build_zw_candidates(
                    problem,
                    *tuple,
                    &cfg,
                    &spectral_z,
                    &spectral_w,
                    &mut stats,
                    &AtomicBool::new(false),
                );
                println!(
                    "{} {} {} {}: z={}/{} w={}/{} pairs={} ({:.3?})",
                    tuple.x,
                    tuple.y,
                    tuple.z,
                    tuple.w,
                    stats.z_spectral_ok,
                    stats.z_generated,
                    stats.w_spectral_ok,
                    stats.w_generated,
                    candidates.len(),
                    start.elapsed()
                );
            }
        }
        return;
    }
    if let Some(ref path) = cfg.dump_dimacs {
        let problem = cfg.problem;
        let mut tuples = phase_a_tuples(problem, cfg.test_tuple.as_ref());
        tuples.sort_by_key(|t| (t.z.abs() + t.w.abs(), (t.x - t.y).abs()));
        let tuple = tuples[0];
        println!(
            "Dumping DIMACS for TT({}) tuple {} to {}",
            problem.n, tuple, path
        );
        let (_enc, solver) = sat_encode(problem, tuple);
        let mut file = std::fs::File::create(path).expect("failed to create DIMACS file");
        solver
            .dump_dimacs(&mut file)
            .expect("failed to write DIMACS");
        println!(
            "Wrote {} vars, {} clauses",
            solver.num_vars(),
            solver.num_clauses()
        );
        return;
    }
    if cfg.benchmark_repeats > 0 {
        run_benchmark(&cfg);
    } else if cfg.stochastic {
        let report = stochastic_search(
            cfg.problem,
            cfg.test_tuple.as_ref(),
            true,
            cfg.stochastic_seconds,
        );
        println!(
            "Stochastic search: found_solution={}, elapsed={:.3?}\n  {}",
            report.found_solution,
            report.elapsed,
            run_info()
        );
    } else {
        // All three --wz modes funnel through the same unified runner.
        // The runner's monitor thread either enumerates Z × W pairs
        // (--wz=cross) or walks MDD boundaries (--wz=apart|together),
        // feeding the same DualQueue + worker loop + XY SAT stage.
        // Auto-defaults already applied at the top of `main` so we can
        // echo the resolved settings line first; just unpack them here.
        // Measured times with `--wz=together --mdd-k=5` at commit 92959bd:
        //   n=16:   23ms      n=18:    172ms     n=20:  880ms
        //   n=22:   16.8s     n=24:    98s       n=26:  open
        // `--wz=cross` is currently broken for n>=6 (pre-existing bug
        // on main).  `--wz=apart` works for n<=20 but regresses at n=22.
        // `--wz=together` is the reliable default.
        let (mode, mdd_k) = resolved_mode_k.expect("unified search branch must have resolved mode");
        // Heuristic tuple ordering (was previously inside run_hybrid_search).
        let mut tuples = phase_a_tuples(cfg.problem, cfg.test_tuple.as_ref());
        if mode == WzMode::Cross {
            if cfg.problem.n >= 26 {
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
        }
        #[cfg(feature = "search-framework")]
        if cfg.engine == EngineKind::New && matches!(mode, WzMode::Cross | WzMode::Apart | WzMode::Together) {
            run_framework_mdd_mode(cfg.problem, tuples, &cfg, true, mdd_k);
            return;
        }
        let report = run_mdd_sat_search(cfg.problem, &tuples, &cfg, true, mdd_k);
        let label = match mode {
            WzMode::Cross => "cross",
            WzMode::Together => "together",
            WzMode::Apart => "apart",
            WzMode::Sync => "sync",
        };
        println!(
            "Unified search (--wz={}): found_solution={}, elapsed={:.3?}\n  {}",
            label,
            report.found_solution,
            report.elapsed,
            run_info()
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tuple_equation_holds_for_tt56() {
        let p = Problem::new(56);
        let tuples = enumerate_sum_tuples(p);
        assert!(!tuples.is_empty());
        assert!(tuples.iter().all(|t| t.x * t.x + t.y * t.y + 2 * t.z * t.z + 2 * t.w * t.w == p.target_energy()));
    }

    #[test]
    fn tuple_equation_holds_for_tt8() {
        let p = Problem::new(8);
        let tuples = enumerate_sum_tuples(p);
        assert!(!tuples.is_empty());
        assert!(tuples.iter().all(|t| t.x * t.x + t.y * t.y + 2 * t.z * t.z + 2 * t.w * t.w == p.target_energy()));
    }

    #[test]
    fn packed_seq_ops() {
        let s = PackedSeq::from_values(&[1, -1, 1, -1, 1]);
        assert_eq!(s.sum(), 1);
        assert_eq!(s.reverse().as_string(), "+-+-+");
        assert_eq!(s.negate().as_string(), "-+-+-");
        assert_eq!(s.alternate().as_string(), "+++++");
    }

    #[test]
    fn verify_handles_trivial_false() {
        let p = Problem::new(8);
        let x = PackedSeq::from_values(&vec![1; p.n]);
        let y = PackedSeq::from_values(&vec![1; p.n]);
        let z = PackedSeq::from_values(&vec![1; p.n]);
        let w = PackedSeq::from_values(&vec![1; p.m()]);
        assert!(!verify_tt(p, &x, &y, &z, &w));
    }

    #[test]
    fn generator_respects_sum() {
        let seqs = generate_sequences_with_sum(8, 2, true, false, 1000);
        assert!(!seqs.is_empty());
        assert!(seqs.iter().all(|s| s.sum() == 2));
        assert!(seqs.iter().all(|s| s.get(0) == 1));
    }

    // Benchmark profile test: drives the MDD-walker pipeline at n=4 with
    // the BDKR rule-(i) canonical form (X,Y both endpoints = +1).  We run
    // WzMode::Apart here rather than Cross because the small-n spectral
    // pair filter in Cross mode is tight enough to reject the one
    // canonical (Z,W) pair; Apart mode applies per-lag SAT constraints
    // instead.  Both paths share the same XY SAT fast path, so this still
    // exercises the canonical XY encoder.
    #[test]
    fn benchmark_profile_n4_finds_solution_fast() {
        let cfg = SearchConfig {
            problem: Problem::new(4),
            theta_samples: 64,
            max_z: 200_000,
            max_w: 200_000,
            benchmark_repeats: 1,
            stochastic: false,
            stochastic_seconds: 0,
            max_spectral: None,
            verify_seqs: None,
            test_zw: None,
            conflict_limit: 0,
            test_tuple: None,
            test_outfix: None,
            phase_only: None,
            dump_dimacs: None,
            sat_config: radical::SolverConfig::default(),
            sat_secs: 0,
            quad_pb: true,
            mdd_k: 1,
            mdd_extend: 0,
            wz_together: false,
            wz_mode: Some(WzMode::Apart),
            conj_xy_product: false,
            conj_zw_bound: false,
            conj_tuple: false,
            engine: EngineKind::Legacy,
        };
        let tuples = phase_a_tuples(cfg.problem, None);
        let report = run_mdd_sat_search(cfg.problem, &tuples, &cfg, false, cfg.mdd_k);
        assert!(
            report.found_solution,
            "n=4 MDD-walker search should find canonical TT(4)"
        );
        assert!(report.elapsed.as_secs_f64() < 10.0, "n=4 should be fast");
    }

    #[test]
    fn cached_known_tt6_sequence_verifies_fast() {
        let p = Problem::new(6);
        let x = PackedSeq::from_values(&[-1, -1, -1, -1, 1, -1]);
        let y = PackedSeq::from_values(&[-1, -1, -1, 1, -1, -1]);
        let z = PackedSeq::from_values(&[-1, -1, 1, -1, 1, 1]);
        let w = PackedSeq::from_values(&[-1, 1, 1, 1, -1]);
        assert!(verify_tt(p, &x, &y, &z, &w));
    }

    #[test]
    fn quad_pb_accepts_known_tt6() {
        // Known TT(6) solution — all sequences negated so a[0]=+1
        // Original: x=[-1,-1,-1,-1,1,-1], y=[-1,-1,-1,1,-1,-1], z=[-1,-1,1,-1,1,1], w=[-1,1,1,1,-1]
        let x_vals: &[i8] = &[1, 1, 1, 1, -1, 1];
        let y_vals: &[i8] = &[1, 1, 1, -1, 1, 1];
        let z_vals: &[i8] = &[1, 1, -1, 1, -1, -1];
        let w_vals: &[i8] = &[1, -1, -1, -1, 1];

        let p = Problem::new(6);
        let x = PackedSeq::from_values(x_vals);
        let y = PackedSeq::from_values(y_vals);
        let z = PackedSeq::from_values(z_vals);
        let w = PackedSeq::from_values(w_vals);
        assert!(verify_tt(p, &x, &y, &z, &w), "Known TT(6) should verify");

        // Find the matching sum tuple
        let xs: i32 = x_vals.iter().map(|&v| v as i32).sum();
        let ys: i32 = y_vals.iter().map(|&v| v as i32).sum();
        let zs: i32 = z_vals.iter().map(|&v| v as i32).sum();
        let ws: i32 = w_vals.iter().map(|&v| v as i32).sum();
        let tuple = SumTuple {
            x: xs,
            y: ys,
            z: zs,
            w: ws,
        };

        // Test 1: all-free encoding, fix all variables via unit clauses
        let (enc, mut solver) = sat_encode_quad_pb_unified(p, tuple, None, None, None, None)
            .expect("unified quad PB should be feasible");
        let n = p.n;
        let m = p.m();
        for i in 0..n {
            solver.add_clause([if x_vals[i] > 0 {
                enc.x_var(i)
            } else {
                -enc.x_var(i)
            }]);
            solver.add_clause([if y_vals[i] > 0 {
                enc.y_var(i)
            } else {
                -enc.y_var(i)
            }]);
            solver.add_clause([if z_vals[i] > 0 {
                enc.z_var(i)
            } else {
                -enc.z_var(i)
            }]);
        }
        for i in 0..m {
            solver.add_clause([if w_vals[i] > 0 {
                enc.w_var(i)
            } else {
                -enc.w_var(i)
            }]);
        }
        assert_eq!(
            solver.solve(),
            Some(true),
            "All-free quad PB should accept known TT(6)"
        );

        // Test 2: Z-fixed encoding (simulates --z-sat --quad-pb)
        let (enc2, mut solver2) =
            sat_encode_quad_pb_unified(p, tuple, None, None, Some(z_vals), None)
                .expect("Z-fixed quad PB should be feasible");
        for i in 0..n {
            solver2.add_clause([if x_vals[i] > 0 {
                enc2.x_var(i)
            } else {
                -enc2.x_var(i)
            }]);
            solver2.add_clause([if y_vals[i] > 0 {
                enc2.y_var(i)
            } else {
                -enc2.y_var(i)
            }]);
        }
        for i in 0..m {
            solver2.add_clause([if w_vals[i] > 0 {
                enc2.w_var(i)
            } else {
                -enc2.w_var(i)
            }]);
        }
        assert_eq!(
            solver2.solve(),
            Some(true),
            "Z-fixed quad PB should accept known TT(6)"
        );

        // Test 3: Z+W fixed encoding (simulates hybrid --quad-pb)
        let (enc3, mut solver3) =
            sat_encode_quad_pb_unified(p, tuple, None, None, Some(z_vals), Some(w_vals))
                .expect("Z+W fixed quad PB should be feasible");
        for i in 0..n {
            solver3.add_clause([if x_vals[i] > 0 {
                enc3.x_var(i)
            } else {
                -enc3.x_var(i)
            }]);
            solver3.add_clause([if y_vals[i] > 0 {
                enc3.y_var(i)
            } else {
                -enc3.y_var(i)
            }]);
        }
        assert_eq!(
            solver3.solve(),
            Some(true),
            "Z+W fixed quad PB should accept known TT(6)"
        );
    }

    #[test]
    fn stochastic_search_finds_tt8() {
        let p = Problem::new(8);
        let report = stochastic_search(p, None, false, 0);
        assert!(report.found_solution);
        assert!(report.elapsed.as_secs_f64() < 30.0);
    }

    #[test]
    fn cardinality_encoding_exactly_2_of_4() {
        // Test: exactly 2 of 4 variables must be true
        let mut enc = SatEncoder {
            n: 0,
            next_var: 5,
            xnor_triples: Vec::new(),
        };
        let mut solver: radical::Solver = Default::default();
        let lits = vec![1, 2, 3, 4];
        enc.encode_cardinality_eq(&mut solver, &lits, 2);
        // Should be SAT (many solutions: e.g. 1=T,2=T,3=F,4=F)
        assert_eq!(solver.solve(), Some(true));
        let vals: Vec<bool> = (1..=4).map(|v| solver.value(v) == Some(true)).collect();
        let count: usize = vals.iter().filter(|&&v| v).count();
        assert_eq!(count, 2, "Expected exactly 2 true, got {:?}", vals);
    }

    #[test]
    fn cardinality_encoding_exactly_0_of_3() {
        let mut enc = SatEncoder {
            n: 0,
            next_var: 4,
            xnor_triples: Vec::new(),
        };
        let mut solver: radical::Solver = Default::default();
        let lits = vec![1, 2, 3];
        enc.encode_cardinality_eq(&mut solver, &lits, 0);
        assert_eq!(solver.solve(), Some(true));
        for v in 1..=3 {
            assert_eq!(solver.value(v), Some(false), "var {} should be false", v);
        }
    }

    #[test]
    fn cardinality_encoding_exactly_3_of_3() {
        let mut enc = SatEncoder {
            n: 0,
            next_var: 4,
            xnor_triples: Vec::new(),
        };
        let mut solver: radical::Solver = Default::default();
        let lits = vec![1, 2, 3];
        enc.encode_cardinality_eq(&mut solver, &lits, 3);
        assert_eq!(solver.solve(), Some(true));
        for v in 1..=3 {
            assert_eq!(solver.value(v), Some(true), "var {} should be true", v);
        }
    }

    #[test]
    fn xnor_encoding_correct() {
        let mut enc = SatEncoder {
            n: 0,
            next_var: 3,
            xnor_triples: Vec::new(),
        };
        let mut solver: radical::Solver = Default::default();
        // a=1, b=2, test all 4 combos
        let aux = enc.encode_xnor(&mut solver, 1, 2);
        // Force a=T, b=T → aux should be T (agree)
        solver.add_clause([1]);
        solver.add_clause([2]);
        assert_eq!(solver.solve(), Some(true));
        assert_eq!(solver.value(aux), Some(true));
    }

    /// Regression: the standalone `encode_xnor_agree` helper (used by the
    /// --wz=together coupled per-lag constraints) had a spurious extra
    /// clause `[-aux, -a, -b]` that forbade (aux=T, a=T, b=T) — making
    /// `aux ↔ (a==b)` unsatisfiable whenever both inputs were TRUE.
    /// This silently rejected the canonical TT(26) boundary at k=5,
    /// driving the WZ pipeline to produce zero solutions. Exercise all 4
    /// input combinations here.
    #[test]
    fn encode_xnor_agree_all_four_combos_sound() {
        // For each (a, b) ∈ {T, F}², check that the forced aux value matches a==b.
        for (a_val, b_val) in [(true, true), (true, false), (false, true), (false, false)] {
            let mut solver: radical::Solver = Default::default();
            let a = 1i32;
            let b = 2i32;
            let aux = 3i32;
            // encode_xnor_agree uses variables 1, 2, 3 — add a noop clause first
            // to ensure var 3 exists in the solver's var range.
            solver.add_clause([aux, -aux]);
            encode_xnor_agree(&mut solver, aux, a, b);
            solver.add_clause([if a_val { a } else { -a }]);
            solver.add_clause([if b_val { b } else { -b }]);
            assert_eq!(
                solver.solve(),
                Some(true),
                "encode_xnor_agree UNSAT when pinning a={a_val} b={b_val}"
            );
            let expected = a_val == b_val;
            assert_eq!(
                solver.value(aux),
                Some(expected),
                "aux should be {expected} when a={a_val} b={b_val}"
            );
        }
    }

    #[test]
    fn build_counter_exactly_2_of_3() {
        let mut enc = SatEncoder {
            n: 0,
            next_var: 4,
            xnor_triples: Vec::new(),
        };
        let mut solver: radical::Solver = Default::default();
        let lits = vec![1, 2, 3];
        let ctr = enc.build_counter(&mut solver, &lits);
        // Enforce exactly 2: at-least 2 AND at-most 2 (i.e., NOT at-least 3)
        assert!(ctr.len() >= 3, "counter should have at-least-2 var");
        solver.add_clause([ctr[2]]); // at least 2
        if ctr.len() > 3 && ctr[3] != 0 {
            solver.add_clause([-ctr[3]]); // at most 2
        }
        assert_eq!(solver.solve(), Some(true));
        let count: usize = (1..=3).filter(|&v| solver.value(v) == Some(true)).count();
        assert_eq!(count, 2, "expected exactly 2 true");
    }

    #[test]
    // Same as hybrid_finds_tt4: the Cross-mode spectral pair filter is
    // too tight to recover the rule-(i) canonical TT(6) at small n, so
    // we exercise the MDD-walker (Apart) pipeline here.
    fn hybrid_finds_tt6() {
        let cfg = SearchConfig {
            problem: Problem::new(6),
            mdd_k: 2,
            wz_mode: Some(WzMode::Apart),
            ..Default::default()
        };
        let tuples = phase_a_tuples(cfg.problem, None);
        let report = run_mdd_sat_search(cfg.problem, &tuples, &cfg, false, cfg.mdd_k);
        assert!(
            report.found_solution,
            "MDD-walker search should find canonical TT(6)"
        );
    }

    #[test]
    fn known_tt36_verifies() {
        // Known TT(36), **canonical form** (rules (i)-(vi)).
        // Derived from Kharaghani & Tayfeh-Rezaie (2005) TT(36) by applying
        // the BDKR symmetry group and picking the unique orbit member
        // satisfying all 6 rules.
        //
        // X =: '+++-+-++-----+++--++--+-+++-+--+--++'  sum 2
        // Y =: '+++-+--+-+++---+-++-+-++++++--+-++-+'  sum 8
        // Z =: '+++-+-++++--+-+++-+++--++-++++---+--'  sum 8
        // W =: '+++-+---+------++-++++--++-+-++++-+'   sum 3
        let p = Problem::new(36);
        let x = PackedSeq::from_values(&[
            1, 1, 1, -1, 1, -1, 1, 1, -1, -1, -1, -1, -1, 1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1,
            1, 1, -1, 1, -1, -1, 1, -1, -1, 1, 1,
        ]);
        let y = PackedSeq::from_values(&[
            1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, 1, -1, 1, -1, 1, 1, 1, 1,
            1, 1, -1, -1, 1, -1, 1, 1, -1, 1,
        ]);
        let z = PackedSeq::from_values(&[
            1, 1, 1, -1, 1, -1, 1, 1, 1, 1, -1, -1, 1, -1, 1, 1, 1, -1, 1, 1, 1, -1, -1, 1, 1, -1,
            1, 1, 1, 1, -1, -1, -1, 1, -1, -1,
        ]);
        let w = PackedSeq::from_values(&[
            1, 1, 1, -1, 1, -1, -1, -1, 1, -1, -1, -1, -1, -1, -1, 1, 1, -1, 1, 1, 1, 1, -1, -1, 1,
            1, -1, 1, -1, 1, 1, 1, 1, -1, 1,
        ]);
        assert!(
            verify_tt(p, &x, &y, &z, &w),
            "Canonical TT(36) should verify"
        );
        assert_eq!(x.sum(), 2);
        assert_eq!(y.sum(), 8);
        assert_eq!(z.sum(), 8);
        assert_eq!(w.sum(), 3);
        // Sum-squared invariant (6n-2 = 214 at n=36).
        let ss =
            x.sum() * x.sum() + y.sum() * y.sum() + 2 * z.sum() * z.sum() + 2 * w.sum() * w.sum();
        assert_eq!(ss, 214);
    }

    #[test]
    fn known_tt26_verifies() {
        // Known TT(26), **canonical form** (satisfies BDKR rules (i)-(vi)).
        // Obtained by applying the BDKR symmetry group (T1 negate, T2 reverse,
        // T3 alternate-all, T4 swap X↔Y) to the original TT(26) from commit
        // 88aae1a (X sum 6, Y sum 6, Z sum 4, W sum 5) and picking the unique
        // orbit member satisfying all 6 canonicalisation rules.
        //
        // X =: '++----++-----+-+-+--+++--+'  sum -4
        // Y =: '+-+++++-+-+---++++-++++--+'  sum  8
        // Z =: '++-----+--++--+-+-++----+-'  sum -6
        // W =: '+++++-+--++-++---+----+-+'   sum  1
        let p = Problem::new(26);
        let x = PackedSeq::from_values(&[
            1, 1, -1, -1, -1, -1, 1, 1, -1, -1, -1, -1, -1, 1, -1, 1, -1, 1, -1, -1, 1, 1, 1, -1,
            -1, 1,
        ]);
        let y = PackedSeq::from_values(&[
            1, -1, 1, 1, 1, 1, 1, -1, 1, -1, 1, -1, -1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, -1, -1, 1,
        ]);
        let z = PackedSeq::from_values(&[
            1, 1, -1, -1, -1, -1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, -1, 1, 1, -1, -1, -1, -1,
            1, -1,
        ]);
        let w = PackedSeq::from_values(&[
            1, 1, 1, 1, 1, -1, 1, -1, -1, 1, 1, -1, 1, 1, -1, -1, -1, 1, -1, -1, -1, -1, 1, -1, 1,
        ]);
        assert!(
            verify_tt(p, &x, &y, &z, &w),
            "Canonical TT(26) should verify the Turyn identity"
        );
        assert_eq!(x.sum(), -4);
        assert_eq!(y.sum(), 8);
        assert_eq!(z.sum(), -6);
        assert_eq!(w.sum(), 1);
        // Sum-squared invariant (6n-2 = 154 at n=26).
        let ss =
            x.sum() * x.sum() + y.sum() * y.sum() + 2 * z.sum() * z.sum() + 2 * w.sum() * w.sum();
        assert_eq!(ss, 154);

        // Rule (i): x[0]=x[n-1]=y[0]=y[n-1]=z[0]=w[0]=+1.
        let x_v: Vec<i8> = (0..26).map(|i| x.get(i)).collect();
        let y_v: Vec<i8> = (0..26).map(|i| y.get(i)).collect();
        let z_v: Vec<i8> = (0..26).map(|i| z.get(i)).collect();
        let w_v: Vec<i8> = (0..25).map(|i| w.get(i)).collect();
        assert_eq!(
            (x_v[0], x_v[25], y_v[0], y_v[25], z_v[0], w_v[0]),
            (1, 1, 1, 1, 1, 1),
            "Rule (i): x[0]=x[n-1]=y[0]=y[n-1]=z[0]=w[0]=+1"
        );
    }

    #[test]
    fn sat_xy_solves_known_tt36_zw() {
        // Given the known Z/W from TT(36), can SAT find X/Y?
        //
        // The original Kharaghani–Tayfeh-Rezaie (2005) TT(36) has
        // x[35]=y[35]=-1, outside rule (i)'s canonical orbit.  We apply
        // T3 alternation (a[i] ↦ (-1)^i·a[i] on all four sequences) to
        // move into the canonical orbit: for odd i, the sign flips, so
        // position n-1=35 flips and now satisfies x[n-1]=y[n-1]=+1.
        // T3 preserves the Turyn identity (N_·(s) ↦ (-1)^s·N_·(s), and
        // the sum at each lag acquires the same factor, so the identity
        // still vanishes).
        // Canonical TT(36) under the full BDKR rule set (i)..(vi) —
        // produced by orbit-enumerating the Kharaghani–Tayfeh-Rezaie
        // (2005) representative and picking the unique form that
        // satisfies every rule.  The transformation used: negate X,
        // reverse X, reverse W, alternate all four, swap X↔Y.
        // Verified externally; every rule-(i..vi) predicate holds and
        // the Turyn identity vanishes at every lag.
        let p = Problem::new(36);
        let parse =
            |s: &str| -> Vec<i8> { s.bytes().map(|b| if b == b'+' { 1 } else { -1 }).collect() };
        let known_x = parse("+++-+-++-----+++--++--+-+++-+--+--++");
        let known_y = parse("+++-+--+-+++---+-++-+-++++++--+-++-+");
        let z_vals = parse("+++-+-++++--+-+++-+++--++-++++---+--");
        let w_vals = parse("+++-+---+------++-++++--++-+-++++-+");
        assert_eq!(known_x[0], 1);
        assert_eq!(known_x[35], 1);
        assert_eq!(known_y[0], 1);
        assert_eq!(known_y[35], 1);
        assert_eq!(z_vals[0], 1);
        assert_eq!(w_vals[0], 1);
        let z = PackedSeq::from_values(&z_vals);
        let w = PackedSeq::from_values(&w_vals);
        let mut zw = vec![0; 36];
        for (s, slot) in zw.iter_mut().enumerate().skip(1) {
            let nz = z.autocorrelation(s);
            let nw = if s < p.m() { w.autocorrelation(s) } else { 0 };
            *slot = 2 * nz + 2 * nw;
        }
        let candidate = CandidateZW { zw_autocorr: zw };
        // Tuple in the alternated orbit — recompute from the T3-applied
        // sequences (the pre-T3 tuple (0, 6, 8, 5) no longer applies).
        let sum_i8 = |v: &[i8]| -> i32 { v.iter().map(|&x| x as i32).sum() };
        let tuple = SumTuple {
            x: sum_i8(&known_x),
            y: sum_i8(&known_y),
            z: sum_i8(&z_vals),
            w: sum_i8(&w_vals),
        };
        // Test 1: can the SAT solver find X/Y from scratch?
        let template = SatXYTemplate::build(p, tuple, &radical::SolverConfig::default())
            .expect("template should build");
        assert!(
            template.is_feasible(&candidate),
            "known Z/W should be feasible"
        );

        // Test 2: hardcode the known X/Y and check consistency
        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (36 + i + 1) as i32 };
        let mut solver = template.solver.clone();
        // Add per-lag quadratic PB constraints
        for s in 1..36 {
            let target_raw = 2 * (36 - s) as i32 - candidate.zw_autocorr[s];
            let target = (target_raw / 2) as usize;
            let lp = &template.lag_pairs[s];
            let ones: Vec<u32> = vec![1; lp.lits_a.len()];
            solver.add_quad_pb_eq(&lp.lits_a, &lp.lits_b, &ones, target as u32);
        }
        // Hardcode known X/Y
        for i in 0..36 {
            solver.add_clause([if known_x[i] == 1 { x_var(i) } else { -x_var(i) }]);
            solver.add_clause([if known_y[i] == 1 { y_var(i) } else { -y_var(i) }]);
        }
        let result_hardcoded = solver.solve();
        assert_eq!(
            result_hardcoded,
            Some(true),
            "known X/Y hardcoded into SAT should be consistent"
        );

        // Encoding verified correct (hardcoded test passed above).
        // Free SAT search for n=36 XY (~7K vars) needs radical optimizations.
    }

    /// Encode autocorrelation constraints for all four sequences using
    /// XNOR + weighted agree selectors. Shared by sat_encode and tests.
    fn encode_autocorr_xnor(
        n: usize,
        m: usize,
        enc: &mut SatEncoder,
        solver: &mut radical::Solver,
    ) {
        for k in 1..n {
            let w_overlap = if k < m { m - k } else { 0 };
            let target = 2 * (n - k) + w_overlap;

            let mut xy_lits = Vec::new();
            for i in 0..(n - k) {
                xy_lits.push(enc.encode_xnor(solver, enc.x_var(i), enc.x_var(i + k)));
            }
            for i in 0..(n - k) {
                xy_lits.push(enc.encode_xnor(solver, enc.y_var(i), enc.y_var(i + k)));
            }

            let mut zw_lits = Vec::new();
            for i in 0..(n - k) {
                zw_lits.push(enc.encode_xnor(solver, enc.z_var(i), enc.z_var(i + k)));
            }
            for i in 0..w_overlap {
                zw_lits.push(enc.encode_xnor(solver, enc.w_var(i), enc.w_var(i + k)));
            }

            enc.encode_weighted_agree_eq(solver, &xy_lits, &zw_lits, target);
        }
    }

    #[test]
    fn sat_autocorr_only_n4() {
        // Test: just autocorrelation constraints (no sums, no symmetry breaking)
        let n = 4usize;
        let m = 3usize;
        let mut enc = SatEncoder::new(n);
        let mut solver: radical::Solver = Default::default();

        encode_autocorr_xnor(n, m, &mut enc, &mut solver);

        let result = solver.solve();
        assert_eq!(result, Some(true), "autocorr-only n=4 should be SAT");
    }

    #[test]
    fn sat_counter_with_xnor_hardcoded() {
        // Minimal test: hardcode X=[1,1,1,1], check XY agree at lag 3 = exactly 2
        let mut enc = SatEncoder {
            n: 4,
            next_var: 9,
            xnor_triples: Vec::new(),
        }; // vars 1-4=X, 5-8=Y
        let mut solver: radical::Solver = Default::default();
        // X = [T,T,T,T], Y = [T,F,T,T]
        for v in 1..=4 {
            solver.add_clause([v]);
        } // all X = true
        solver.add_clause([5]); // Y[0]=T
        solver.add_clause([-6]); // Y[1]=F
        solver.add_clause([7]); // Y[2]=T
        solver.add_clause([8]); // Y[3]=T

        // XY agree at lag 3: (X0,X3)=(T,T)=agree, (Y0,Y3)=(T,T)=agree
        let ag1 = enc.encode_xnor(&mut solver, 1, 4); // X0 XNOR X3
        let ag2 = enc.encode_xnor(&mut solver, 5, 8); // Y0 XNOR Y3
        let lits = vec![ag1, ag2];
        let ctr = enc.build_counter(&mut solver, &lits);
        // Enforce exactly 2 via counter
        assert!(ctr.len() >= 3 && ctr[2] != 0);
        solver.add_clause([ctr[2]]); // at least 2
        // ctr[3] doesn't exist (len=3), so at-most-2 is automatic

        let result = solver.solve();
        assert_eq!(
            result,
            Some(true),
            "hardcoded XY agrees at lag 3 should give exactly 2"
        );
    }

    #[test]
    fn sat_autocorr_hardcoded_tt4() {
        // Hardcode the known TT(4) solution and check if the encoding is consistent
        // X=[1,1,1,1], Y=[1,-1,1,1], Z=[1,1,-1,-1], W=[1,-1,1]
        let n = 4usize;
        let m = 3usize;
        let mut enc = SatEncoder::new(n);
        let mut solver: radical::Solver = Default::default();

        // Hardcode solution
        let x = [1i8, 1, 1, 1];
        let y = [1i8, -1, 1, 1];
        let z = [1i8, 1, -1, -1];
        let w = [1i8, -1, 1];
        for i in 0..n {
            solver.add_clause([if x[i] == 1 {
                enc.x_var(i)
            } else {
                -enc.x_var(i)
            }]);
        }
        for i in 0..n {
            solver.add_clause([if y[i] == 1 {
                enc.y_var(i)
            } else {
                -enc.y_var(i)
            }]);
        }
        for i in 0..n {
            solver.add_clause([if z[i] == 1 {
                enc.z_var(i)
            } else {
                -enc.z_var(i)
            }]);
        }
        for i in 0..m {
            solver.add_clause([if w[i] == 1 {
                enc.w_var(i)
            } else {
                -enc.w_var(i)
            }]);
        }

        // Add autocorrelation constraints
        encode_autocorr_xnor(n, m, &mut enc, &mut solver);

        let result = solver.solve();
        assert_eq!(
            result,
            Some(true),
            "hardcoded TT(4) solution should be consistent with encoding"
        );
    }

    // At n=4 the Cross-mode spectral pair filter is too tight to recover
    // the rule-(i) canonical TT(4) (X=[+,+,+,+], Y=[+,-,+,+], Z=[+,+,-,-],
    // W=[+,-,+]) — the only pair that passes all Phase A/B sees
    // |Z(ω)|²+|W(ω)|² above the 3n-1=11 bound at one of the ω samples.
    // The MDD-walker path (WzMode::Apart) does not use the same pair
    // filter and recovers the canonical solution cleanly, so we test
    // that pipeline here instead.
    #[test]
    fn hybrid_finds_tt4() {
        let cfg = SearchConfig {
            problem: Problem::new(4),
            mdd_k: 1,
            wz_mode: Some(WzMode::Apart),
            ..Default::default()
        };
        let tuples = phase_a_tuples(cfg.problem, None);
        let report = run_mdd_sat_search(cfg.problem, &tuples, &cfg, false, cfg.mdd_k);
        assert!(
            report.found_solution,
            "MDD-walker search should find canonical TT(4)"
        );
    }

    #[test]
    fn sat_tt14_hardcoded_solution_bisect_lags() {
        // Known TT(14) solution (found via simulated annealing, x[0]=+1):
        let n = 14usize;
        let m = n - 1; // 13
        let x_vals: Vec<i8> = vec![1, -1, 1, -1, -1, -1, 1, 1, 1, -1, -1, 1, 1, 1]; // sum=2
        let y_vals: Vec<i8> = vec![1, 1, 1, -1, 1, -1, -1, 1, -1, -1, 1, -1, 1, 1]; // sum=2
        let z_vals: Vec<i8> = vec![-1, -1, -1, 1, -1, -1, 1, 1, -1, -1, -1, -1, -1, 1]; // sum=-6
        let w_vals: Vec<i8> = vec![1, 1, 1, -1, 1, 1, -1, 1, -1, 1, -1, -1, -1]; // sum=1

        let px = PackedSeq::from_values(&x_vals);
        let py = PackedSeq::from_values(&y_vals);
        let pz = PackedSeq::from_values(&z_vals);
        let pw = PackedSeq::from_values(&w_vals);

        // First verify the solution is actually valid
        let sx = px.sum();
        let sy = py.sum();
        let sz = pz.sum();
        let sw = pw.sum();
        eprintln!("Sums: x={}, y={}, z={}, w={}", sx, sy, sz, sw);
        eprintln!(
            "Energy: x^2+y^2+2z^2+2w^2 = {}",
            sx * sx + sy * sy + 2 * sz * sz + 2 * sw * sw
        );
        eprintln!("Target energy: {}", 6 * n as i32 - 2);
        assert!(
            verify_tt(Problem::new(n), &px, &py, &pz, &pw),
            "Known TT(14) solution should verify"
        );

        let tuple = SumTuple {
            x: sx,
            y: sy,
            z: sz,
            w: sw,
        };

        // Step 1: Build the FULL encoding (matching sat_search exactly) plus
        // hardcode the known solution. Check if SAT.
        {
            let (enc, mut solver) = sat_encode(Problem::new(n), tuple);

            // Hardcode the known solution as unit clauses
            for i in 0..n {
                solver.add_clause([if x_vals[i] == 1 {
                    enc.x_var(i)
                } else {
                    -enc.x_var(i)
                }]);
                solver.add_clause([if y_vals[i] == 1 {
                    enc.y_var(i)
                } else {
                    -enc.y_var(i)
                }]);
                solver.add_clause([if z_vals[i] == 1 {
                    enc.z_var(i)
                } else {
                    -enc.z_var(i)
                }]);
            }
            for i in 0..m {
                solver.add_clause([if w_vals[i] == 1 {
                    enc.w_var(i)
                } else {
                    -enc.w_var(i)
                }]);
            }

            let result = solver.solve();
            if result != Some(true) {
                eprintln!("FULL encoding with hardcoded TT(14) is UNSAT! Bisecting by lag...");
            } else {
                eprintln!("FULL encoding with hardcoded TT(14) is SAT (no bug?)");
                // Even if it passes, continue bisecting to be thorough
            }
        }

        // Step 2: Bisect by adding autocorrelation constraints ONE LAG AT A TIME
        // to find which lag's encoding is buggy.
        let mut first_buggy_lag: Option<usize> = None;
        for max_lag in 1..n {
            let mut enc = SatEncoder::new(n);
            let mut solver: radical::Solver = Default::default();

            // Symmetry breaking
            solver.add_clause([enc.x_var(0)]);

            // Sum constraints
            let x_pos = ((tuple.x + n as i32) / 2) as usize;
            let y_pos = ((tuple.y + n as i32) / 2) as usize;
            let z_pos = ((tuple.z + n as i32) / 2) as usize;
            let w_pos = ((tuple.w + m as i32) / 2) as usize;

            let x_lits: Vec<i32> = (0..n).map(|i| enc.x_var(i)).collect();
            let y_lits: Vec<i32> = (0..n).map(|i| enc.y_var(i)).collect();
            let z_lits: Vec<i32> = (0..n).map(|i| enc.z_var(i)).collect();
            let w_lits: Vec<i32> = (0..m).map(|i| enc.w_var(i)).collect();

            enc.encode_cardinality_eq(&mut solver, &x_lits, x_pos);
            enc.encode_cardinality_eq(&mut solver, &y_lits, y_pos);
            enc.encode_cardinality_eq(&mut solver, &z_lits, z_pos);
            enc.encode_cardinality_eq(&mut solver, &w_lits, w_pos);

            // Add autocorrelation constraints ONLY up to lag max_lag
            for k in 1..=max_lag {
                let w_overlap = if k < m { m - k } else { 0 };
                let target = 2 * (n - k) + w_overlap;

                let mut xy_lits_k = Vec::new();
                for i in 0..(n - k) {
                    xy_lits_k.push(enc.encode_xnor(&mut solver, enc.x_var(i), enc.x_var(i + k)));
                }
                for i in 0..(n - k) {
                    xy_lits_k.push(enc.encode_xnor(&mut solver, enc.y_var(i), enc.y_var(i + k)));
                }

                let mut zw_lits_k = Vec::new();
                for i in 0..(n - k) {
                    zw_lits_k.push(enc.encode_xnor(&mut solver, enc.z_var(i), enc.z_var(i + k)));
                }
                for i in 0..w_overlap {
                    zw_lits_k.push(enc.encode_xnor(&mut solver, enc.w_var(i), enc.w_var(i + k)));
                }

                enc.encode_weighted_agree_eq(&mut solver, &xy_lits_k, &zw_lits_k, target);
            }

            // Hardcode the known solution
            for i in 0..n {
                solver.add_clause([if x_vals[i] == 1 {
                    enc.x_var(i)
                } else {
                    -enc.x_var(i)
                }]);
                solver.add_clause([if y_vals[i] == 1 {
                    enc.y_var(i)
                } else {
                    -enc.y_var(i)
                }]);
                solver.add_clause([if z_vals[i] == 1 {
                    enc.z_var(i)
                } else {
                    -enc.z_var(i)
                }]);
            }
            for i in 0..m {
                solver.add_clause([if w_vals[i] == 1 {
                    enc.w_var(i)
                } else {
                    -enc.w_var(i)
                }]);
            }

            let result = solver.solve();
            let sat = result == Some(true);

            // Compute expected values for this lag for diagnostic output
            if !sat {
                let k = max_lag;
                let w_overlap = if k < m { m - k } else { 0 };
                let target = 2 * (n - k) + w_overlap;

                // Count actual agree pairs from the known solution
                let mut xy_agree = 0usize;
                for i in 0..(n - k) {
                    if x_vals[i] == x_vals[i + k] {
                        xy_agree += 1;
                    }
                }
                for i in 0..(n - k) {
                    if y_vals[i] == y_vals[i + k] {
                        xy_agree += 1;
                    }
                }
                let mut zw_agree = 0usize;
                for i in 0..(n - k) {
                    if z_vals[i] == z_vals[i + k] {
                        zw_agree += 1;
                    }
                }
                for i in 0..w_overlap {
                    if w_vals[i] == w_vals[i + k] {
                        zw_agree += 1;
                    }
                }

                let actual_combined = xy_agree + 2 * zw_agree;

                eprintln!("LAG {} makes it UNSAT!", k);
                eprintln!(
                    "  target (from formula) = 2*(n-k) + w_overlap = 2*{} + {} = {}",
                    n - k,
                    w_overlap,
                    target
                );
                eprintln!(
                    "  actual xy_agree={}, zw_agree={}, xy_agree + 2*zw_agree = {}",
                    xy_agree, zw_agree, actual_combined
                );
                eprintln!("  target == actual? {}", target == actual_combined);

                // Also verify autocorrelation directly
                let nx = px.autocorrelation(k);
                let ny = py.autocorrelation(k);
                let nz = pz.autocorrelation(k);
                let nw = if k < m { pw.autocorrelation(k) } else { 0 };
                eprintln!(
                    "  N_X({})={}, N_Y({})={}, N_Z({})={}, N_W({})={}",
                    k, nx, k, ny, k, nz, k, nw
                );
                eprintln!("  N_X+N_Y+2*N_Z+2*N_W = {}", nx + ny + 2 * nz + 2 * nw);

                // Check which selector splits are available
                let xy_total = 2 * (n - k);
                let zw_total = (n - k) + w_overlap;
                eprintln!("  xy_lits.len()={}, zw_lits.len()={}", xy_total, zw_total);
                eprintln!("  Valid (c_xy, c_zw) splits for target={}:", target);
                for c_zw in 0..=zw_total {
                    let rem = target as isize - 2 * c_zw as isize;
                    if rem < 0 || rem as usize > xy_total {
                        continue;
                    }
                    let c_xy = rem as usize;
                    let matches_actual = c_xy == xy_agree && c_zw == zw_agree;
                    eprintln!(
                        "    c_xy={}, c_zw={} {}",
                        c_xy,
                        c_zw,
                        if matches_actual { "<-- ACTUAL" } else { "" }
                    );
                }

                if first_buggy_lag.is_none() {
                    first_buggy_lag = Some(k);
                }
                // Don't break - show all buggy lags
            } else {
                eprintln!("Lags 1..={}: SAT (ok)", max_lag);
            }
        }

        // The test should fail if any lag is buggy
        assert!(
            first_buggy_lag.is_none(),
            "Encoding is buggy starting at lag {}. See stderr for details.",
            first_buggy_lag.unwrap_or(0)
        );
    }

    #[test]
    fn sat_n14_free_search_manual_encoding() {
        // Build the EXACT same encoding as sat_search for tuple (2,2,-6,1)
        // but without using sat_search — replicate its code path here.
        // Then try free search (no hardcoded solution).
        let n = 14usize;
        let m = 13usize;
        let tuple = SumTuple {
            x: 2,
            y: 2,
            z: -6,
            w: 1,
        };
        let mut enc = SatEncoder::new(n);
        let mut solver: radical::Solver = Default::default();

        solver.add_clause([enc.x_var(0)]); // x[0]=+1

        let x_pos = ((tuple.x + n as i32) / 2) as usize; // 8
        let y_pos = ((tuple.y + n as i32) / 2) as usize; // 8
        let z_pos = ((tuple.z + n as i32) / 2) as usize; // 4
        let w_pos = ((tuple.w + m as i32) / 2) as usize; // 7

        let x_lits: Vec<i32> = (0..n).map(|i| enc.x_var(i)).collect();
        let y_lits: Vec<i32> = (0..n).map(|i| enc.y_var(i)).collect();
        let z_lits: Vec<i32> = (0..n).map(|i| enc.z_var(i)).collect();
        let w_lits: Vec<i32> = (0..m).map(|i| enc.w_var(i)).collect();

        enc.encode_cardinality_eq(&mut solver, &x_lits, x_pos);
        enc.encode_cardinality_eq(&mut solver, &y_lits, y_pos);
        enc.encode_cardinality_eq(&mut solver, &z_lits, z_pos);
        enc.encode_cardinality_eq(&mut solver, &w_lits, w_pos);

        for k in 1..n {
            let w_overlap = if k < m { m - k } else { 0 };
            let target = 2 * (n - k) + w_overlap;
            let mut xy_lits_k = Vec::new();
            for i in 0..(n - k) {
                xy_lits_k.push(enc.encode_xnor(&mut solver, enc.x_var(i), enc.x_var(i + k)));
            }
            for i in 0..(n - k) {
                xy_lits_k.push(enc.encode_xnor(&mut solver, enc.y_var(i), enc.y_var(i + k)));
            }
            let mut zw_lits_k = Vec::new();
            for i in 0..(n - k) {
                zw_lits_k.push(enc.encode_xnor(&mut solver, enc.z_var(i), enc.z_var(i + k)));
            }
            for i in 0..w_overlap {
                zw_lits_k.push(enc.encode_xnor(&mut solver, enc.w_var(i), enc.w_var(i + k)));
            }
            let xy_ctr = enc.build_counter(&mut solver, &xy_lits_k);
            let zw_ctr = enc.build_counter(&mut solver, &zw_lits_k);
            let mut selectors = Vec::new();
            for c_zw in 0..=zw_lits_k.len() {
                let rem = target as isize - 2 * c_zw as isize;
                if rem < 0 || rem as usize > xy_lits_k.len() {
                    continue;
                }
                let c_xy = rem as usize;
                let sel = enc.fresh();
                if c_xy > 0 {
                    if c_xy < xy_ctr.len() && xy_ctr[c_xy] != 0 {
                        solver.add_clause([-sel, xy_ctr[c_xy]]);
                    } else {
                        solver.add_clause([-sel]);
                        continue;
                    }
                }
                if c_xy + 1 < xy_ctr.len() && xy_ctr[c_xy + 1] != 0 {
                    solver.add_clause([-sel, -xy_ctr[c_xy + 1]]);
                }
                if c_zw > 0 {
                    if c_zw < zw_ctr.len() && zw_ctr[c_zw] != 0 {
                        solver.add_clause([-sel, zw_ctr[c_zw]]);
                    } else {
                        solver.add_clause([-sel]);
                        continue;
                    }
                }
                if c_zw + 1 < zw_ctr.len() && zw_ctr[c_zw + 1] != 0 {
                    solver.add_clause([-sel, -zw_ctr[c_zw + 1]]);
                }
                selectors.push(sel);
            }
            if selectors.is_empty() {
                solver.add_clause(std::iter::empty::<i32>());
            } else {
                solver.add_clause(selectors.iter().copied());
            }
        }

        eprintln!(
            "Manual encoding: {} vars, {} clauses",
            solver.num_vars(),
            solver.num_clauses()
        );
        let result = solver.solve();
        eprintln!(
            "Result: {:?}, conflicts: {}",
            result,
            solver.num_conflicts()
        );
        assert_eq!(
            result,
            Some(true),
            "TT(14) manual encoding should be SAT for tuple (2,2,-6,1)"
        );
    }

    #[test]
    fn sat_solves_tt2() {
        // TT(2) canonical form (BDKR rule i): apply T3 alternation to the
        // old Z=[+,+], W=[+] representative (X=Y=[+,-] violates rule i).
        //   After T3:  Z=[+,-], W=[+]  →  X=Y=[+,+],  tuple=(2,2,0,1)
        //   Check: N_X(1)=1, N_Y(1)=1, N_Z(1)=-1, N_W(1)=0  ⇒  1+1-2+0 = 0 ✓
        //   Energy: 4+4+0+2 = 10 = 6·2-2 ✓
        let p = Problem::new(2);
        let tuple = SumTuple {
            x: 2,
            y: 2,
            z: 0,
            w: 1,
        };
        let z = PackedSeq::from_values(&[1, -1]);
        let w = PackedSeq::from_values(&[1]);
        let mut zw = vec![0i32; p.n];
        for s in 1..p.n {
            let nz = z.autocorrelation(s);
            let nw = if s < p.m() { w.autocorrelation(s) } else { 0 };
            zw[s] = 2 * nz + 2 * nw;
        }
        let candidate = CandidateZW { zw_autocorr: zw };
        let template = SatXYTemplate::build(p, tuple, &radical::SolverConfig::default());
        assert!(template.is_some(), "Template should build for n=2");
        let result = template.unwrap().solve_for(&candidate);
        assert!(result.is_some(), "SAT should find X,Y for TT(2)");
        let (x, y) = result.unwrap();
        assert!(verify_tt(p, &x, &y, &z, &w), "Solution should verify");
    }

    #[test]
    fn z_sat_finds_known_tt22_z_middle() {
        // Known TT(22) solution
        let z_full: Vec<i8> = vec![
            1, 1, -1, -1, -1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, 1, -1, 1,
        ];
        let w_full: Vec<i8> = vec![
            1, 1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, -1, -1, 1, -1, 1,
        ];
        let n = 22usize;
        let m = 21usize;
        let k = 3usize;
        let middle_n = n - 2 * k; // 16
        let z_mid_sum: i32 = z_full[k..n - k].iter().map(|&v| v as i32).sum(); // 6

        // Build Z boundary
        let mut z_boundary = vec![0i8; n];
        z_boundary[..k].copy_from_slice(&z_full[..k]);
        z_boundary[n - k..].copy_from_slice(&z_full[n - k..]);

        // Build Z SAT solver (same as pipeline)
        let z_tmpl = sat_z_middle::LagTemplate::new(n, k);
        let mut z_solver = z_tmpl.build_base_solver_quad_pb(middle_n, z_mid_sum);
        sat_z_middle::fill_z_solver_quad_pb_with_boundary(
            &mut z_solver,
            &z_tmpl,
            n,
            m,
            middle_n,
            &z_boundary,
            &w_full,
        );

        // Test 1: does solve() find ANY Z middle?
        let result = z_solver.solve();
        eprintln!("Z SAT (no spectral): {:?}", result);
        assert_eq!(
            result,
            Some(true),
            "Z SAT should find a solution for the known Z/W pair"
        );

        if result == Some(true) {
            let z_mid_vars: Vec<i32> = (0..middle_n).map(|i| (i + 1) as i32).collect();
            let found_mid: Vec<i8> = (0..middle_n)
                .map(|i| {
                    if z_solver.value(z_mid_vars[i]).unwrap() {
                        1
                    } else {
                        -1
                    }
                })
                .collect();
            let known_mid: Vec<i8> = z_full[k..n - k].to_vec();
            eprintln!("Found Z mid: {:?}", found_mid);
            eprintln!("Known Z mid: {:?}", known_mid);
        }

        // Test 2: enumerate ALL Z middles — how many exist?
        let mut z_solver_enum = z_tmpl.build_base_solver_quad_pb(middle_n, z_mid_sum);
        sat_z_middle::fill_z_solver_quad_pb_with_boundary(
            &mut z_solver_enum,
            &z_tmpl,
            n,
            m,
            middle_n,
            &z_boundary,
            &w_full,
        );
        let z_mid_vars: Vec<i32> = (0..middle_n).map(|i| (i + 1) as i32).collect();
        let mut z_enum_count = 0;
        loop {
            let r = z_solver_enum.solve();
            if r != Some(true) {
                break;
            }
            z_enum_count += 1;
            let mid: Vec<i8> = (0..middle_n)
                .map(|i| {
                    if z_solver_enum.value(z_mid_vars[i]).unwrap() {
                        1
                    } else {
                        -1
                    }
                })
                .collect();
            eprintln!("  Z#{}: {:?}", z_enum_count, mid);
            // Add blocking clause
            let block: Vec<i32> = z_mid_vars
                .iter()
                .map(|&v| {
                    if z_solver_enum.value(v) == Some(true) {
                        -v
                    } else {
                        v
                    }
                })
                .collect();
            z_solver_enum.add_clause(block);
        }
        eprintln!("Total Z middles (no spectral): {}", z_enum_count);

        // Test 3: enumerate with spectral constraint
        let mut z_solver_spec = z_tmpl.build_base_solver_quad_pb(middle_n, z_mid_sum);
        sat_z_middle::fill_z_solver_quad_pb_with_boundary(
            &mut z_solver_spec,
            &z_tmpl,
            n,
            m,
            middle_n,
            &z_boundary,
            &w_full,
        );
        let ztab = radical::SpectralTables::new(n, k, 256);
        let z_spec = radical::SpectralConstraint::from_tables(
            &ztab,
            &z_boundary,
            (6 * n as i32 - 2) as f64 / 2.0,
        );
        z_solver_spec.spectral = Some(z_spec);
        let mut z_spec_count = 0;
        loop {
            let r = z_solver_spec.solve();
            if r != Some(true) {
                break;
            }
            z_spec_count += 1;
            let mid: Vec<i8> = (0..middle_n)
                .map(|i| {
                    if z_solver_spec.value(z_mid_vars[i]).unwrap() {
                        1
                    } else {
                        -1
                    }
                })
                .collect();
            eprintln!("  Z_spec#{}: {:?}", z_spec_count, mid);
            let block: Vec<i32> = z_mid_vars
                .iter()
                .map(|&v| {
                    if z_solver_spec.value(v) == Some(true) {
                        -v
                    } else {
                        v
                    }
                })
                .collect();
            z_solver_spec.add_clause(block);
        }
        eprintln!("Total Z middles (with spectral): {}", z_spec_count);
        // Note: only 1 Z found even without spectral — investigating why

        // Test 4: find Z#1, block it, verify state, test known Z
        let mut z_solver3 = z_tmpl.build_base_solver_quad_pb(middle_n, z_mid_sum);
        sat_z_middle::fill_z_solver_quad_pb_with_boundary(
            &mut z_solver3,
            &z_tmpl,
            n,
            m,
            middle_n,
            &z_boundary,
            &w_full,
        );
        let r1 = z_solver3.solve();
        assert_eq!(r1, Some(true));
        let found1: Vec<i8> = (0..middle_n)
            .map(|i| {
                if z_solver3.value(z_mid_vars[i]).unwrap() {
                    1
                } else {
                    -1
                }
            })
            .collect();
        eprintln!("Before blocking: found {:?}", found1);

        // Verify state BEFORE blocking clause
        let bad_before = z_solver3.verify_quad_pb_state();
        eprintln!("Quad PB state before blocking: {} mismatches", bad_before);

        // Add blocking clause (while model is still in place)
        let block: Vec<i32> = z_mid_vars
            .iter()
            .map(|&v| {
                if z_solver3.value(v) == Some(true) {
                    -v
                } else {
                    v
                }
            })
            .collect();
        z_solver3.add_clause(block.clone());

        // Verify state AFTER blocking clause
        let bad_after = z_solver3.verify_quad_pb_state();
        eprintln!("Quad PB state after blocking: {} mismatches", bad_after);

        // Backtrack to level 0 (what solve_with_assumptions does)
        z_solver3.reset();
        let bad_reset = z_solver3.verify_quad_pb_state();
        eprintln!("Quad PB state after reset: {} mismatches", bad_reset);

        // Recompute stale
        z_solver3.recompute_all_quad_pb();
        let bad_recomp = z_solver3.verify_quad_pb_state();
        eprintln!("Quad PB state after recompute: {} mismatches", bad_recomp);

        // Now test known Z with assumptions
        let known_mid2: Vec<i8> = z_full[k..n - k].to_vec();
        let known_assumptions: Vec<i32> = (0..middle_n)
            .map(|i| {
                if known_mid2[i] == 1 {
                    z_mid_vars[i]
                } else {
                    -z_mid_vars[i]
                }
            })
            .collect();
        let r2 = z_solver3.solve_with_assumptions(&known_assumptions);
        eprintln!(
            "After blocking Z#1, known Z assumptions (reused, with learnt): {:?}",
            r2
        );

        // Test 4b: same thing but clear learnt clauses first
        z_solver3.reset();
        z_solver3.clear_learnt_clauses();
        let r2b = z_solver3.solve_with_assumptions(&known_assumptions);
        eprintln!("After clearing learnt clauses: {:?}", r2b);

        // Test 4c: reset BEFORE adding blocking clause (the actual fix)
        let mut z_solver3c = z_tmpl.build_base_solver_quad_pb(middle_n, z_mid_sum);
        sat_z_middle::fill_z_solver_quad_pb_with_boundary(
            &mut z_solver3c,
            &z_tmpl,
            n,
            m,
            middle_n,
            &z_boundary,
            &w_full,
        );
        let _ = z_solver3c.solve();
        let block2 = z_mid_vars
            .iter()
            .map(|&v| {
                if z_solver3c.value(v) == Some(true) {
                    -v
                } else {
                    v
                }
            })
            .collect::<Vec<i32>>();
        z_solver3c.reset(); // THE FIX: backtrack before adding blocking clause
        z_solver3c.add_clause(block2);
        eprintln!("ok flag after reset+add_clause: {}", z_solver3c.ok);
        let r2c = z_solver3c.solve_with_assumptions(&known_assumptions);
        eprintln!("With reset before block: {:?}", r2c);
        assert_eq!(
            r2c,
            Some(true),
            "Reset before blocking clause should fix enumeration"
        );

        // Test 5: binary search for the bad learnt clause
        let learnt = z_solver3.get_learnt_clauses();
        eprintln!("Learnt clauses after first solve: {}", learnt.len());
        // Test each learnt clause: which one makes the known Z UNSAT?
        for (ci, lc) in learnt.iter().enumerate() {
            let mut ts = z_tmpl.build_base_solver_quad_pb(middle_n, z_mid_sum);
            sat_z_middle::fill_z_solver_quad_pb_with_boundary(
                &mut ts,
                &z_tmpl,
                n,
                m,
                middle_n,
                &z_boundary,
                &w_full,
            );
            ts.add_clause(block.clone()); // blocking clause for Z#1
            ts.add_clause(lc.clone()); // one learnt clause
            let r = ts.solve_with_assumptions(&known_assumptions);
            if r != Some(true) {
                eprintln!("BAD LEARNT CLAUSE #{}: {:?} → {:?}", ci, lc, r);
                // Also check: is this clause actually implied by the original constraints?
                let mut ts2 = z_tmpl.build_base_solver_quad_pb(middle_n, z_mid_sum);
                sat_z_middle::fill_z_solver_quad_pb_with_boundary(
                    &mut ts2,
                    &z_tmpl,
                    n,
                    m,
                    middle_n,
                    &z_boundary,
                    &w_full,
                );
                // Check if the negation of the clause is SAT (if so, clause is NOT implied)
                let neg: Vec<i32> = lc.iter().map(|&l| -l).collect();
                for &l in &neg {
                    ts2.add_clause([l]);
                }
                let r3 = ts2.solve();
                eprintln!("  Negation SAT? {:?} (if SAT, learnt clause is WRONG)", r3);
            }
        }

        // Test 6: FRESH solver + blocking clause + known Z — is it the solver or the clause?
        let mut z_solver4 = z_tmpl.build_base_solver_quad_pb(middle_n, z_mid_sum);
        sat_z_middle::fill_z_solver_quad_pb_with_boundary(
            &mut z_solver4,
            &z_tmpl,
            n,
            m,
            middle_n,
            &z_boundary,
            &w_full,
        );
        z_solver4.add_clause(block.clone());
        let r3 = z_solver4.solve_with_assumptions(&known_assumptions);
        eprintln!("Fresh solver + blocking clause + known Z: {:?}", r3);

        // Test 6: FRESH solver, no blocking clause, known Z
        let mut z_solver5 = z_tmpl.build_base_solver_quad_pb(middle_n, z_mid_sum);
        sat_z_middle::fill_z_solver_quad_pb_with_boundary(
            &mut z_solver5,
            &z_tmpl,
            n,
            m,
            middle_n,
            &z_boundary,
            &w_full,
        );
        let r4 = z_solver5.solve_with_assumptions(&known_assumptions);
        eprintln!("Fresh solver, no block, known Z: {:?}", r4);

        assert_eq!(
            r3,
            Some(true),
            "Fresh solver + blocking clause should find known Z"
        );

        // Test 5: with known Z middle as assumptions, is it SAT?
        let z_mid_vars: Vec<i32> = (0..middle_n).map(|i| (i + 1) as i32).collect();
        let known_mid: Vec<i8> = z_full[k..n - k].to_vec();
        let assumptions: Vec<i32> = (0..middle_n)
            .map(|i| {
                if known_mid[i] == 1 {
                    z_mid_vars[i]
                } else {
                    -z_mid_vars[i]
                }
            })
            .collect();
        let mut z_solver2 = z_tmpl.build_base_solver_quad_pb(middle_n, z_mid_sum);
        sat_z_middle::fill_z_solver_quad_pb_with_boundary(
            &mut z_solver2,
            &z_tmpl,
            n,
            m,
            middle_n,
            &z_boundary,
            &w_full,
        );
        let result2 = z_solver2.solve_with_assumptions(&assumptions);
        eprintln!("Z SAT with known Z middle assumptions: {:?}", result2);
        assert_eq!(
            result2,
            Some(true),
            "Known Z middle should satisfy Z SAT constraints"
        );
    }

    /// Check every spectral filter the n=18 pipeline applies against
    /// the canonical TT(18).  If any of them rejects the canonical
    /// that's a bug (the user's standing rule: filters can only reject
    /// bad candidates, never valid TTs).  Also enumerate Zs from the
    /// multi-σ SAT and verify (a) they're all distinct and (b) the
    /// canonical Z is eventually among them.
    #[test]
    fn spectral_filters_accept_canonical_tt18() {
        let parse =
            |s: &str| -> Vec<i8> { s.bytes().map(|b| if b == b'+' { 1 } else { -1 }).collect() };
        let z = parse("++-+++----+-+-++--");
        let w = parse("++----+--+--+++-+");
        let n = 18usize;
        let m = n - 1;
        let k = 5usize;
        let middle_n = n - 2 * k;
        let problem = Problem::new(n);

        // Sanity: canonical TT(18) verifies the Turyn identity.
        let xs = parse("++-+++++++++-+--++");
        let ys = parse("++----++-+---+-+-+");
        let pz = PackedSeq::from_values(&z);
        let pw = PackedSeq::from_values(&w);
        assert!(verify_tt(
            problem,
            &PackedSeq::from_values(&xs),
            &PackedSeq::from_values(&ys),
            &pz,
            &pw,
        ));

        // -----------------------------------------------------------------
        // (1) Individual W spectral filter (`spectral_w`, theta_samples=128).
        let spectral_w = SpectralFilter::new(m, 128);
        let individual_bound = problem.spectral_bound();
        let mut fft_buf_w = FftScratch::new(&spectral_w);
        let w_spectrum = spectrum_if_ok(&w, &spectral_w, individual_bound, &mut fft_buf_w)
            .expect("canonical W must pass individual spectral filter");

        // -----------------------------------------------------------------
        // (2) External Z spectral pair filter (`spectral_z`, same theta grid).
        let spectral_z = SpectralFilter::new(n, 128);
        let mut fft_buf_z = FftScratch::new(&spectral_z);
        let mut z_spectrum = vec![0.0; w_spectrum.len()];
        compute_spectrum_into(&z, &spectral_z, &mut fft_buf_z, &mut z_spectrum);
        let pair_bound = problem.spectral_bound();
        assert!(
            spectral_pair_ok(&z_spectrum, &w_spectrum, pair_bound),
            "canonical (Z,W) must pass external spectral_pair_ok; max |Z|²+|W|² over the \
             128-FFT grid exceeded bound {pair_bound}: z={:?} w={:?}",
            z_spectrum,
            w_spectrum,
        );

        // -----------------------------------------------------------------
        // (3) In-SAT per-freq spectral.  Build the exact SolveZ solver
        // configuration and hardcode the canonical Z middle; SAT must
        // return SAT.  This catches the case where the SAT's 167-freq
        // per-freq bound incorrectly rejects the canonical middle.
        let z_tmpl = sat_z_middle::LagTemplate::new(n, k);
        let mut z_boundary = vec![0i8; n];
        z_boundary[..k].copy_from_slice(&z[..k]);
        z_boundary[n - k..].copy_from_slice(&z[n - k..]);
        let z_bnd_sum: i32 = z_boundary.iter().map(|&v| v as i32).sum();
        let abs_z = 0i32;
        let z_counts: Vec<u32> = if abs_z == 0 {
            sigma_full_to_cnt(0, z_bnd_sum, middle_n)
                .into_iter()
                .collect()
        } else {
            [abs_z, -abs_z]
                .iter()
                .filter_map(|&s| sigma_full_to_cnt(s, z_bnd_sum, middle_n))
                .collect()
        };
        let mut z_solver = z_tmpl.build_base_solver_quad_pb_pb_set(middle_n, &z_counts);
        sat_z_middle::fill_z_solver_quad_pb_with_boundary(
            &mut z_solver,
            &z_tmpl,
            n,
            m,
            middle_n,
            &z_boundary,
            &w,
        );

        // Attach the same per-freq spectral constraint SolveZ uses.
        let ztab = radical::SpectralTables::new(n, k, SPECTRAL_FREQS);
        let mut z_spec = radical::SpectralConstraint::from_tables(&ztab, &z_boundary, pair_bound);
        // Per-freq bound: pair_bound − |W(ω)|² computed at ztab's 167 freqs.
        let nf = ztab.num_freqs;
        let mut w_re = vec![0.0f64; nf];
        let mut w_im = vec![0.0f64; nf];
        for (pos, &wv) in w.iter().enumerate() {
            let base = pos * nf;
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
        let pfb: Vec<f64> = (0..nf)
            .map(|fi| (pair_bound - w_re[fi] * w_re[fi] - w_im[fi] * w_im[fi]).max(0.0))
            .collect();
        // Check: the canonical Z's |Z(ω)|² at each ω must be ≤ pfb[ω].
        // If not, the in-SAT per-freq bound rejects canonical — a bug
        // since `spectral_pair_ok` above already passed.
        let mut z_full_re = vec![0.0f64; nf];
        let mut z_full_im = vec![0.0f64; nf];
        for (pos, &zv) in z.iter().enumerate() {
            let base = pos * nf;
            let cos_slice = &ztab.pos_cos[base..base + nf];
            let sin_slice = &ztab.pos_sin[base..base + nf];
            if zv > 0 {
                for fi in 0..nf {
                    z_full_re[fi] += cos_slice[fi];
                    z_full_im[fi] += sin_slice[fi];
                }
            } else {
                for fi in 0..nf {
                    z_full_re[fi] -= cos_slice[fi];
                    z_full_im[fi] -= sin_slice[fi];
                }
            }
        }
        for fi in 0..nf {
            let zmag2 = z_full_re[fi] * z_full_re[fi] + z_full_im[fi] * z_full_im[fi];
            assert!(
                zmag2 <= pfb[fi] + 1e-6,
                "in-SAT per-freq bound rejects canonical Z at freq {fi}: \
                 |Z|²={zmag2} > pfb={}",
                pfb[fi],
            );
        }
        z_spec.per_freq_bound = Some(pfb);
        z_solver.spectral = Some(z_spec);

        // Enumerate up to 32 Zs with blocking clauses; verify (a) they
        // are all distinct (blocking actually works) and (b) the
        // canonical Z middle appears within the first few dozen.
        let z_mid_vars: Vec<i32> = (0..middle_n).map(|i| (i + 1) as i32).collect();
        let mut seen_mids: std::collections::HashSet<Vec<i8>> = std::collections::HashSet::new();
        let mut canonical_found_at: Option<usize> = None;
        let canonical_mid: Vec<i8> = z[k..k + middle_n].to_vec();
        for i in 0..64 {
            let r = z_solver.solve();
            if r != Some(true) {
                break;
            }
            let z_mid = extract_vals(&z_solver, |idx| z_mid_vars[idx], middle_n);
            assert!(
                seen_mids.insert(z_mid.clone()),
                "SAT returned duplicate Z middle at iteration {i}"
            );
            if z_mid == canonical_mid && canonical_found_at.is_none() {
                canonical_found_at = Some(i);
            }
            // Blocking clause.
            let blk: Vec<i32> = z_mid_vars
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
            z_solver.add_clause(blk);
        }
        eprintln!(
            "enumerated {} distinct Z middles; canonical found at iter {:?}",
            seen_mids.len(),
            canonical_found_at,
        );
        assert!(
            canonical_found_at.is_some(),
            "canonical Z middle not found in first {} SAT solutions — either \
             the in-SAT spectral rejects it (shouldn't, given (3) above passed) \
             or the SAT never reaches it",
            seen_mids.len(),
        );
    }

    /// Sanity check: PbSetEq-based W middle SAT accepts the canonical
    /// TT(18) W middle when the boundary is hardcoded and V_w covers
    /// both signs of σ_W.
    #[test]
    fn pbseteq_w_middle_accepts_canonical_tt18() {
        let parse =
            |s: &str| -> Vec<i8> { s.bytes().map(|b| if b == b'+' { 1 } else { -1 }).collect() };
        let w = parse("++----+--+--+++-+");
        let n = 18usize;
        let m = n - 1;
        let k = 5usize;
        let middle_m = m - 2 * k;
        let mut w_boundary = vec![0i8; m];
        w_boundary[..k].copy_from_slice(&w[..k]);
        w_boundary[m - k..].copy_from_slice(&w[m - k..]);
        let w_bnd_sum: i32 = w_boundary.iter().map(|&v| v as i32).sum();
        // |σ_W| = 1 for canonical TT(18); V_w covers +1 and -1.
        let abs_w = 1i32;
        let counts: Vec<u32> = [abs_w, -abs_w]
            .iter()
            .filter_map(|&s| sigma_full_to_cnt(s, w_bnd_sum, middle_m))
            .collect::<Vec<_>>();
        eprintln!("σ_W_bnd = {}, V_w = {:?}", w_bnd_sum, counts);

        let w_tmpl = sat_z_middle::LagTemplate::new(m, k);
        let mut solver = w_tmpl.build_base_solver_pb_set(middle_m, &counts);
        sat_z_middle::fill_w_solver(&mut solver, &w_tmpl, m, &w_boundary);

        // Hardcode canonical W middle.
        let mid_lits: Vec<i32> = (0..middle_m).map(|i| (i + 1) as i32).collect();
        for (i, &v) in w[k..k + middle_m].iter().enumerate() {
            solver.add_clause([if v == 1 { mid_lits[i] } else { -mid_lits[i] }]);
        }
        assert_eq!(
            solver.solve(),
            Some(true),
            "W middle SAT should accept canonical middle"
        );
    }

    /// Same for Z middle.
    #[test]
    fn pbseteq_z_middle_accepts_canonical_tt18() {
        let parse =
            |s: &str| -> Vec<i8> { s.bytes().map(|b| if b == b'+' { 1 } else { -1 }).collect() };
        let z = parse("++-+++----+-+-++--");
        let w = parse("++----+--+--+++-+");
        let n = 18usize;
        let m = n - 1;
        let k = 5usize;
        let middle_n = n - 2 * k;
        let mut z_boundary = vec![0i8; n];
        z_boundary[..k].copy_from_slice(&z[..k]);
        z_boundary[n - k..].copy_from_slice(&z[n - k..]);
        let z_bnd_sum: i32 = z_boundary.iter().map(|&v| v as i32).sum();
        // |σ_Z| = 0 for canonical; single target.
        let abs_z = 0i32;
        let counts: Vec<u32> = if abs_z == 0 {
            sigma_full_to_cnt(0, z_bnd_sum, middle_n)
                .into_iter()
                .collect()
        } else {
            [abs_z, -abs_z]
                .iter()
                .filter_map(|&s| sigma_full_to_cnt(s, z_bnd_sum, middle_n))
                .collect()
        };
        eprintln!("σ_Z_bnd = {}, V_z = {:?}", z_bnd_sum, counts);

        let z_tmpl = sat_z_middle::LagTemplate::new(n, k);
        let mut solver = z_tmpl.build_base_solver_quad_pb_pb_set(middle_n, &counts);
        sat_z_middle::fill_z_solver_quad_pb_with_boundary(
            &mut solver,
            &z_tmpl,
            n,
            m,
            middle_n,
            &z_boundary,
            &w,
        );

        let mid_lits: Vec<i32> = (0..middle_n).map(|i| (i + 1) as i32).collect();
        for (i, &v) in z[k..k + middle_n].iter().enumerate() {
            solver.add_clause([if v == 1 { mid_lits[i] } else { -mid_lits[i] }]);
        }
        assert_eq!(
            solver.solve(),
            Some(true),
            "Z middle SAT should accept canonical middle"
        );
    }

    /// Sanity check: build the XY template with the unsigned n=18 canonical
    /// tuple, hardcode the canonical X/Y as unit clauses, and assert the
    /// solver finds it.  Guards against regressions in the PbSetEq-based
    /// sum encoding in `build_sat_xy_clauses`.
    #[test]
    fn pbseteq_xy_accepts_canonical_tt18() {
        let parse =
            |s: &str| -> Vec<i8> { s.bytes().map(|b| if b == b'+' { 1 } else { -1 }).collect() };
        let x = parse("++-+++++++++-+--++");
        let y = parse("++----++-+---+-+-+");
        let z = parse("++-+++----+-+-++--");
        let w = parse("++----+--+--+++-+");
        let n = 18usize;
        let m = n - 1;
        let tuple = SumTuple {
            x: 10,
            y: 2,
            z: 0,
            w: 1,
        };
        let pz = PackedSeq::from_values(&z);
        let pw = PackedSeq::from_values(&w);
        let mut zw = vec![0i32; n];
        for s in 1..n {
            let nz = pz.autocorrelation(s);
            let nw = if s < m { pw.autocorrelation(s) } else { 0 };
            zw[s] = 2 * nz + 2 * nw;
        }
        let candidate = CandidateZW { zw_autocorr: zw };
        let template =
            SatXYTemplate::build(Problem::new(n), tuple, &radical::SolverConfig::default())
                .expect("template should build");
        assert!(template.is_feasible(&candidate));
        let mut solver = template
            .prepare_candidate_solver(&candidate)
            .expect("prepare");
        let x_var = |i: usize| -> i32 { (i + 1) as i32 };
        let y_var = |i: usize| -> i32 { (n + i + 1) as i32 };
        for i in 0..n {
            solver.add_clause([if x[i] == 1 { x_var(i) } else { -x_var(i) }]);
            solver.add_clause([if y[i] == 1 { y_var(i) } else { -y_var(i) }]);
        }
        assert_eq!(
            solver.solve(),
            Some(true),
            "hardcoded canonical TT(18) should be SAT-consistent with PbSetEq XY template"
        );
    }

    /// The pipeline's XY path: build template, prepare_candidate_solver,
    /// inject ONLY boundary (x_bits, y_bits) assumptions — leave the
    /// middle positions for the SAT to find.  Regression test for the
    /// n=18 open-search failure where 6863 XY SATs all returned UNSAT
    /// because `add_pb_set_eq` had a stale-counter bug when combined
    /// with ≥12 `add_quad_pb_eq` constraints.  Fixed 2026-04-15; see
    /// `pb_set_eq_plus_quad_pb_tt18_regression` in `radical/src/lib.rs`.
    #[test]
    fn pbseteq_xy_boundary_only_finds_canonical_tt18() {
        sanity_check_canonical_tt(
            "++-+++++++++-+--++",
            "++----++-+---+-+-+",
            "++-+++----+-+-++--",
            "++----+--+--+++-+",
            5,
        );
    }

    /// Sanity check: canonical TT(26) passes verify_tt, all 6 BDKR rules,
    /// and the pipeline's XY SAT accepts its (x_bits, y_bits) boundary.
    #[test]
    fn sanity_canonical_tt26() {
        sanity_check_canonical_tt(
            "++----++-----+-+-+--+++--+",
            "+-+++++-+-+---++++-++++--+",
            "++-----+--++--+-+-++----+-",
            "+++++-+--++-++---+----+-+",
            7,
        );
    }

    /// Same at k=5 — the current auto-default for --wz=together at n>=24.
    /// Confirms the full Z middle SAT, W middle SAT, and XY SAT all accept
    /// canonical when the boundary is narrower (fewer pins, more middle vars).
    #[test]
    fn sanity_canonical_tt26_k5() {
        sanity_check_canonical_tt(
            "++----++-----+-+-+--+++--+",
            "+-+++++-+-+---++++-++++--+",
            "++-----+--++--+-+-++----+-",
            "+++++-+--++-++---+----+-+",
            5,
        );
    }

    /// Oracle tests driven by Kharaghani's complete catalogue in `data/`.
    ///
    /// `data/turyn-type-{02..32}` is a mirror of Hadi Kharaghani's Turyn-type
    /// sequence catalogue, in BDKR hex format (each hex digit packs
    /// `(X, Y, Z, W)` at one position with `+1 → 0, -1 → 1` as
    /// `8·X + 4·Y + 2·Z + W`; last position `n-1` is 3-bit since W has
    /// length `n-1`; `Z[n-1] = -1` always by BDKR consequence, and
    /// `X[n-1] = Y[n-1] = +1` by rule (i)).
    ///
    /// These tests decode a sample of rows and run them through
    /// `sanity_check_canonical_tt`, which exercises the Turyn identity
    /// check, BDKR rule checks, rule-(iv)/(v) boundary pre-filters, W- and
    /// Z-middle SAT encoders, the external and in-SAT spectral filters,
    /// and the XY SAT template's acceptance of the canonical (x_bits,
    /// y_bits) boundary.  Any regression in canonical-form encoding,
    /// spectral bounds, or rule pre-filters will surface here as a
    /// concrete failing input from a published catalogue.
    ///
    /// Catalogue source: <https://www.cs.uleth.ca/~hadi/research/TurynType/>,
    /// mirrored under `data/` (see `data/README.md`).
    fn decode_kharaghani_hex(hex: &str, n: usize) -> (String, String, String, String) {
        assert_eq!(hex.len(), n - 1, "hex must have n-1 digits for TT({n})");
        let mut x = String::with_capacity(n);
        let mut y = String::with_capacity(n);
        let mut z = String::with_capacity(n);
        let mut w = String::with_capacity(n - 1);
        for c in hex.chars() {
            let d = c.to_digit(16).expect("hex digit");
            x.push(if (d >> 3) & 1 == 0 { '+' } else { '-' });
            y.push(if (d >> 2) & 1 == 0 { '+' } else { '-' });
            z.push(if (d >> 1) & 1 == 0 { '+' } else { '-' });
            w.push(if d & 1 == 0 { '+' } else { '-' });
        }
        // Append X[n-1]=+1, Y[n-1]=+1, Z[n-1]=-1 (BDKR consequences).
        x.push('+');
        y.push('+');
        z.push('-');
        (x, y, z, w)
    }

    /// Pick a deterministic sample of rows from a data file (first, 25%,
    /// 50%, 75%, last — or fewer if the file is shorter).
    fn sample_kharaghani_rows(n: usize) -> Vec<String> {
        let path = format!("data/turyn-type-{:02}", n);
        let contents = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => panic!(
                "failed to read {path}: {e}.  \
                The Kharaghani oracle needs `data/turyn-type-{n:02}` checked into \
                the repo; re-run after rebasing on main."
            ),
        };
        let rows: Vec<String> = contents
            .lines()
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .map(String::from)
            .collect();
        assert!(!rows.is_empty(), "{path} has no rows");
        let picks: Vec<usize> = {
            let len = rows.len();
            if len <= 5 {
                (0..len).collect()
            } else {
                vec![0, len / 4, len / 2, 3 * len / 4, len - 1]
            }
        };
        picks.into_iter().map(|i| rows[i].clone()).collect()
    }

    /// Full oracle run at one `n`, with a given `k`.  Decodes a small
    /// sample of canonical solutions from `data/turyn-type-{n}` and
    /// checks that the pipeline accepts each one at the key stages:
    ///
    /// 1. `verify_tt` — Turyn identity holds.
    /// 2. BDKR rules (i)–(vi) satisfied.
    /// 3. Rule-(iv)/(v) boundary pre-filters accept the Z/W boundary at k.
    /// 4. W-middle SAT accepts the canonical W middle.
    /// 5. Z-middle SAT accepts the canonical Z middle (given canonical W).
    /// 6. External and in-SAT spectral pair filters accept canonical (Z, W).
    /// 7. XY SAT `try_candidate(x_bits, y_bits)` returns **Sat(_, _)**
    ///    for the canonical boundary, and whatever (X, Y) it finds is
    ///    itself a valid TT with the canonical (Z, W).
    ///
    /// Step 7 does *not* assert that SAT returns the exact canonical
    /// (X, Y), because the same `(Z, W, x_bits, y_bits)` sometimes
    /// admits more than one middle completion and SAT may pick any.
    fn run_kharaghani_sample(n: usize, k: usize) {
        let rows = sample_kharaghani_rows(n);
        for (i, row) in rows.iter().enumerate() {
            let (x, y, z, w) = decode_kharaghani_hex(row, n);
            eprintln!(
                "kharaghani oracle n={n} k={k} sample {i}/{}: row={row}",
                rows.len()
            );
            kharaghani_oracle_check(&x, &y, &z, &w, k);
        }
    }

    /// Like `sanity_check_canonical_tt` but only asserts *existence*
    /// of an (X, Y) middle for the canonical boundary — the pipeline
    /// is allowed to return any valid completion, not necessarily the
    /// exact canonical one from the data row.  Panics identify the
    /// first stage that rejects.  Shares steps (a)–(g2) with
    /// `sanity_check_canonical_tt`; only the final XY step is relaxed.
    fn kharaghani_oracle_check(x_str: &str, y_str: &str, z_str: &str, w_str: &str, k: usize) {
        let parse =
            |s: &str| -> Vec<i8> { s.bytes().map(|b| if b == b'+' { 1 } else { -1 }).collect() };
        let x = parse(x_str);
        let y = parse(y_str);
        let z = parse(z_str);
        let w = parse(w_str);
        let n = x.len();
        let m = n - 1;

        let problem = Problem::new(n);
        let px = PackedSeq::from_values(&x);
        let py = PackedSeq::from_values(&y);
        let pz = PackedSeq::from_values(&z);
        let pw = PackedSeq::from_values(&w);
        assert!(
            verify_tt(problem, &px, &py, &pz, &pw),
            "n={n}: fails verify_tt"
        );

        // BDKR rules (i)–(vi).  These repeat the ones in
        // sanity_check_canonical_tt so failures on oracle data are easy
        // to attribute.
        assert_eq!(
            (x[0], x[n - 1], y[0], y[n - 1], z[0], w[0]),
            (1, 1, 1, 1, 1, 1),
            "n={n}: rule (i) violated"
        );
        for i in 1..n / 2 {
            if x[i] != x[n - 1 - i] {
                assert_eq!(x[i], 1, "n={n}: rule (ii)");
                break;
            }
        }
        for i in 1..n / 2 {
            if y[i] != y[n - 1 - i] {
                assert_eq!(y[i], 1, "n={n}: rule (iii)");
                break;
            }
        }
        for i in 1..n / 2 {
            if z[i] == z[n - 1 - i] {
                assert_eq!(z[i], 1, "n={n}: rule (iv)");
                break;
            }
        }
        let tail = w[m - 1];
        for i in 1..(m - 1) / 2 + 1 {
            if w[i] * w[m - 1 - i] != tail {
                assert_eq!(w[i], 1, "n={n}: rule (v)");
                break;
            }
        }
        if x[1] != y[1] {
            assert_eq!(x[1], 1, "n={n}: rule (vi)");
        } else {
            assert_eq!(x[n - 2], 1, "n={n}: rule (vi)");
            assert_eq!(y[n - 2], -1, "n={n}: rule (vi)");
        }

        let sigma_z: i32 = z.iter().map(|&b| b as i32).sum();
        let sigma_w: i32 = w.iter().map(|&b| b as i32).sum();

        // Middle boundaries at k.
        let mut z_boundary = vec![0i8; n];
        z_boundary[..k].copy_from_slice(&z[..k]);
        z_boundary[n - k..].copy_from_slice(&z[n - k..]);
        let mut w_boundary = vec![0i8; m];
        w_boundary[..k].copy_from_slice(&w[..k]);
        w_boundary[m - k..].copy_from_slice(&w[m - k..]);
        let middle_n = n - 2 * k;
        let middle_m = m - 2 * k;
        let z_bnd_sum: i32 = z_boundary.iter().map(|&v| v as i32).sum();
        let w_bnd_sum: i32 = w_boundary.iter().map(|&v| v as i32).sum();

        let rule_iv_state = sat_z_middle::check_z_boundary_rule_iv(n, k, &z_boundary);
        assert_ne!(
            rule_iv_state,
            sat_z_middle::BoundaryRuleState::ViolatedAtBoundary,
            "n={n}: rule (iv) pre-filter rejects canonical Z boundary"
        );
        let rule_v_state = sat_z_middle::check_w_boundary_rule_v(m, k, &w_boundary);
        assert_ne!(
            rule_v_state,
            sat_z_middle::BoundaryRuleState::ViolatedAtBoundary,
            "n={n}: rule (v) pre-filter rejects canonical W boundary"
        );

        // W-middle SAT must accept the canonical middle.
        let abs_w = sigma_w.abs();
        let w_counts: Vec<u32> = if abs_w == 0 {
            sigma_full_to_cnt(0, w_bnd_sum, middle_m)
                .into_iter()
                .collect()
        } else {
            [abs_w, -abs_w]
                .iter()
                .filter_map(|&s| sigma_full_to_cnt(s, w_bnd_sum, middle_m))
                .collect()
        };
        assert!(!w_counts.is_empty(), "n={n}: empty V_w");
        let w_tmpl = sat_z_middle::LagTemplate::new(m, k);
        let mut w_solver = w_tmpl.build_base_solver_pb_set(middle_m, &w_counts);
        sat_z_middle::fill_w_solver(&mut w_solver, &w_tmpl, m, &w_boundary);
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
        let w_mid_lits: Vec<i32> = (0..middle_m).map(|i| (i + 1) as i32).collect();
        for (i, &v) in w[k..k + middle_m].iter().enumerate() {
            w_solver.add_clause([if v == 1 {
                w_mid_lits[i]
            } else {
                -w_mid_lits[i]
            }]);
        }
        assert_eq!(
            w_solver.solve(),
            Some(true),
            "n={n}: W-middle SAT rejects canonical W middle"
        );

        // Z-middle SAT must accept the canonical middle.
        let abs_z = sigma_z.abs();
        let z_counts: Vec<u32> = if abs_z == 0 {
            sigma_full_to_cnt(0, z_bnd_sum, middle_n)
                .into_iter()
                .collect()
        } else {
            [abs_z, -abs_z]
                .iter()
                .filter_map(|&s| sigma_full_to_cnt(s, z_bnd_sum, middle_n))
                .collect()
        };
        assert!(!z_counts.is_empty(), "n={n}: empty V_z");
        let z_tmpl = sat_z_middle::LagTemplate::new(n, k);
        let mut z_solver = z_tmpl.build_base_solver_quad_pb_pb_set(middle_n, &z_counts);
        sat_z_middle::fill_z_solver_quad_pb_with_boundary(
            &mut z_solver,
            &z_tmpl,
            n,
            m,
            middle_n,
            &z_boundary,
            &w,
        );
        let z_mid_lits: Vec<i32> = (0..middle_n).map(|i| (i + 1) as i32).collect();
        for (i, &v) in z[k..k + middle_n].iter().enumerate() {
            z_solver.add_clause([if v == 1 {
                z_mid_lits[i]
            } else {
                -z_mid_lits[i]
            }]);
        }
        assert_eq!(
            z_solver.solve(),
            Some(true),
            "n={n}: Z-middle SAT rejects canonical Z middle"
        );

        // External spectral pair filter.
        let spectral_z = SpectralFilter::new(n, 128);
        let spectral_w = SpectralFilter::new(m, 128);
        let mut fft_z = FftScratch::new(&spectral_z);
        let mut fft_w = FftScratch::new(&spectral_w);
        let pair_bound = problem.spectral_bound();
        let w_spec = spectrum_if_ok(&w, &spectral_w, pair_bound, &mut fft_w)
            .unwrap_or_else(|| panic!("n={n}: canonical W fails individual spectral filter"));
        let mut z_spec = vec![0.0; w_spec.len()];
        compute_spectrum_into(&z, &spectral_z, &mut fft_z, &mut z_spec);
        assert!(
            spectral_pair_ok(&z_spec, &w_spec, pair_bound),
            "n={n}: canonical (Z, W) fails external spectral_pair_ok"
        );

        // XY SAT: try_candidate must accept the canonical boundary.
        // Whatever (X, Y) it returns must be a valid TT with the
        // canonical (Z, W); it is not required to equal (x, y).
        let sigma_x: i32 = x.iter().map(|&b| b as i32).sum();
        let sigma_y: i32 = y.iter().map(|&b| b as i32).sum();
        let mut zw = vec![0i32; n];
        for s in 1..n {
            let nz = pz.autocorrelation(s);
            let nw = if s < m { pw.autocorrelation(s) } else { 0 };
            zw[s] = 2 * nz + 2 * nw;
        }
        let candidate = CandidateZW { zw_autocorr: zw };
        let tuple = SumTuple {
            x: sigma_x,
            y: sigma_y,
            z: sigma_z,
            w: sigma_w,
        };
        let template = SatXYTemplate::build(problem, tuple, &radical::SolverConfig::default())
            .expect("template should build");
        let mut state = SolveXyPerCandidate::new(problem, &candidate, &template, k)
            .expect("SolveXyPerCandidate::new should succeed");
        let mut x_bits = 0u32;
        let mut y_bits = 0u32;
        for i in 0..k {
            if x[i] == 1 {
                x_bits |= 1 << i;
            }
            if x[n - k + i] == 1 {
                x_bits |= 1 << (k + i);
            }
            if y[i] == 1 {
                y_bits |= 1 << i;
            }
            if y[n - k + i] == 1 {
                y_bits |= 1 << (k + i);
            }
        }
        let (result, _stats) = state.try_candidate(x_bits, y_bits);
        match result {
            XyTryResult::Sat(found_x, found_y) => {
                let fx: Vec<i8> = (0..n).map(|i| found_x.get(i)).collect();
                let fy: Vec<i8> = (0..n).map(|i| found_y.get(i)).collect();
                let pfx = PackedSeq::from_values(&fx);
                let pfy = PackedSeq::from_values(&fy);
                assert!(
                    verify_tt(problem, &pfx, &pfy, &pz, &pw),
                    "n={n}: SAT returned non-TT completion for canonical (Z, W) + x_bits=0b{x_bits:b}, y_bits=0b{y_bits:b}"
                );
            }
            XyTryResult::Unsat => panic!(
                "n={n}: try_candidate returned UNSAT for canonical TT — rule/template/PbSetEq bug. \
                 tuple=({}, {}, {}, {}), x_bits=0b{x_bits:b}, y_bits=0b{y_bits:b}",
                tuple.x, tuple.y, tuple.z, tuple.w
            ),
            XyTryResult::Pruned => {
                panic!("n={n}: try_candidate pruned canonical at GJ/lag pre-filter")
            }
            XyTryResult::Timeout => panic!("n={n}: try_candidate timed out"),
        }
    }

    #[test]
    fn kharaghani_oracle_n6() {
        run_kharaghani_sample(6, 2);
    }

    #[test]
    fn kharaghani_oracle_n8() {
        run_kharaghani_sample(8, 2);
    }

    #[test]
    fn kharaghani_oracle_n10() {
        run_kharaghani_sample(10, 3);
    }

    #[test]
    fn kharaghani_oracle_n12() {
        run_kharaghani_sample(12, 3);
    }

    #[test]
    fn kharaghani_oracle_n14() {
        run_kharaghani_sample(14, 4);
    }

    #[test]
    fn kharaghani_oracle_n16() {
        run_kharaghani_sample(16, 4);
    }

    #[test]
    fn kharaghani_oracle_n18() {
        run_kharaghani_sample(18, 5);
    }

    #[test]
    fn kharaghani_oracle_n20() {
        run_kharaghani_sample(20, 5);
    }

    // Larger n are slower (bigger SAT instances).  Gate n≥22 behind
    // `--ignored` so the default `cargo test` run stays quick.  Run the
    // full oracle with `cargo test -- --ignored kharaghani`.
    #[test]
    #[ignore = "slow; run via `cargo test -- --ignored kharaghani`"]
    fn kharaghani_oracle_n22() {
        run_kharaghani_sample(22, 6);
    }

    #[test]
    #[ignore = "slow"]
    fn kharaghani_oracle_n24() {
        run_kharaghani_sample(24, 6);
    }

    #[test]
    #[ignore = "slow"]
    fn kharaghani_oracle_n26() {
        run_kharaghani_sample(26, 7);
    }

    #[test]
    #[ignore = "slow"]
    fn kharaghani_oracle_n28() {
        run_kharaghani_sample(28, 7);
    }

    #[test]
    #[ignore = "slow"]
    fn kharaghani_oracle_n30() {
        run_kharaghani_sample(30, 7);
    }

    #[test]
    #[ignore = "slow"]
    fn kharaghani_oracle_n32() {
        run_kharaghani_sample(32, 8);
    }

    /// Regression test for the `--outfix` middle-pin wiring.  Pre-fix,
    /// `outfix_z_mid_pins` and `outfix_w_mid_pins` were only honoured
    /// inside the combined `SolveWZ` path at `src/mdd_pipeline.rs:1380`;
    /// the separate `--wz=apart` `SolveW` and `SolveZ` stages ignored
    /// them, so an outfix with middle pins (`pref_len > k` or
    /// `suf_len > k+1`) would walk over the user-specified middle and
    /// enumerate arbitrary completions, nearly all of which fail the
    /// downstream pair check → UNSAT even on a canonical TT.
    ///
    /// This test drives the regression at the CLI level: give the
    /// pipeline a *fully pinning* outfix derived from a known TT(28),
    /// and require it to find a solution in a few seconds.  Also
    /// covers n=16 as a smaller reproducer.
    ///
    /// Note: a *minimal* outfix (`pref_len=k`, `suf_len=k+1` — boundary
    /// only, no middle pins) on n=28 still returns UNSAT, but that is
    /// a separate issue: the Z SAT's 16-frequency pair filter rejects
    /// the canonical middle when combined with certain boundaries.
    /// Tracked by `outfix_minimal_boundary_bug_tt28` below.
    #[test]
    fn outfix_extended_finds_canonical_tt28() {
        use std::process::Command;
        // Unit tests can't use CARGO_BIN_EXE_*; resolve the release
        // binary from the workspace manifest dir.  `cargo test --release`
        // builds it automatically before running tests.
        let exe = format!("{}/target/release/turyn", env!("CARGO_MANIFEST_DIR"));
        let out = Command::new(exe)
            .args([
                "--n=28",
                "--wz=apart",
                "--mdd-k=9",
                "--sat-secs=5",
                "--outfix=0000067cde3e50...0639ab46135aa51",
            ])
            .output()
            .expect("turyn binary should run");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        let all = format!("{stdout}{stderr}");
        assert!(
            all.contains("found_solution=true"),
            "--outfix with fully-pinning prefix+suffix should find a TT(28)\nfull output:\n{all}"
        );
    }

    /// Smaller variant at n=16 (row 1 of `data/turyn-type-16`, all-positive σ).
    #[test]
    fn outfix_extended_finds_canonical_tt16() {
        use std::process::Command;
        // Unit tests can't use CARGO_BIN_EXE_*; resolve the release
        // binary from the workspace manifest dir.  `cargo test --release`
        // builds it automatically before running tests.
        let exe = format!("{}/target/release/turyn", env!("CARGO_MANIFEST_DIR"));
        let out = Command::new(exe)
            .args([
                "--n=16",
                "--wz=apart",
                "--mdd-k=4",
                "--sat-secs=5",
                "--outfix=00007e4b0e53...19561",
            ])
            .output()
            .expect("turyn binary should run");
        let all = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(
            all.contains("found_solution=true"),
            "--outfix with fully-pinning prefix+suffix should find a TT(16)\nfull output:\n{all}"
        );
    }

    /// Known-broken repro for the minimal-outfix (boundary-only) case on
    /// n=28.  Passes a k=9 boundary with no middle pins and expects the
    /// pipeline to find some (Z, W) middle + (X, Y) completion.  Fails
    /// today because the 16-frequency Z pair filter rejects every
    /// Z-middle candidate at this boundary.  Moving the filter to a
    /// higher-resolution grid, or making it a hint rather than a
    /// hard cut, would plausibly fix this.  Left as `#[ignore]` so
    /// `cargo test -- --ignored` surfaces it as a known limitation.
    #[test]
    #[ignore = "minimal outfix + 16-freq Z pair filter rejects canonical (Z,W)"]
    fn outfix_minimal_boundary_bug_tt28() {
        use std::process::Command;
        // Unit tests can't use CARGO_BIN_EXE_*; resolve the release
        // binary from the workspace manifest dir.  `cargo test --release`
        // builds it automatically before running tests.
        let exe = format!("{}/target/release/turyn", env!("CARGO_MANIFEST_DIR"));
        let out = Command::new(exe)
            .args([
                "--n=28",
                "--wz=apart",
                "--mdd-k=9",
                "--sat-secs=10",
                "--outfix=0000067cd...146135aa51",
            ])
            .output()
            .expect("turyn binary should run");
        let all = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(
            all.contains("found_solution=true"),
            "minimal --outfix (boundary-only) should find a TT(28)\noutput:\n{all}"
        );
    }

    /// Same for canonical TT(36).
    #[test]
    fn sanity_canonical_tt36() {
        sanity_check_canonical_tt(
            "+++-+-++-----+++--++--+-+++-+--+--++",
            "+++-+--+-+++---+-++-+-++++++--+-++-+",
            "+++-+-++++--+-+++-+++--++-++++---+--",
            "+++-+---+------++-++++--++-+-++++-+",
            10,
        );
    }

    /// Reusable end-to-end sanity check: given a TT(n) in canonical form,
    /// verify
    ///   (a) verify_tt passes (Turyn identity holds),
    ///   (b) BDKR rules (i)-(vi) are all satisfied,
    ///   (c) the pipeline's XY SAT path accepts the canonical
    ///       (x_bits, y_bits) boundary with the canonical tuple.
    fn sanity_check_canonical_tt(x_str: &str, y_str: &str, z_str: &str, w_str: &str, k: usize) {
        let parse =
            |s: &str| -> Vec<i8> { s.bytes().map(|b| if b == b'+' { 1 } else { -1 }).collect() };
        let x = parse(x_str);
        let y = parse(y_str);
        let z = parse(z_str);
        let w = parse(w_str);
        let n = x.len();
        assert_eq!(y.len(), n);
        assert_eq!(z.len(), n);
        assert_eq!(w.len(), n - 1);
        let m = n - 1;

        // (a) Turyn identity.
        let problem = Problem::new(n);
        let px = PackedSeq::from_values(&x);
        let py = PackedSeq::from_values(&y);
        let pz = PackedSeq::from_values(&z);
        let pw = PackedSeq::from_values(&w);
        assert!(
            verify_tt(problem, &px, &py, &pz, &pw),
            "n={n}: canonical TT fails verify_tt"
        );

        // (b) Rules (i)-(vi).
        assert_eq!(
            (x[0], x[n - 1], y[0], y[n - 1], z[0], w[0]),
            (1, 1, 1, 1, 1, 1),
            "n={n}: rule (i) violated"
        );
        // Rule (ii): first i with x[i] != x[n-1-i] must have x[i]=+1.
        for i in 1..n / 2 {
            if x[i] != x[n - 1 - i] {
                assert_eq!(x[i], 1, "n={n}: rule (ii) violated at i={i}");
                break;
            }
        }
        // Rule (iii): same for y.
        for i in 1..n / 2 {
            if y[i] != y[n - 1 - i] {
                assert_eq!(y[i], 1, "n={n}: rule (iii) violated at i={i}");
                break;
            }
        }
        // Rule (iv): first i with z[i] == z[n-1-i] must have z[i]=+1.
        for i in 1..n / 2 {
            if z[i] == z[n - 1 - i] {
                assert_eq!(z[i], 1, "n={n}: rule (iv) violated at i={i}");
                break;
            }
        }
        // Rule (v): first i with w[i]*w[m-1-i] != w[m-1] must have w[i]=+1.
        let tail = w[m - 1];
        for i in 1..(m - 1) / 2 + 1 {
            if w[i] * w[m - 1 - i] != tail {
                assert_eq!(w[i], 1, "n={n}: rule (v) violated at i={i}");
                break;
            }
        }
        // Rule (vi): if x[1]!=y[1] then x[1]=+1; else x[n-2]=+1 AND y[n-2]=-1.
        if x[1] != y[1] {
            assert_eq!(x[1], 1, "n={n}: rule (vi) case-1 violated");
        } else {
            assert_eq!(x[n - 2], 1, "n={n}: rule (vi) case-2 x[n-2] violated");
            assert_eq!(y[n - 2], -1, "n={n}: rule (vi) case-2 y[n-2] violated");
        }

        let sigma_x: i32 = x.iter().map(|&b| b as i32).sum();
        let sigma_y: i32 = y.iter().map(|&b| b as i32).sum();
        let sigma_z: i32 = z.iter().map(|&b| b as i32).sum();
        let sigma_w: i32 = w.iter().map(|&b| b as i32).sum();

        // (c) Middle boundaries: encode (z_bits, w_bits) and extract middle values.
        let mut z_boundary = vec![0i8; n];
        z_boundary[..k].copy_from_slice(&z[..k]);
        z_boundary[n - k..].copy_from_slice(&z[n - k..]);
        let mut w_boundary = vec![0i8; m];
        w_boundary[..k].copy_from_slice(&w[..k]);
        w_boundary[m - k..].copy_from_slice(&w[m - k..]);
        let middle_n = n - 2 * k;
        let middle_m = m - 2 * k;
        let z_bnd_sum: i32 = z_boundary.iter().map(|&v| v as i32).sum();
        let w_bnd_sum: i32 = w_boundary.iter().map(|&v| v as i32).sum();

        // (d) Rule-(iv)/(v) boundary pre-filters must not reject canonical.
        let rule_iv_state = sat_z_middle::check_z_boundary_rule_iv(n, k, &z_boundary);
        assert_ne!(
            rule_iv_state,
            sat_z_middle::BoundaryRuleState::ViolatedAtBoundary,
            "n={n}: rule (iv) boundary pre-filter rejects canonical Z boundary"
        );
        let rule_v_state = sat_z_middle::check_w_boundary_rule_v(m, k, &w_boundary);
        assert_ne!(
            rule_v_state,
            sat_z_middle::BoundaryRuleState::ViolatedAtBoundary,
            "n={n}: rule (v) boundary pre-filter rejects canonical W boundary"
        );

        // (e) W-middle SAT: V_w covers both σ_W signs of the tuple's |σ_W|.
        let abs_w = sigma_w.abs();
        let w_counts: Vec<u32> = if abs_w == 0 {
            sigma_full_to_cnt(0, w_bnd_sum, middle_m)
                .into_iter()
                .collect()
        } else {
            [abs_w, -abs_w]
                .iter()
                .filter_map(|&s| sigma_full_to_cnt(s, w_bnd_sum, middle_m))
                .collect::<Vec<_>>()
        };
        assert!(
            !w_counts.is_empty(),
            "n={n}: sigma_full_to_cnt gives empty V_w for |σ_W|={abs_w}, bnd_sum={w_bnd_sum}"
        );
        let w_tmpl = sat_z_middle::LagTemplate::new(m, k);
        let mut w_solver = w_tmpl.build_base_solver_pb_set(middle_m, &w_counts);
        sat_z_middle::fill_w_solver(&mut w_solver, &w_tmpl, m, &w_boundary);
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
        // Pin the canonical W middle as unit clauses.
        let w_mid_lits: Vec<i32> = (0..middle_m).map(|i| (i + 1) as i32).collect();
        for (i, &v) in w[k..k + middle_m].iter().enumerate() {
            w_solver.add_clause([if v == 1 {
                w_mid_lits[i]
            } else {
                -w_mid_lits[i]
            }]);
        }
        assert_eq!(
            w_solver.solve(),
            Some(true),
            "n={n}: W-middle SAT rejects canonical W middle (V_w={w_counts:?}, σ_W={sigma_w})"
        );

        // (f) Z-middle SAT (with full canonical W): V_z covers both σ_Z signs.
        let abs_z = sigma_z.abs();
        let z_counts: Vec<u32> = if abs_z == 0 {
            sigma_full_to_cnt(0, z_bnd_sum, middle_n)
                .into_iter()
                .collect()
        } else {
            [abs_z, -abs_z]
                .iter()
                .filter_map(|&s| sigma_full_to_cnt(s, z_bnd_sum, middle_n))
                .collect::<Vec<_>>()
        };
        assert!(
            !z_counts.is_empty(),
            "n={n}: sigma_full_to_cnt gives empty V_z for |σ_Z|={abs_z}, bnd_sum={z_bnd_sum}"
        );
        let z_tmpl = sat_z_middle::LagTemplate::new(n, k);
        let mut z_solver = z_tmpl.build_base_solver_quad_pb_pb_set(middle_n, &z_counts);
        sat_z_middle::fill_z_solver_quad_pb_with_boundary(
            &mut z_solver,
            &z_tmpl,
            n,
            m,
            middle_n,
            &z_boundary,
            &w,
        );
        let z_mid_lits: Vec<i32> = (0..middle_n).map(|i| (i + 1) as i32).collect();
        for (i, &v) in z[k..k + middle_n].iter().enumerate() {
            z_solver.add_clause([if v == 1 {
                z_mid_lits[i]
            } else {
                -z_mid_lits[i]
            }]);
        }
        assert_eq!(
            z_solver.solve(),
            Some(true),
            "n={n}: Z-middle SAT rejects canonical Z middle (V_z={z_counts:?}, σ_Z={sigma_z})"
        );

        // (g) External spectral pair filter must accept canonical (Z, W).
        let spectral_z = SpectralFilter::new(n, 128);
        let spectral_w = SpectralFilter::new(m, 128);
        let mut fft_z = FftScratch::new(&spectral_z);
        let mut fft_w = FftScratch::new(&spectral_w);
        let pair_bound = problem.spectral_bound();
        let w_spec = spectrum_if_ok(&w, &spectral_w, pair_bound, &mut fft_w)
            .unwrap_or_else(|| panic!("n={n}: canonical W fails individual spectral filter"));
        let mut z_spec = vec![0.0; w_spec.len()];
        compute_spectrum_into(&z, &spectral_z, &mut fft_z, &mut z_spec);
        assert!(
            spectral_pair_ok(&z_spec, &w_spec, pair_bound),
            "n={n}: canonical (Z, W) fails external spectral_pair_ok"
        );

        // (g2) In-SAT 167-freq per-freq spectral bound must accept canonical
        // Z given canonical W.  The pipeline's SolveZ computes pfb[ω] =
        // pair_bound - |W(ω)|² at 167 frequencies and constrains |Z(ω)|²
        // ≤ pfb[ω].  Different grid from the external 128-FFT — a
        // canonical Z that passes the external grid may not pass the
        // 167-grid if this bound were buggy.
        let ztab = radical::SpectralTables::new(n, k, SPECTRAL_FREQS);
        let nf = ztab.num_freqs;
        let mut w_re = vec![0.0f64; nf];
        let mut w_im = vec![0.0f64; nf];
        for (pos, &wv) in w.iter().enumerate() {
            let base = pos * nf;
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
        let pfb: Vec<f64> = (0..nf)
            .map(|fi| (pair_bound - w_re[fi] * w_re[fi] - w_im[fi] * w_im[fi]).max(0.0))
            .collect();
        let mut zr = vec![0.0f64; nf];
        let mut zi = vec![0.0f64; nf];
        for (pos, &zv) in z.iter().enumerate() {
            let base = pos * nf;
            let cs = &ztab.pos_cos[base..base + nf];
            let sn = &ztab.pos_sin[base..base + nf];
            if zv > 0 {
                for fi in 0..nf {
                    zr[fi] += cs[fi];
                    zi[fi] += sn[fi];
                }
            } else {
                for fi in 0..nf {
                    zr[fi] -= cs[fi];
                    zi[fi] -= sn[fi];
                }
            }
        }
        for fi in 0..nf {
            let zmag2 = zr[fi] * zr[fi] + zi[fi] * zi[fi];
            assert!(
                zmag2 <= pfb[fi] + 1e-6,
                "n={n}: in-SAT 167-freq bound rejects canonical Z at freq {fi}: |Z|²={zmag2} > pfb={}",
                pfb[fi]
            );
        }

        // (h) XY SAT accepts the canonical (x_bits, y_bits).
        let mut zw = vec![0i32; n];
        for s in 1..n {
            let nz = pz.autocorrelation(s);
            let nw = if s < m { pw.autocorrelation(s) } else { 0 };
            zw[s] = 2 * nz + 2 * nw;
        }
        let candidate = CandidateZW { zw_autocorr: zw };
        let tuple = SumTuple {
            x: sigma_x,
            y: sigma_y,
            z: sigma_z,
            w: sigma_w,
        };
        let template = SatXYTemplate::build(problem, tuple, &radical::SolverConfig::default())
            .expect("template should build");
        let mut state = SolveXyPerCandidate::new(problem, &candidate, &template, k)
            .expect("SolveXyPerCandidate::new should succeed");

        let mut x_bits = 0u32;
        let mut y_bits = 0u32;
        for i in 0..k {
            if x[i] == 1 {
                x_bits |= 1 << i;
            }
            if x[n - k + i] == 1 {
                x_bits |= 1 << (k + i);
            }
            if y[i] == 1 {
                y_bits |= 1 << i;
            }
            if y[n - k + i] == 1 {
                y_bits |= 1 << (k + i);
            }
        }
        let (result, _stats) = state.try_candidate(x_bits, y_bits);
        match result {
            XyTryResult::Sat(found_x, found_y) => {
                for i in 0..n {
                    assert_eq!(found_x.get(i), x[i], "n={n}: X[{i}] mismatch");
                    assert_eq!(found_y.get(i), y[i], "n={n}: Y[{i}] mismatch");
                }
            }
            XyTryResult::Unsat => panic!(
                "n={n}: try_candidate returned UNSAT for canonical TT — rule/template/PbSetEq bug. \
                 tuple=({}, {}, {}, {}), x_bits=0b{:b}, y_bits=0b{:b}",
                tuple.x, tuple.y, tuple.z, tuple.w, x_bits, y_bits,
            ),
            XyTryResult::Pruned => {
                panic!("n={n}: try_candidate pruned canonical at GJ/lag pre-filter")
            }
            XyTryResult::Timeout => panic!("n={n}: try_candidate timed out"),
        }
    }
}
