//! Turyn benchmark harness (divan).
//!
//! Reproduces the README's "Current results" table by shelling out to the
//! release binary with nothing more than `--n=N`. Divan handles sample
//! orchestration; we parse turyn's own "Time to cover" line from every
//! run, aggregate it ourselves, and print a TTC summary after divan's
//! wall-clock table. TTC is the cross-size apples-to-apples metric:
//! `total_work / effective_rate` is `n`-independent in units (seconds),
//! whereas paths/sec throughput is not.
//!
//! Usage:
//!   cargo bench --bench turyn_bench                 # TT(4)..TT(24)
//!   cargo bench --bench turyn_bench -- tt26         # TT(26), standalone
//!
//! The first run pre-builds `target/release/turyn` + `target/release/gen_mdd`
//! and generates every `mdd-{1..5}.bin` boundary table the default
//! `--wz=together --mdd-k=5` path needs across n = 4..24. (mdd_k is
//! clamped to `min(5, (n-1)/2, m/2)`, so k>5 is never requested. n=2 is
//! skipped: the clamp drives mdd_k to 0 and the binary can't load a
//! k=0 table.)

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::Command;
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

fn main() {
    divan::main();
    print_ttc_summary();
}

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn turyn_binary() -> PathBuf {
    project_root().join("target/release/turyn")
}

fn gen_mdd_binary() -> PathBuf {
    project_root().join("target/release/gen_mdd")
}

/// Build the release binaries and make sure every `mdd-{1..5}.bin` is on
/// disk so the default `target/release/turyn --n=N` path can find an
/// exact-`k` boundary table for every benched `n`.
fn ensure_ready() {
    static READY: OnceLock<()> = OnceLock::new();
    READY.get_or_init(|| {
        let status = Command::new("cargo")
            .args(["build", "--release", "--bin", "turyn", "--bin", "gen_mdd"])
            .current_dir(project_root())
            .status()
            .expect("failed to spawn cargo build");
        assert!(status.success(), "cargo build --release failed");

        for k in 1..=5 {
            let path = project_root().join(format!("mdd-{k}.bin"));
            if path.exists() {
                continue;
            }
            eprintln!("[bench] generating mdd-{k}.bin (one-time)...");
            let status = Command::new(gen_mdd_binary())
                .arg(k.to_string())
                .current_dir(project_root())
                .status()
                .expect("failed to spawn gen_mdd");
            assert!(status.success(), "gen_mdd {k} failed");
        }
    });
}

struct TuryRun {
    wall: Duration,
    /// Parsed `eff_rate × total_work` from the "Time to cover" line:
    /// `total_work / eff_rate` seconds. `None` if the line is missing or
    /// unparseable (e.g., the rate is zero for a very short run).
    ttc: Option<Duration>,
    ttc_line: Option<String>,
    found_solution: bool,
}

/// Extract TTC as a real `Duration` from the raw summary line. The
/// format is fixed: `Time to cover: <pretty> (<rate> <unit>, <total> <label>)`.
/// We compute `total / rate` rather than parsing the pretty string so
/// we're robust to the s/m/h/d bucket breakpoints.
fn parse_ttc_seconds(line: &str) -> Option<f64> {
    let paren = line.split_once('(')?.1;
    let inside = paren.split_once(')')?.0;
    let mut parts = inside.split(',');
    let rate_field = parts.next()?.trim();
    let total_field = parts.next()?.trim();
    let rate: f64 = rate_field.split_whitespace().next()?.parse().ok()?;
    let total: f64 = total_field.split_whitespace().next()?.parse().ok()?;
    if rate <= 0.0 {
        return None;
    }
    Some(total / rate)
}

/// Run `target/release/turyn --n=N` once. Returns wall-clock plus the
/// parsed TTC duration and the raw summary line.
fn run_turyn(n: usize) -> TuryRun {
    ensure_ready();
    let start = Instant::now();
    let output = Command::new(turyn_binary())
        .arg(format!("--n={n}"))
        .current_dir(project_root())
        .output()
        .expect("failed to spawn turyn");
    let wall = start.elapsed();

    if !output.status.success() {
        panic!(
            "turyn --n={n} exited with {:?}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let ttc_line = stdout
        .lines()
        .find(|l| l.contains("Time to cover:"))
        .map(|l| l.trim().to_string());
    let ttc = ttc_line
        .as_deref()
        .and_then(parse_ttc_seconds)
        .map(Duration::from_secs_f64);
    let found_solution = stdout.contains("found_solution=true");

    TuryRun {
        wall,
        ttc,
        ttc_line,
        found_solution,
    }
}

// ---------------------------------------------------------------------------
// TTC collector: accumulate the parsed `Duration` from every sample,
// keyed by the problem size `n` so the summary sorts numerically. The
// human-readable label rides along for display. Printed after
// `divan::main()` returns so the TTC table appears beneath divan's
// wall-clock table.
// ---------------------------------------------------------------------------
struct TtcSeries {
    label: String,
    samples: Vec<Duration>,
}
static TTC_SAMPLES: Mutex<BTreeMap<usize, TtcSeries>> = Mutex::new(BTreeMap::new());

fn record(n: usize, r: &TuryRun) {
    let label = format!("TT({n})");
    let line = r.ttc_line.as_deref().unwrap_or("(no Time-to-cover line)");
    let solved = if r.found_solution {
        "solved"
    } else {
        "NO SOLUTION"
    };
    eprintln!("[{label}] wall={:>10.3?} {solved} | {line}", r.wall);
    if let Some(ttc) = r.ttc {
        let mut map = TTC_SAMPLES.lock().unwrap();
        map.entry(n)
            .or_insert_with(|| TtcSeries {
                label: label.clone(),
                samples: Vec::new(),
            })
            .samples
            .push(ttc);
    }
}

fn fmt_duration(d: Duration) -> String {
    let s = d.as_secs_f64();
    if s < 60.0 {
        format!("{s:>6.2}s")
    } else if s < 3600.0 {
        format!("{:>6.2}m", s / 60.0)
    } else if s < 86400.0 {
        format!("{:>6.2}h", s / 3600.0)
    } else {
        format!("{:>6.2}d", s / 86400.0)
    }
}

fn print_ttc_summary() {
    let samples = TTC_SAMPLES.lock().unwrap();
    if samples.is_empty() {
        return;
    }
    eprintln!();
    eprintln!("Time to cover (cross-size comparable metric):");
    eprintln!(
        "  {:<10} {:>7}  {:>7}  {:>7}  {:>7}  samples",
        "bench", "min", "median", "max", "mean"
    );
    for series in samples.values() {
        let mut v = series.samples.clone();
        v.sort();
        let n = v.len();
        if n == 0 {
            continue;
        }
        let min = v[0];
        let max = v[n - 1];
        let median = v[n / 2];
        let sum: Duration = v.iter().sum();
        let mean = sum / n as u32;
        eprintln!(
            "  {:<10} {}  {}  {}  {}  {}",
            series.label,
            fmt_duration(min),
            fmt_duration(median),
            fmt_duration(max),
            fmt_duration(mean),
            n,
        );
    }
}

// ---------------------------------------------------------------------------
// Reproduce README table: find TT(n) for each even n from 4 to 24.
//
// `sample_count = 3` doubles as "retry / find a solution again" for the
// fast sizes. Time-to-solve is noisy (thread-scheduling dominated), but
// TTC is stable — that's the metric we aggregate below.
// ---------------------------------------------------------------------------
#[divan::bench(
    args = [4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24],
    sample_count = 3,
    sample_size = 1,
    max_time = 600,
)]
fn tt(bencher: divan::Bencher, n: usize) {
    bencher.bench_local(|| {
        let r = run_turyn(n);
        record(n, &r);
        divan::black_box(r.wall);
    });
}

// ---------------------------------------------------------------------------
// TT(26): current frontier. Single sample, 24-hour budget, may not find
// a solution. Run with: `cargo bench --bench turyn_bench -- tt26`.
// ---------------------------------------------------------------------------
#[divan::bench(sample_count = 1, sample_size = 1, max_time = 86_400)]
fn tt26(bencher: divan::Bencher) {
    bencher.bench_local(|| {
        let r = run_turyn(26);
        record(26, &r);
        divan::black_box(r.wall);
    });
}
