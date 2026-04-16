//! Turyn benchmark harness (divan).
//!
//! Reproduces the README's "Current results" table by shelling out to the
//! release binary with nothing more than `--n=N`. Wall-clock samples are
//! what divan reports; each run also prints turyn's own "Time to cover"
//! (TTC) line so we can track that metric alongside time-to-solve.
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

use std::path::PathBuf;
use std::process::Command;
use std::sync::OnceLock;
use std::time::{Duration, Instant};

fn main() {
    divan::main();
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
    ttc_line: Option<String>,
    found_solution: bool,
}

/// Run `target/release/turyn --n=N` once. Returns wall-clock plus the
/// parsed "Time to cover:" line from the binary's verbose summary.
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
    let found_solution = stdout.contains("found_solution=true");

    TuryRun { wall, ttc_line, found_solution }
}

fn report(tag: &str, r: &TuryRun) {
    let solved = if r.found_solution { "solved" } else { "NO SOLUTION" };
    match &r.ttc_line {
        Some(line) => eprintln!("[{tag}] wall={:>10.3?} {solved} | {line}", r.wall),
        None => eprintln!("[{tag}] wall={:>10.3?} {solved} | (no Time-to-cover line)", r.wall),
    }
}

// ---------------------------------------------------------------------------
// Reproduce README table: find TT(n) for each even n from 4 to 24.
//
// `sample_count = 3` doubles as "retry / find a solution again" for the
// fast sizes, where the cost of a rerun is negligible and the variance
// between runs is interesting on its own. For larger `n` the same three
// samples just establish a median.
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
        report(&format!("TT({n})"), &r);
        divan::black_box(r.wall);
    });
}

// ---------------------------------------------------------------------------
// TT(26): current frontier. Single sample, 24-hour budget, may not find
// a solution. Run with: `cargo bench --bench turyn_bench -- tt26`.
// ---------------------------------------------------------------------------
#[divan::bench(
    sample_count = 1,
    sample_size = 1,
    max_time = 86_400,
)]
fn tt26(bencher: divan::Bencher) {
    bencher.bench_local(|| {
        let r = run_turyn(26);
        report("TT(26)", &r);
        divan::black_box(r.wall);
    });
}
