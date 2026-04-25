//! Criterion harness for fixed-work TTC benchmarking.
//!
//! The benchmark shells out to the release `turyn` binary with
//! `--bench-cover-log2=X`, so every sample covers approximately the same
//! raw-equivalent amount of work and SAT hits do not end the run early.
//!
//! Environment knobs:
//!
//! - `TURYN_CRIT_N` (default `10`)
//! - `TURYN_CRIT_WZ` (default `cross`)
//! - `TURYN_CRIT_MDD_K` (optional)
//! - `TURYN_CRIT_COVER_LOG2` (default `8`)
//! - `TURYN_CRIT_SAT_SECS` (default `30`)
//!
//! Example:
//!
//! ```text
//! $env:TURYN_CRIT_N=26
//! $env:TURYN_CRIT_WZ="together"
//! $env:TURYN_CRIT_MDD_K=7
//! $env:TURYN_CRIT_COVER_LOG2=34
//! cargo bench --bench fixed_work_criterion
//! ```

use std::path::PathBuf;
use std::process::Command;
use std::sync::OnceLock;
use std::time::{Duration, Instant};

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};

#[derive(Clone, Debug)]
struct BenchConfig {
    n: usize,
    wz: String,
    mdd_k: Option<usize>,
    cover_log2: f64,
    sat_secs: u64,
}

impl BenchConfig {
    fn from_env() -> Self {
        Self {
            n: env_parse("TURYN_CRIT_N").unwrap_or(10),
            wz: std::env::var("TURYN_CRIT_WZ").unwrap_or_else(|_| "cross".to_string()),
            mdd_k: env_parse("TURYN_CRIT_MDD_K"),
            cover_log2: env_parse("TURYN_CRIT_COVER_LOG2").unwrap_or(8.0),
            sat_secs: env_parse("TURYN_CRIT_SAT_SECS").unwrap_or(30),
        }
    }

    fn label(&self) -> String {
        match self.mdd_k {
            Some(k) => format!("n{}_{}_k{}_2^{}", self.n, self.wz, k, self.cover_log2),
            None => format!("n{}_{}_2^{}", self.n, self.wz, self.cover_log2),
        }
    }

    fn args(&self) -> Vec<String> {
        let mut args = vec![
            "search".to_string(),
            format!("--n={}", self.n),
            format!("--wz={}", self.wz),
            format!("--bench-cover-log2={}", self.cover_log2),
            format!("--sat-secs={}", self.sat_secs),
        ];
        if let Some(k) = self.mdd_k {
            args.push(format!("--mdd-k={k}"));
        }
        args
    }
}

fn env_parse<T: std::str::FromStr>(name: &str) -> Option<T> {
    std::env::var(name).ok()?.parse().ok()
}

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn turyn_binary() -> PathBuf {
    project_root().join("target/release/turyn")
}

fn ensure_release_binary() {
    static READY: OnceLock<()> = OnceLock::new();
    READY.get_or_init(|| {
        let status = Command::new("cargo")
            .args(["build", "--release", "--bin", "turyn"])
            .current_dir(project_root())
            .status()
            .expect("failed to spawn cargo build");
        assert!(status.success(), "cargo build --release --bin turyn failed");
    });
}

fn run_one(cfg: &BenchConfig) -> Duration {
    ensure_release_binary();
    let start = Instant::now();
    let output = Command::new(turyn_binary())
        .args(cfg.args())
        .current_dir(project_root())
        .output()
        .expect("failed to spawn target/release/turyn");
    let elapsed = start.elapsed();

    if !output.status.success() {
        panic!(
            "turyn fixed-work benchmark failed with {:?}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    elapsed
}

fn fixed_work_bench(c: &mut Criterion) {
    let cfg = BenchConfig::from_env();
    let id = BenchmarkId::new("turyn_fixed_work", cfg.label());

    c.bench_with_input(id, &cfg, |b, cfg| {
        b.iter_custom(|iters| {
            let mut total = Duration::ZERO;
            for _ in 0..iters {
                total += run_one(cfg);
            }
            total
        });
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .sample_size(10)
        .measurement_time(Duration::from_secs(30))
        .warm_up_time(Duration::from_secs(3));
    targets = fixed_work_bench
}
criterion_main!(benches);
