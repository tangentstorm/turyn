//! Criterion harness for fixed-work TTC benchmarking.
//!
//! The benchmark shells out to the release `turyn` binary with
//! `--bench-cover-log2=X`, so every sample covers approximately the same
//! raw-equivalent amount of work and SAT hits do not end the run early.
//!
//! Command-line knobs:
//!
//! - `--turyn-n=N` (default `10`)
//! - `--turyn-wz=cross|apart|together|sync` (default `cross`)
//! - `--turyn-mdd-k=K` (optional)
//! - `--turyn-cover-log2=X` (default `8`)
//! - `--turyn-sat-secs=S` (default `30`)
//!
//! Example:
//!
//! ```text
//! cargo bench --bench fixed_work_criterion -- \
//!   --turyn-n=26 --turyn-wz=together --turyn-mdd-k=7 --turyn-cover-log2=34
//! ```

use std::path::PathBuf;
use std::process::Command;
use std::sync::OnceLock;
use std::time::{Duration, Instant};

use criterion::{BenchmarkId, Criterion};

#[derive(Clone, Debug)]
struct BenchConfig {
    n: usize,
    wz: String,
    mdd_k: Option<usize>,
    cover_log2: f64,
    sat_secs: u64,
}

impl BenchConfig {
    fn from_args() -> Self {
        let mut cfg = Self::default();
        for arg in std::env::args().skip(1) {
            if arg == "--turyn-help" {
                print_usage_and_exit();
            } else if let Some(v) = arg.strip_prefix("--turyn-n=") {
                cfg.n = parse_arg("--turyn-n", v);
            } else if let Some(v) = arg.strip_prefix("--turyn-wz=") {
                cfg.wz = v.to_string();
            } else if let Some(v) = arg.strip_prefix("--turyn-mdd-k=") {
                cfg.mdd_k = Some(parse_arg("--turyn-mdd-k", v));
            } else if let Some(v) = arg.strip_prefix("--turyn-cover-log2=") {
                cfg.cover_log2 = parse_arg("--turyn-cover-log2", v);
            } else if let Some(v) = arg.strip_prefix("--turyn-sat-secs=") {
                cfg.sat_secs = parse_arg("--turyn-sat-secs", v);
            }
        }
        cfg.validate();
        cfg
    }

    fn validate(&self) {
        match self.wz.as_str() {
            "cross" | "apart" | "together" | "sync" => {}
            other => panic!("--turyn-wz must be one of cross|apart|together|sync, got {other:?}"),
        }
        assert!(
            self.cover_log2.is_finite() && self.cover_log2 >= 0.0,
            "--turyn-cover-log2 must be a non-negative finite number"
        );
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

impl Default for BenchConfig {
    fn default() -> Self {
        Self {
            n: 10,
            wz: "cross".to_string(),
            mdd_k: None,
            cover_log2: 8.0,
            sat_secs: 30,
        }
    }
}

fn parse_arg<T: std::str::FromStr>(name: &str, value: &str) -> T {
    value
        .parse()
        .unwrap_or_else(|_| panic!("{name} has invalid value {value:?}"))
}

fn print_usage_and_exit() -> ! {
    eprintln!(
        "fixed_work_criterion options:\n\
         \n\
         --turyn-n=N\n\
         --turyn-wz=cross|apart|together|sync\n\
         --turyn-mdd-k=K\n\
         --turyn-cover-log2=X\n\
         --turyn-sat-secs=S\n\
         \n\
         example:\n\
         cargo bench --bench fixed_work_criterion -- --turyn-n=26 --turyn-wz=together --turyn-mdd-k=7 --turyn-cover-log2=34"
    );
    std::process::exit(0);
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
    let cfg = BenchConfig::from_args();
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

fn main() {
    let mut criterion = Criterion::default()
        .sample_size(10)
        .measurement_time(Duration::from_secs(30))
        .warm_up_time(Duration::from_secs(3));
    fixed_work_bench(&mut criterion);
    criterion.final_summary();
}
