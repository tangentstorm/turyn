# Profiling in this environment

## What works right now

`perf` is not present in this container, but GNU `gprof` is available and works for this project.

### 1) Build with gprof instrumentation

```bash
RUSTFLAGS='-C link-arg=-pg' cargo build --release
```

### 2) Run a workload that is long enough to collect samples

For example:

```bash
./target/release/turyn --n=16 --theta=192 --max-z=200000 --max-w=200000 --max-pairs=2000 --benchmark=20
```

This generates `gmon.out` in the working directory.

### 3) Inspect hot functions

```bash
gprof ./target/release/turyn gmon.out | less
```

## Latest profile snapshot (2026-03-31)

Using the commands above on the latest `main`/HEAD in this container, benchmark mode reported:

- `mean_ms=267.109`
- `median_ms=265.155`

`gprof` flat profile top self-time entries:

- `radical::Solver::propagate` — **54.43%**
- `turyn::build_zw_candidates` — **28.24%**
- `radical::Solver::solve_inner` — **5.61%**
- `radical::Solver::enqueue` — **2.75%**
- `radical::Solver::backtrack` — **2.75%**
- `rustfft::Fft::process` — **2.65%**
- `turyn::spectrum_if_ok` — **1.33%**

Interpretation: SAT propagation is now the dominant bottleneck for this workload, while spectral filtering is no longer the top hotspot.

## Suggested optimization hotspots (next experiments)

1. **BCP/watch-list micro-optimization in `radical::Solver::propagate`**
   - Reduce pointer chasing and bounds checks in watched-literal scans.
   - Try tighter memory layout for watch entries and clause headers to improve cache locality.
   - Measure branch-miss impact by comparing variants that reduce unpredictable conditionals in inner loops.

2. **Clause database pressure management**
   - Tune restart + deletion trigger thresholds to keep propagation fast under heavy learned-clause growth.
   - Experiment with stricter retention for high-LBD clauses only when they remain active in recent conflicts.

3. **Hybrid pipeline load reduction before SAT calls (`build_zw_candidates`)**
   - Add cheaper early filters before expensive candidate materialization when possible.
   - Increase deduplication/canonicalization opportunities for equivalent Z/W autocorrelation signatures.

4. **Allocator pressure checks in SAT path**
   - Audit per-solve clone/allocation paths to ensure no avoidable short-lived allocations remain.
   - Reuse buffers/vectors in hot loops where ownership allows.

5. **FFT path is secondary now**
   - `rustfft::Fft::process` is still visible; minor wins are possible (buffer reuse/alignment), but expected ROI is lower than SAT propagation work.

---

## Why `perf` and Cargo-installed profilers are failing here

Attempts to install tooling from apt and crates.io currently fail with HTTP 403 responses from the network proxy/mirror layer.

Observed failures:

- `apt-get update` fails for Ubuntu and LLVM apt sources (`403 Forbidden`).
- `cargo install cargo-flamegraph` fails fetching crates.io index (`CONNECT tunnel failed, response 403`).

So today, you cannot reliably install:

- Linux perf tools (`perf`)
- Rust crates such as `cargo-flamegraph` / `samply`

without changing network/repository access.

---

## If you want better profiling than gprof

Once network/proxy access is fixed, preferred order for Rust:

1. `perf` + `cargo flamegraph` (best Linux native workflow)
2. `samply` (good cross-platform timeline UI)
3. `-Zself-profile` on nightly (compiler-time profiling, not runtime app profiling)

Until then, use `gprof` as the practical fallback in this container.
