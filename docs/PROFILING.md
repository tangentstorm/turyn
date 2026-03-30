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

In this environment, that profile currently shows `turyn::spectrum_if_ok` as the dominant hotspot for the sample workload.

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
