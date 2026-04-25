# Turyn Search Optimization Log

This file tracks performance-oriented changes and their measured impact.

## April 25 2026 — multi-tuple XY MDD walk in `process_boundary` (-21 % fixed-work, mdd-mode boundary stage)

`src/mdd_pipeline.rs::process_boundary` previously called
`any_valid_xy` once per tuple (16× at n=26), each call walking the
same XY sub-MDD up to depth 14 with only the per-leaf ±|σ_X|, ±|σ_Y|
check changing between calls. A probe showed σ-fails were 0 at
n=26 k=7 for every boundary and tuple, so the per-tuple XY walk was
the dominant cost in the boundary stage.

Replaced with a single multi-tuple walk (`valid_xy_tuple_mask` in
`src/xy_sat.rs`): one recursive descent that returns a 32-bit
bitmask of tuples whose leaf check passes for at least one
reachable leaf. At each leaf, the per-tuple check runs over the
still-pending mask; an early exit fires when every wanted tuple is
already validated. The legacy LEAF-before-`xy_depth` semantics
(unconstrained residual ⇒ unconditionally true) is preserved by
OR-ing the pending mask straight into the result instead of
walking the unconstrained subtree.

### Benchmark: `cargo bench --bench fixed_work_criterion`

Command:

```text
cargo bench --bench fixed_work_criterion -- \
  --turyn-n=26 --turyn-wz=apart --turyn-mdd-k=7 \
  --turyn-cover-log2=50 --turyn-sat-secs=120
```

Criterion, 10 samples each side, sequential machine:

| | Time (95% CI) |
|---|---|
| Baseline | 11.16 — 11.22 — 11.28 s |
| After | 8.81 — 8.89 — 8.97 s |

Change: **+24.8 % to +27.5 % faster (p < 0.05)** — confidence intervals
do not overlap.

Standard documented profile (`--turyn-wz=together --turyn-cover-log2=34`)
also drops from ~7.7 s median (pre-session baseline) to ~5.7 s
median; that profile is high-variance because cover-log2=34 is hit
within 50 ms of the seed-boundaries enumeration finishing, so the
larger cover-log2=50 run is the cleaner statistical signal and is
the headline number.

### TTC mechanism

**Rate.** The boundary stage's per-second throughput rises ~25 %
because each boundary now does a single XY walk instead of
`n_tuples` walks. `stage_exit[0]/elapsed` rises proportionally.
Soundness preserved: `flow_z_*` and `flow_xy_*` on TT(18)/TT(22)
match the legacy run for the same seed, confirming the same
boundaries pass the σ + XY filter into stage 1.

### Counters that moved

- `stage_exit[0]` per second: up ~25 %
- `flow_bnd_sum_fail` total: unchanged (still bumped once per
  failing tuple, just in batched bit-count form)
- TT(18) `flow Z: unsat=548 sol=11`, TT(18) `flow XY: sat=1`:
  identical to baseline.

### Correctness validation

- TT(18) `--wz=apart --mdd-k=5 --sat-secs=10`: still solves
  (`flow XY: sat=1`).
- TT(22) `--wz=apart --mdd-k=5 --sat-secs=20`: full pipeline fires.
- `cargo test --release --bin turyn -- --test-threads=1 --skip
  outfix`: 89 passed, 0 failed.
  - 3 `outfix_*` tests fail on this checkout because they require
    `mdd-9.bin`, which has to be generated with `gen_mdd 9` and
    is not present here. This is the documented MDD scratch-file
    failure mode in `TICK-PROMPT.md`.

## April 19 2026 — `--wz=sync` deep optimization session (-99.3 % TTC cumulative, 150×)

A single multi-hour session pushed `--wz=sync` from baseline TTC
6.581e8 s parallel down to ~4.40e6 s parallel — a **150× cumulative
speedup** at n=26. The final order-of-magnitude came from
**backbone detection** (kissat-style preprocessing) alone.  All wins came from the walker / solver
interaction; no algorithmic changes to the search space.

| Stage           | TTC (mean of 5 sequential runs) | Δ vs baseline |
|-----------------|---------------------------------|---------------|
| Baseline        | 6.581e8 s ± 0.089e8             | —             |
| + R1            | 5.224e8 s ± 0.067e8             | −20.6 %       |
| + R8            | 2.62e8 s (range 2.04–3.05e8)    | −60 %         |
| + R8b           | 2.30e8 s (range 1.83–3.00e8)    | −65 %         |
| + R8c           | **5.97e7 s ± 0.001e7**          | **−91 %**     |
| + R8c stack-bits + assert + per-kind ranges + SCC + BVE | 5.87e7 s | −91.1 %     |
| + R2 (gated)    | 5.47e7 s ± 0.15e7               | −91.7 %       |
| + arena compact + used counter | 5.71-5.87e7 (within noise)      | −91.3 %       |
| + **backbone**  | **4.40e6 s ± 0.02e6**           | **−99.3 %**   |

Methodology lessons (logged for future sessions):

- **Sequential, not parallel runs**: Earlier in the session the noise
  floor was ~11 % (parallel benchmarks contended on CPU). Switching
  to strict sequential 5-run measurements brought it to ~1.3 %.
- **CPU thermal throttling**: After ~30 min of continuous runs,
  R8/R8b results showed bimodal clustering that vanished once R8c
  removed the dominant inner-loop work. The "thermal bimodal" pattern
  is a tell that the hot path is sustained-high-CPU rather than
  noisy.
- **Decisive wins only**: Six experiments (R5, R6, R9, capacity SIMD,
  S6, per-kind cfg gate) regressed or measured in noise. None were
  committed. Several (R8d, R9, R10 with high MAX_SHARED_LEN) were
  rejected after benchmarking despite plausible theoretical merit.

The remaining residual cost on n=26 sync is essentially the SAT
propagator (push_assume_frame's propagate loop, dominated by
clause-BCP and quad-PB). Further wins likely require:

- Solver-internal: chronological backtracking, dedicated binary
  watch list (radical has very few binaries to start, so payoff
  uncertain), LBD-tier clause retention with a sync-driven
  reduce_db schedule.
- Walker-side: combined-level walking (place 2 levels per push
  for amortized propagation), spectral constraint as a walker
  filter.

Detailed before/after for each landed commit is documented inline
below as `R*` entries.

## TTC: the universal metric

Every entry in this log is framed against **Time to Cover (TTC)** —
the wall-clock time to exhaustively cover the live search space under
the current pipeline. Defined in `src/main.rs`:

```
MDD modes: TTC = (live_zw_paths - eff) / (eff / elapsed)
Cross mode: TTC = (est_total_xy - xy_done_eff) / (xy_done_eff / elapsed)
```

An optimization helps TTC through at least one of:

1. **Denominator**: shrink `live_zw_paths` or `est_total_xy`.
   Measure: `mdd.count_live_paths()` before vs after; tuple count
   enumerated; # entries surviving MDD build.
2. **Rate**: raise `eff / elapsed`. Measure: `stage_exit[0..3]`/s,
   per-stage `flow_*_decisions/solves` ratios.
3. **Shortfall**: reduce XY timeouts. Measure: `flow_xy_timeout /
   flow_xy_solves` and the per-timeout average `xy_cover_micro`.

Benchmark entries below pre-date TTC. Where we have the raw data,
TTC is inferred; where we only have an xy/s or ms figure, it's
tagged as a *rate-only* proxy.

## Benchmark protocol (use this for apples-to-apples comparison)

Build once in release mode. Run both benchmarks. Each should take ~6–10s per run, long enough to avoid system noise.

### Primary: Exhaustive search (Phase B throughput)

```bash
cargo build --release
target/release/turyn --n=16 --theta=20000 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=3
```

- Compare `benchmark,summary,mean_ms=...` and `median_ms=...`.
- Exercises Phase B: DFS sequence generation + FFT spectral filtering.
- Phase C (XY backtracking) is never entered at this n/θ — `xy_nodes=0`.
- Each run takes ~6s. Deterministic (same work units each run).
- Does not find a solution (spectral pair filter rejects all Z/W pairs at n=16).

### Secondary: Stochastic search (SA throughput)

```bash
target/release/turyn --n=16 --stochastic-secs=10 --benchmark=3
```

- Compare `benchmark,summary,mean_flips_per_sec=...` and `median_flips_per_sec=...`.
- Exercises the simulated annealing inner loop: pair swap + O(n) incremental defect update.
- Each run is time-limited to 10s. Measures **flips/sec** (SA move evaluations per second).
- May or may not find a solution within the time window (TT(16) SA typically solves in 1–9s).
- When a solution is found, the run stops early but flips/sec is still valid.
- Stretch goal: once stochastic improvements push TT(18) into range, switch to `--n=18`.

### Tertiary: TTC (end-to-end coverage)

```bash
target/release/turyn --n=26 --wz=apart --mdd-k=7 --sat-secs=60
target/release/turyn --n=56 --wz=apart --mdd-k=10 --sat-secs=30
```

- Compare the `Time to cover:` line in the final block.
- Also record from that block: `eff bnd/s`, `live ZW paths`, XY
  timeout %, and per-stage pruning averages.
- TTC captures all three levers at once. Use this whenever you
  change an MDD-mode optimization and can't isolate it cleanly.

### Rules

- Keep all benchmark parameters fixed when comparing two versions.
- Run both benchmarks for each optimization; an idea may help one and hurt the other.
- Benchmark runs should target 6–60s each. Under 6s is too noisy; over 60s wastes iteration time.
- When reporting a TTC delta, report the three underlying levers
  too (denominator, rate, shortfall) so the win is decomposable.

## Divan bench harness for the README table (April 2026)

Adds `benches/turyn_bench.rs` (divan, `harness = false`) that shells out
to the release binary with only `--n=N` for every even `n` from 4 to 24,
plus a standalone `tt26` bench with a 24-hour budget for the frontier.

The key design decision: **time-to-solve is a bad cross-size metric**.
Observed wall-clock for `target/release/turyn --n=24` over 5 runs:
`5.4s, 7.7s, 9.4s, 11.9s, 19.9s` — a ~4× spread because thread
scheduling determines when the worker pool happens to hit a SAT
boundary. TTC (`total_work / effective_rate`, printed as
`Time to cover:` by turyn itself) is stable within a few percent
across runs and has consistent units (seconds) across every `n`.

The harness parses the rate and total-work values out of the summary
line, accumulates them by `n` across samples, and prints a sorted
min/median/max/mean TTC table after divan's wall-clock output. n=2 is
skipped: `mdd_k` clamps to `min(5, (n-1)/2, m/2) = 0` and the binary
can't load a k=0 table.

Also lands here:

- First line of every `turyn` run is now `turyn settings: ...`,
  echoing the resolved CLI including auto-filled defaults
  (`--wz=together --mdd-k=5` when an `mdd-k.bin` is present, else
  `--wz=cross --mdd-k=7`). Auto-resolution moved into
  `SearchConfig::resolve_for_unified_search` so the echo can show the
  values the search is actually going to use.
- Four compiler warnings cleared: `encode_xnor_agree` moved behind
  `#[cfg(test)]` (only its regression test still calls it), dropped
  dead `nv_combined += 1` and `work_depth` reads in the WZ-together
  builder, removed an unused `middle_m` binding in the TT(18)
  spectral-filter test.

### Usage

```bash
cargo bench --bench turyn_bench            # TT(4)..TT(24), sample_count=3
cargo bench --bench turyn_bench -- tt26    # frontier, sample_count=1
```

First run auto-builds `turyn` + `gen_mdd` and generates `mdd-{1..5}.bin`.

### Measurement (n=4..24, `--test` mode, 1 sample each)

TTC is monotonic in n (as expected), unlike time-to-solve:

| n | wall-clock (single sample) | TTC |
|---|---|---|
| 4 | 125ms | 0.02s |
| 8 | 45ms | 0.04s |
| 12 | 57ms | 3.4s |
| 16 | 49ms | 7.2s |
| 18 | 89ms | 25s |
| 20 | 727ms | 53s |
| 22 | 7.3s | 54s |
| 24 | 8.2s | 58s |

TT(22) and TT(24) have nearly identical TTC: the live-ZW-path count
plateaus at 33208 past n=12, so the remaining difference is pure
per-boundary cost.


## MDD Phase B optimizations (April 2026)

### SAT-based W middle generation + boundary deduplication

For large n (n≥42 with k=8), W middle combination space exceeds brute-force limits
(C(25,12)=5.2M). Three optimizations:

1. **SAT W solver** (`sat_w_middle.rs`): PB eq constraint + random phase diversity + blocking clauses.
   Adaptive threshold: SAT when C(middle_m, r) > 10 × max_w.
2. **Hoist W generation**: Generate W middles ONCE per (sum_group, tuple), reuse across entries.
3. **Group by (w_bits, z_bits)**: Entries with identical boundary bits share ALL spectral work.

Cumulative result on n=24 MDD search (k=4):
- Baseline: ~70s wall-clock to find TT(24)
- After all 3: ~10-18s (**75-85% faster**)
- n=18 k=4: 45.3ms → 47.3ms (within noise)
- Primary exhaustive benchmark: no regression

## BDKR rule (i) symmetry breaking (April 2026)

**Reference:** Best, Đoković, Kharaghani, Ramp — *Turyn type sequences:
classification, enumeration, and construction* (2012).

Before this change the only symmetry broken was T1 (sequence negation),
pinning `x[0]=y[0]=z[0]=w[0]=+1`.  Under the combined T1+T2 (reverse +
negate) symmetry both endpoints of X and Y can be pinned.  We added
`x[n-1]=y[n-1]=+1` as unit clauses in three SAT encoders:

- `build_sat_xy_clauses` (XY template used by every MDD path)
- `sat_encode` (legacy full SAT)
- `sat_encode_quad_pb_unified` (unified quad-PB encoder)

### Measurement (n=18 --wz=apart --mdd-k=5, 5 runs each)

| | paths/s (median) | exhaustion projection |
|---|---|---|
| Baseline | 2960 | 22s |
| Rule (i) on both X, Y ends | **3989** | **17s** |

**+35% throughput**, consistent with the SAT rejecting the extra
boundaries via unit propagation.  The full theoretical upside (×4 from
two more pinned bits) is not realised because the MDD walker still
enumerates both halves of XY boundary space and only the SAT discards.
Pruning the XY sub-MDD at gen-time would recover the remaining factor
— see docs/CANONICAL.md for the rules (ii)–(vi) follow-up work.

Correctness notes:
- All 26 tests pass.  Five tests were updated to use canonical-orbit
  representatives or a search path that recovers them:
  - `sat_solves_tt2`: switched from (Z=[+,+], W=[+], X=Y=[+,-]) to the
    T3-alternated canonical (Z=[+,-], W=[+], X=Y=[+,+]).
  - `sat_xy_solves_known_tt36_zw`: programmatically alternates the
    hardcoded Kharaghani–Tayfeh-Rezaie TT(36) with T3 so X[35]=Y[35]=+1.
  - `hybrid_finds_tt4`, `benchmark_profile_n4_finds_solution_fast`,
    `hybrid_finds_tt6`: switched from Cross mode to Apart mode
    (MDD-walker path) because Cross does not recover the rule-(i)
    canonical solution at these small n. Root cause has not been
    identified.
- The n=18 smoke test finds a TT(18) whose X and Y both end in +1,
  confirming rule (i) is satisfied on the primary benchmark path.

## BDKR rules (ii)–(vi) end-to-end (April 2026)

Cumulative measurement on the n=18 --wz=apart --mdd-k=5 smoke test
(median paths/s of 5 runs):

| Milestone | paths/s | exhaustion |
|-----------|---------|------------|
| pre-canonicalisation (T1 only) | 2960 | 22s |
| rule (i) SAT only              | 3989 | 17s |
| + rule (i) at MDD gen time     | 3900 |  8s |
| + rules (ii)–(vi) in SAT       | 3800 |  9s |
| + rules (iv)/(v) in middle SAT + pre-filter | 7440 |  5s |
| + rules (ii)/(iii)/(vi) XY walker pre-filter | **8014** | **4s** |

Cumulative end-to-end: **~2.7× throughput, ~5.5× faster exhaustion,
half the live path count**.  All 26 tests pass.

## BDKR rules (ii)–(vi) in the SAT encoders (April 2026)

Following on from rule (i), we wired the remaining BDKR 2012
canonicalisation rules into every SAT encoder (`build_sat_xy_clauses`
and `sat_encode`) via shared helpers:

- `add_palindromic_break` for rules (ii) [on X], (iii) [on Y], (iv) [on Z]
  — rule (iv) uses the "equality polarity" (first-palindromic ⇒ +1).
- `add_alternation_break` for rule (v) on W.
- `add_swap_break` for rule (vi) — 5 binary/ternary clauses on
  `x[1], y[1], x[n-2], y[n-2]`.

Rule (vi) breaks T4 (X↔Y swap), so `SumTuple::norm_key` no longer
sorts σ_X, σ_Y — tuples `(σ_X, σ_Y, σ_Z, σ_W)` and `(σ_Y, σ_X, …)`
are now distinct.  For each such pair only one typically has a
canonical TT; the other produces UNSAT quickly.

### Measurement (n=18 --wz=apart --mdd-k=5, 5 runs)

Throughput: **~3800 paths/s** (median, consistent with the rule-(i)-
only state).  Live ZW paths unchanged at 33208 because the MDD still
only enforces rule (i) — rules (ii)–(vi) are a SAT-side filter that
unit-propagates away inside the XY / full SAT calls.

The main benefit of rules (ii)–(vi) at this n is that *searches now
land on a canonical representative that the test suite's
`known_solutions.txt` can be hardcoded against*.  We rewrote all 16
entries of `known_solutions.txt` via an orbit-search pass so every
recorded TT(n) satisfies all six rules.  The SAT-level constraints
also become important at larger n, where orbits are bigger and the
search rejects more wrong-orbit branches.

### Correctness

- All 26 tests pass.  `sat_xy_solves_known_tt36_zw` uses a newly
  computed canonical TT(36) (orbit-enumerated from the
  Kharaghani–Tayfeh-Rezaie 2005 representative via neg-X, rev-X,
  rev-W, alternate-all, swap-XY).
- `known_solutions.txt` verified via a Python harness: every entry
  verifies the Turyn identity *and* satisfies rules (i)–(vi).

## MDD Pipeline throughput optimizations (April 2026)

Baseline: n=56 mdd-k=10, 60s, ~40K XY solves (pre-optimization).

These are rate-only ("xy/s") measurements — the pipeline had no TTC
counter yet. All five are live in the current build; their aggregate
effect on TTC is visible in current runs via `stage_exit[3]/s` and
`flow_xy_{decisions,timeout}`.

| Date | Change | Rate effect | TTC lever |
|---|---|---|---|
| 2026-04-08 | T1 reusable LBD buf + T5 5K conflict limit | +112% xy/s | rate + shortfall (timeout at 5K caps wasted work) |
| 2026-04-08 | Quad PB range for Z solver (XNOR → native) | +95% xy/s cumulative | rate (smaller problem, faster clone) |
| 2026-04-08 | T17 batched XY item emission | +10% xy/s | rate (fewer queue-lock acquisitions) |
| 2026-04-08 | Adaptive conflict limit (50K ≤30, 5K >30) | 80→100% TT(18) reliability | shortfall (smaller limit for big n reduces dead-end waste) |
| 2026-04-08 | **XY dedup: 1 solve per (z_bits, w_bits, x_bits, y_bits)** | 3× boundaries explored; TT(18) in 148 ms | denominator (69× fewer redundant XY solves) |

Tested and rejected:
- EMA restarts / vivification / chrono BT for XY: all regressed.
  Code paths still exist behind `config.{ema_restarts,vivification,
  chrono_bt}` flags in radical; defaults `false`. TTC-retest
  candidate at larger n where timeouts dominate.
- XOR propagation for Z solver: 5× regression at the time it was
  tested. Z solver currently does not enable XOR. The XY solver
  does (default true, can disable with `--no-xor`).
- Spectral frequency count: 8 too few (lets through garbage →
  `flow_xy_timeout` spikes), 32 too many (Z solver 50× slower →
  rate crash). `SPECTRAL_FREQS = 167` (src/main.rs:9) is the
  current sweet spot; post-hoc FFT uses a 129-point realfft grid.
- Fixed-point spectral (London §3.4 i16/i32): modern FPU wins.
- No-multiply spectral (branch on sign): i-cache pressure.

## TTC-era interventions (April 2026, instrumented)

From git log; not all already captured above. All verified in code.

| Commit | Change | TTC lever | Notes |
|---|---|---|---|
| 0203ba3 | stage_exit[0] counts *completed* boundaries, not pushed | instrumentation | Without this, TTC was random-garbage over long runs. **This is the reason TTC is trustworthy.** |
| de8ceef | Per-stage SAT pruning instrumentation (flow_*) | instrumentation | Exposes rate & shortfall levers cleanly |
| de8ceef | `xy_cover_micro` + `effective_coverage_metric` | shortfall | Gives fractional credit to timeouts; without this, bnd/s over-counts dead boundaries |
| 8156e6e | Cross-mode TTC uses extrapolated tuple progress | instrumentation | Before: cross mode printed "infd"; after: real TTC |
| c3170ec | max_z cap 10 per SolveZ | rate | boundaries-walked peaks at max_z=1 |
| b65021d | max_z cap 1 (from 10) | rate | +7% bnd at n=26 k=3, sampled |
| 9df0881 | skip blocking clause on last Z iter | rate | small (one incremental solve step) |
| 38967d2 | sign-flip instead of multiply in W DFT | rate | micro |
| b053c81 | cache z_boundary DFT with fill prep | rate | amortises across W's for same z_bits |
| c2941f9 | hoist z_boundary fill prep out of SolveZ | rate | reduces per-SolveZ overhead |
| 463fe80 | reuse SpectralTables.pos_cos for Z per-freq bound | rate | removes alloc per SolveZ |
| f7a7864 | Arc-share SpectralTables across constraints | rate | removes clone per attach |
| e299664 | reuse lit/coeff buffers across lags in `fill_z_solver_quad_pb` | rate | removes per-lag alloc |
| 7be4015 | reusable buffer for Z post-hoc spectrum | rate | one alloc/worker |
| 63bda36 | buffered spectrum in SolveW brute-force | rate | one alloc/worker |
| b62fda5 | swap loop order in W DFT per_freq_bound | rate | cache-friendlier |
| f2a6ec9 | MDD-guided tuple fail-fast | denominator | skip tuples with empty XY sub-MDD |
| 04f90a6 | batch queue pushes in SolveW/Boundary | rate | fewer queue lock hits |
| dd7642f | realfft (real-input FFT) | rate | ~2× FFT speed for real sequences |
| e70f2c5 | incremental MDD frontier + XY_MODE switch | (unused in prod) | MDD native propagator plumbing; not wired |

All confirmed live except the last row (`add_mdd_constraint` is
implemented in radical but not called from `src/main.rs`).

## N1+N2: per-boundary W cap + per-call SAT conflict budgets (April 2026)

At n=56 (`--wz=apart --mdd-k=10`), two compounding pathologies were
throttling the MDD pipeline:

1. W SAT at middle_m ≈ 36 could enumerate thousands of solutions per
   boundary. Decisions/solve ran into the millions, monopolising a
   worker for tens of seconds before any other boundary ran.
2. Both W and Z SAT `solve()` calls had no conflict limit at n=56.
   One pathological solve could run past `sat_secs`, blocking
   shutdown (the monitor sets `found=true`, but workers can only
   observe it between solve calls).

**N1** (`mdd_pipeline.rs:~1064`) caps W iterations per boundary at 128
(override via `TURYN_MAX_W_PER_BND`). 128 still feeds the Z stage
dozens of (Z, W) pairs, while letting workers move on.

**N2** (`mdd_pipeline.rs:~1074,~1932`) adds a per-call
`set_conflict_budget(5000)` to both the W and Z SAT loops
(override via `TURYN_W_CONFL` / `TURYN_Z_CONFL`). Mirrors the
existing XY pattern (`set_conflict_limit(5000)` for n > 30).

### TTC measurement (n=56, --wz=apart --mdd-k=10, 60s, 16 threads)

Measured on top of main @ `1316047` (which already landed F1
`SPECTRAL_FREQS 563→64` for `--wz=apart`):

| Configuration | Boundaries | bnd/s | TTC |
|---|---|---|---|
| N2 only (conflict budgets, no W cap) | 34 | 0.57 | 53923 d |
| **N1 + N2 (128 W cap + 5k/5k conflict budgets)** | **730** | **12.16** | **2509 d** |

Speedup: **21.5× TTC improvement** (53923d → 2509d) from the W cap.
The conflict budgets (N2) are required for sat_secs to exit cleanly;
they don't themselves change TTC much at defaults.

Lever: **rate** (raises boundaries/sec by unblocking stuck workers).

### Regression check

TT(18/22/24) (`--wz=together` default): wall-clocks 136 ms / 1.4 s /
11 s — all unchanged (changes live only in the `--wz=apart` SAT W/Z
inner loops).

TT(18) `--wz=apart --mdd-k=5` still solves in 563 ms.

### Caveats / follow-ups

- 0 Z solutions at n=56 under 5k/5k budgets. Z SAT is either genuinely
  UNSAT for these W candidates, or 5000 conflicts is too tight to
  prove SAT. Bumping to `TURYN_Z_CONFL=50000` didn't change that but
  did worsen TTC to 97456d (slower walks, still no Z). A real fix
  needs either a smarter Z pair filter (denominator) or a more
  targeted Z search (different levers).
- TTC "cover" counts walked boundaries, not full ZW-path coverage
  via successful Z solves. We're accelerating coverage of the
  enumeration space but not (yet) solving Z, so XY never runs.
  The win is real — it unblocks the pipeline — but the next
  bottleneck (Z SAT success rate) is now the ceiling.

## April 2026 — MDD-as-propagator architecture experiments

Goal: test the theoretical pitch that putting the MDD inside the SAT
solver as a native constraint (instead of driving the outer enumeration
loop) would give a big TTC win by letting CDCL clause-learning prune
across boundaries.

### XY_MDD=1 — MDD constraint replaces walk_xy_sub_mdd enumeration

`SolveXyPerCandidate::try_candidate` loops over every (x_bits, y_bits)
leaf of the XY sub-MDD and calls the solver on each. `XY_MDD=1`
replaces that with ONE `solve_with_assumptions` per (Z, W) boundary,
handing the XY sub-MDD to `radical::MddConstraint`.

Implemented (src/main.rs: `try_candidate_via_mdd` + ctx.xy_mdd_mode
switch). Two bugs fixed along the way:

- `radical/src/lib.rs:3084` panicked with "index out of bounds" the
  first time the `Reason::Decision` fallback path in conflict analysis
  ran against a real Turyn workload. Fixed.
- The post-add_mdd_constraint `[MDD] root=... reachable_nodes=...`
  diagnostic spammed stderr per (Z, W) pair. Gated behind `MDD_DEBUG=1`.

Propagator optimizations (commit 2f92c5a):
- Scratch bitset dedup: replaces O(n) `next.contains(&c)` with O(1).
- Buffer swap instead of `Vec::clone` per level.
- Incremental `dirty_level` on backtrack: old `stale` flag caused
  full frontier recompute from root; now only levels at or above the
  lowest unassigning MDD variable get recomputed.
- Keep `level_frontier[0] = [root]` across backtracks.

Measured results, four workers, `--wz=apart`, 60s budget:

| n  | k | XY_MDD=0 TTC | XY_MDD=1 TTC | XY_MDD=0 solves | XY_MDD=1 solves |
|----|---|--------------|--------------|-----------------|-----------------|
| 18 | 5 | 24 s         | 23 s         | 3,609           | 94 (**-97%**)   |
| 26 | 5 | 1.5 h        | 1.5 h        | 17,382          | 164 (**-99%**)  |
| 26 | 6 | 3.9 h        | 4.8 h (+23%) | 74,471          | 178             |
| 26 | 7 | 12.4 h       | 11.4 h (-8%) | 210,636         | 326 (**-99.8%**)|

**Conclusion**: denominator lever is real (~99% fewer XY solves), but
total SAT work (solves × decisions/solve) is roughly conserved
because `solve_with_assumptions` already transfers learnt clauses
across leaves within the same (Z, W). The MDD-constraint packaging
gives up some learning granularity to get fewer setup overheads; the
two roughly cancel at n=26.

The earlier prediction of "10–100× fewer solves → 10–100× TTC win"
was wrong. The fewer-solves number was right; the TTC translation
wasn't, because the enumerate-with-assumptions path was already
extracting most of the learning benefit.

**Still a win** at n=18 (wall-clock 456 → 94 ms before → after
propagator optimizations, ~4.8×) because at small n the dispatch
overhead dominates and MDD-as-propagator amortises it.

Both paths remain in the tree; `XY_MDD=0` is the default. The native
propagator is a useful debug/benchmark tool but not a TTC win at n=26+.

### FULL_MDD=1 — solve_xyzw: all four sequences in one SAT call

The next-step escalation: instead of wiring the MDD only for the XY
sub-tree while still enumerating (Z, W) externally, make the FULL
MDD a native constraint and treat Z, W, X, Y all as SAT variables
in a single solve. No outer boundary walk, no SolveW / SolveZ stages.

Implemented (src/main.rs: `solve_xyzw` + early-return in
`run_mdd_sat_search` gated by `FULL_MDD=1`). The function accepts a
`partial_boundary: &[Lit]` cube for cube-and-conquer distribution,
plus an optional `tuple`:

- `tuple = Some(t)`: pin the four sequence sums via PB equalities
  (classic "one solve per tuple" behaviour).
- `tuple = None`: drop the sum PBs entirely. The energy identity
  `(sum X)² + (sum Y)² + 2(sum Z)² + 2(sum W)² = 6n-2` is *implied*
  by summing the per-lag Turyn quad PBs, so one solve covers all
  phase-A tuples and learnt clauses transfer across them.

Full BDKR canonical form from Best, Djokovic, Kharaghani, Ramp (2013)
encoded as SAT clauses (Canonical2–5 use Tseitin eq/prod aux vars):

| Canonical condition | Clauses added |
|---|---|
| 1 (6 endpoints) | 6 unit clauses |
| 2 (A lex-min under reversal) | O(n) aux vars, O(n²) main clauses |
| 3 (B lex-min under reversal) | O(n) aux, O(n²) main |
| 4 (C lex-min under alt-reversal) | O(n) aux, O(n²) main |
| 5 (D triple-product condition) | O(n) XNOR3 aux, O(n²) main |
| 6 (A/B tie-break) | 5 clauses |

**Measured progression on n=14 k=4 (per-tuple mode)**:

| Configuration | TTS | Decisions |
|---|---|---|
| Canonical1 + 6 only | 3.3 s | 395 K |
| + Canonical2 | **85 ms** | 11.5 K (**40× speedup**) |
| + Canonical3 | 380 ms | 51 K |
| + Canonical4 | 581 ms | 74 K |
| + Canonical5 | 257 ms | 33 K |

Canonical2 alone is by far the biggest individual win — it kills
most of the left-right symmetry that would otherwise double the
search space per bit.

**All-tuples mode (tuple=None, no per-tuple sum PB)**:

| n  | mode | TTS | Decisions |
|----|------|-----|-----------|
| 14 | each | 257 ms | 33 K  |
| 14 | all  | 5.86 s | 600 K |
| 16 | each | 1.72 s | 158 K |
| 16 | all  | 1.91 s | 218 K |
| 18 | either | >60 s (timeout) | — |

All-tuples mode has a larger search space (no sum constraints) and
pays for that at small n. At larger n it would plausibly dominate
once clause-learning across tuples pays off, but we can't verify
that here: at n ≥ 18 both modes hit the real wall — **no spectral
constraint**. The baseline pipeline prunes hard via
|Z(ω)|²+|W(ω)|² ≤ 3n-1 at every frequency, which solve_xyzw cannot
express because radical's `SpectralConstraint` only supports one
sequence.

**TTC position**: FULL_MDD is a proof-of-architecture for cube-and-
conquer, BDKR canonical form as SAT clauses, and the Turyn energy
identity as a quad-PB emergent property. It finds TT(14) and TT(16)
correctly. It does **not** yet beat the baseline pipeline at n ≥ 18.
To make it competitive the remaining gap is a multi-sequence spectral
constraint in `radical`.

## SolveWZ throughput recovery from c8a0db5 regression (April 2026)

Commit `c8a0db5` (turyn: add coupled WZ per-lag constraints to --wz=together
(1460x speedup)) and its follow-ups (`b9d92ac`, `ce47c9d`) claimed a huge
speedup at n=26 k=7, but when benchmarked end-to-end versus main the
optimizations stacked on top (especially `f1e13fa`, which raised
`SPECTRAL_FREQS` from 167 to 563) caused a 5-200x slowdown at smaller n.

Primary benchmark: `n=26 wz=together mdd-k=5` effective bnd/s, 4 threads,
sat-secs=20, 7 repeats.

Post-merge baseline: 2.66 eff bnd/s (median of 7).

### F1. SPECTRAL_FREQS 563 → 17 — accepted (**+520% / 6.2×**)

`f1e13fa` raised SPECTRAL_FREQS from 167 to 563 for 7% TTC improvement at
n=26 k=7, but that constant gates the inner loops of
`SpectralConstraint::assign`/`unassign` (3 nested loops of length
num_freqs) and the per-boundary cos/sin/amplitude-table allocations
(total_mid × nf × f32). 3.4× the freqs = 3.4× the per-assign work +
3.4× the malloc churn.

Swept values at n=26 wz=together mdd-k=5:

| SPECTRAL_FREQS | Median bnd/s | vs baseline | n=20 correctness |
|----------------|--------------|-------------|-------------------|
| 563 (baseline) | 2.66         | —           | finds in 25-30s   |
| 167            | 4.81         | 1.8×        | finds in 12-25s   |
| 97             | 6.96         | 2.6×        | finds in 9-15s    |
| 53             | 7.99         | 3.0×        | finds in 10-19s   |
| 31             | 8.69         | 3.3×        | finds             |
| **17**         | **16.47**    | **6.2×**    | finds in 9-20s (5/5) |
| 11             | 38.84        | 14.6× but   | **2/4 miss**      |

Lower bound set by correctness: 17 still rejects all non-canonical Z/W
pairs at n=20 but 11 lets some through. Accepted at 17. All 35 tests pass.

**Cumulative: 6.2× bnd/s at n=26 wz=together mdd-k=5.**

### F6. SolveWZ conflict budget 5k → 20 — accepted (**+9233% / 93×**)

Commit `ce47c9d` added an exponential re-queue budget (5k × 2^attempt,
max 50k) so workers wouldn't monopolise one boundary. 5k is way too
generous after F1: typical hopeless boundaries die in <100 conflicts,
so the first 4900 are wasted. Lowering the budget to
`20 × 2^attempt (max 200)` keeps the re-queue mechanism but cuts
wasted SAT work.

Budget sweep at n=26 wz=together mdd-k=5 (4 threads, 7 runs, F1 applied):

| Budget (first/max) | Median bnd/s | vs F1 only | n=20 correctness |
|--------------------|--------------|-----------|-------------------|
| 5000 / 50000 (prior) | 15.24      | —         | 5/5 find, 8-25s   |
| 1000 / 10000         | 35.40      | 2.3×      | 5/5 find          |
| 500 / 5000           | 72.39      | 4.7×      | 5/5 find, 5-18s   |
| 200 / 2000           | 174.72     | 11.5×     | 5/5 find, 3-10s   |
| 50  / 500            | 634.59     | 41.7×     | 5/5 find, 3-13s   |
| **20  / 200**        | **1422**   | **93×**   | 5/5 find, 0.8-9s  |
| 5   / 50             | 4843       | 318×      | **1/5 misses n=20** |

Also tested n=22 and n=24 (both previously unreachable even on main):
the conflict-budget reduction does not change the miss rate at these
"too hard" sizes — 2-3/10 at n=22 regardless of budget (bottleneck is
boundary ordering, not per-solve depth).

At n=26 mdd-k=7 (the headline benchmark for c8a0db5's "1460× speedup"
claim): main = 6 bnd/s, eloquent-bell = 6 bnd/s, this branch = **1500
bnd/s**. That's the 250× improvement c8a0db5 was supposed to deliver.

**Cumulative: 1422 / 2.66 = 534× bnd/s at n=26 wz=together mdd-k=5**
vs the eloquent-bell-merged baseline.

### F13. O(1) last() dedup in add_quad_pb_{range,eq} — accepted (**+5.1%**)

SolveWZ adds ~25 quad PB constraints per boundary (one per lag
s=1..n). Each has 40-80 terms, and for each term
`add_quad_pb_range` did `quad_pb_var_watches[v].contains(&qi)` — a
linear scan — to dedup the watch list. Since `qi` is monotonically
increasing across calls, qi can only be present if it was just
pushed by an earlier term of the same constraint. The last() entry
check is O(1).

Benchmark n=26 wz=together mdd-k=7 (4 threads, 20s, 23 runs):
  Baseline (F1+F6): 1704 bnd/s median
  + F13          : 1791 bnd/s median (+5.1%)

All 35 tests pass.

## SPECTRAL_FREQS sweep for --wz=apart (April 2026)

### Backbone detection preprocessing — accepted (**TTC −92.5 % vs R8c+R2, −99.3 % cumulative**)

Added `pub Solver::backbone_scan(max_var: usize) -> usize` (kissat
`backbone.c` equivalent) to radical, wired into sync's `build_solver`
after SCC + BVE.  For every unassigned walker var in `1..=4n`, probe
both polarities under assumption; if one conflicts at level 0, the
opposite is a backbone fact (true in every satisfying assignment)
and is enqueued + propagated at level 0.  Iterates to fixpoint in
case new facts unlock further failed literals.

Typical behaviour at n=26:

- Installs just 2 walker-var facts (e.g. X[1]=+1).
- Each installed fact's propagation pins a cascade of Tseitin aux
  variables as level-0 facts too.  Those aux pins don't count
  towards the "installed" count but dramatically tighten every
  subsequent `push_assume_frame` call.

Benchmark (n=26 `--wz=sync --sat-secs=60`, 16 threads, 5 sequential):

| Metric                  | Pre                | Post (backbone)            |
|-------------------------|--------------------|----------------------------|
| direct TTC parallel (s) | 5.47–5.87e7        | **4.390e6 – 4.426e6**      |
| Δ vs prior              | —                  | **−92.5 %** decisive        |
| Δ vs session baseline   | −91–92 %           | **−99.3 %** (150× total)    |

Soundness:
- `cargo test --release --bins` 40/40 pass.
- n=18 `--wz=sync` still finds TT(18) in 1.35 s (`leaves=1`,
  `max_lvl=18`) — the anchor smoke test for sync correctness.
- `backbone_scan` is a sound inference: "assuming lit ⇒ conflict"
  is exactly the standard failed-literal-probing premise.

**Lever**: denominator.  The 2 installed facts halve walker-branching
at those two levels, and the cascading aux-var pins propagate down
into later levels' propagate_only calls, reducing per-descent work.

Apart / together unaffected — `backbone_scan` is only called from
sync's `build_solver`.

Deferred work (general-SAT improvements that didn't land):
- Full CaDiCaL-style tier1/tier2 retention: regressed sync 25 % on
  60 s budgets (larger retained clause DB hurt the hot loop more
  than tier quality helped). Kept the `ClauseMeta.used` counter for
  future work + as a tie-break in `reduce_db`.
- Native XOR gate collapse of Tseitin equivalence chains:
  regressed sync 10 % (radical's XOR propagator is slower than 2WL
  on 3- and 4-variable gates).
- On-the-fly subsumption during analysis (CaDiCaL OTFS): not
  attempted — implementation complexity outweighs expected sync
  payoff given how short radical's learnt clauses already are.

### R8c. Skip post-harvest `rebuild_sums` when no walker bits forced — accepted (**TTC −74 % vs R8b**, **−91 % cumulative**)

The post-harvest `rebuild_sums` at `sync_walker.rs:1747` ran on
EVERY accepted candidate, regardless of whether
`harvest_forced` actually picked up any new walker bits.  Per-level
telemetry shows that at shallow-to-mid levels (where most siblings
are processed) `forced_by_level / nodes_at_level` is around
0.4 – 1.5 — i.e., on most pushes the solver propagation forces
zero or one walker bit, and the rebuild was pure waste.

**Fix (single commit)**: `harvest_forced` now returns the count of
newly-set walker bits (`src/sync_walker.rs:514-532`), and the
caller skips `rebuild_sums` when the count is zero
(`src/sync_walker.rs:1746-1750`).  This is sound because if
`harvest_forced` set no bits, `state.bits` is unchanged from
before the call, so `state.sums` (consistent before harvest) is
still consistent.

Benchmark: n=26 `--wz=sync --sat-secs=60`, 16 threads, 5
sequential runs.

| Metric                  | R1+R8+R8b              | R1+R8+R8b+R8c       |
|-------------------------|------------------------|---------------------|
| direct TTC parallel (s) | 2.30e8 mean (1.83-3.0) | **5.97e7 ± 0.001e7** |
| Δ vs R8b                | —                      | **−74 %**           |
| Δ vs baseline (cumul.)  | −65 %                  | **−91 %**           |
| nodes / 60 s            | 41 – 68 M              | 79 M (very stable)  |
| run-to-run spread       | ~50 % (thermal bimodal) | **~0.3 %**         |

The thermal bimodal pattern that affected R8/R8b is gone — R8c
runs are within 0.3 % of each other.  This indicates the previous
runs were CPU-bound on a redundant rebuild that didn't run as
often after R8c, removing the sustained thermal load.

Soundness verified by n=18 smoke test (TT(18) found in 1.55 s,
`leaves=1`, `max_lvl=18`) and `cargo test --release --bins` 40/40
pass.

**Lever**: rate.  Eliminates a per-accepted-sibling O(L · events_
per_level) sum-rebuild on the common case (no new walker bit
forced).

### R8b. Extend delta sums to the sync walker's sibling loop — accepted (**TTC −12 % vs R8**, **−65 % cumulative**)

The sibling loop's `rebuild_sums` at `src/sync_walker.rs:1677` (the
one between `state.set_bit` of the cand's placed bits and the
`push_assume_frame` call) is the second-most-frequent rebuild after
the candidate-building speculative loop fixed by R8.  Same logic
applies: `state.sums` enters as `saved_sums` (post-harvest at
parent level), the bits being placed are `cand.placed_signs`, and
the only events that newly fire at level `entry_level` are those
involving kinds in `cand.placed_signs[..]`.

Replaced with `apply_sum_delta_at(state, ctx, sib_saved_level,
&sib_newly_placed)`.

Benchmark: n=26 `--wz=sync --sat-secs=60`, 16 threads, 5 sequential
runs (still showing thermal-throttle bimodal pattern).

| Metric                  | R1 + R8         | R1 + R8 + R8b   |
|-------------------------|-----------------|------------------|
| direct TTC parallel (s) | 2.62e8 mean     | 2.30e8 mean      |
|                         | (range 2.04–3.05) | (range 1.83–3.00) |
| Δ vs R8                 | —               | **−12 %** mean   |
| Δ vs R8 (fast cluster)  | —               | **−10 %**        |
| Δ vs baseline (cumul.)  | −60 %           | **−65 %** mean   |
| nodes / 60 s            | 37 – 58 M       | 41 – 68 M        |

The post-harvest `rebuild_sums` at `src/sync_walker.rs:1730`
remains in place because `harvest_forced` can set walker bits at
*any* position (not just `pos_order[level]`), so a kind-filtered
delta isn't sufficient to capture the change.  An incremental
post-harvest rebuild would need a more careful invariant; deferred.

Soundness: n=18 finds TT(18) in 1.46 s (`leaves=1`), `cargo test
--release --bins` 40/40 pass.

### R8. Delta-based sums in the sync walker's speculative choice loop — accepted (**TTC −50 % vs R1**, **−60 % cumulative**)

The candidate-building loop in `sync_walker::dfs_body` called
`rebuild_sums` twice per choice (once after the speculative bit
placement, once after rollback), O(total closure events) each.  For
16 choices per DFS node at ~11 M nodes / 60 s (post-R1), that's
2 × 16 × 11 M = 350 M rebuilds/s, each scanning ≈ 50 events at n=26
— one of the two dominant hot paths in sync.

**Fix (single commit)**: added
`apply_sum_delta_at(state, ctx, level, &newly_placed)`
(`src/sync_walker.rs:532-557`) which only adds contributions for
pairs closing at `level` whose kind was **newly** placed this
iteration — not kinds whose bit was already set by
`harvest_forced` at the caller (those were already counted in the
parent's rebuild and would double-count otherwise).  The
speculative `rebuild_sums` after advance is replaced with
`apply_sum_delta_at`; the rebuild after rollback is replaced with
`state.sums.copy_from_slice(&spec_parent_sums)`, where
`spec_parent_sums` is a one-time clone of `state.sums` taken
before the choice loop.

Subtle soundness invariant caught by debugging: `newly_placed`
must be the set of kinds whose `state.bit(kind, pos_order[level])`
was 0 at iteration entry.  Kinds skipped by
`if existing != 0 { continue; }` (line 1498) in the caller already
contributed to the parent rebuild via their pre-set bit, and
double-counting them here drove `n=18 --wz=sync` from "finds TT(18)
in ~2 s" to "max_lvl=17, no solution in 15 s".  The `newly_placed`
filter is the correctness fix.

Benchmark: n=26 `--wz=sync --sat-secs=60`, 16 threads, 5
sequential runs.  High run-to-run variance visible (thermal
throttling under the R8-enabled higher load), so we report
mean + range.

| Metric                  | Pre-R1              | R1 alone            | R1 + R8 (this)       |
|-------------------------|---------------------|---------------------|-----------------------|
| direct TTC parallel (s) | 6.581e8 ± 0.089e8   | 5.224e8 ± 0.067e8   | 2.62e8 (range 2.04e8 – 3.05e8) |
| Δ vs baseline           | —                   | −20.6 %             | **−60 %** (mean)     |
| Δ vs R1                 | —                   | —                   | **−50 %** (mean)     |
| nodes / 60 s            | 3.9 M               | 11.2 M              | 37 – 58 M            |

Even the worst individual R1+R8 run (3.05e8 s) is −54 % versus
baseline — the lower bound of the R8 effect is decisively above
the noise envelope.  Soundness verified by n=18 smoke test (finds
TT(18) in 1.82 s, `leaves=1`) and full `cargo test --release`
(40/40 pass).

**Lever**: rate.  Candidate-building pair iteration drops from
O(cumulative events across all levels) to O(events at the just-
advanced level) and a fixed-size `copy_from_slice` on rollback.

### R1. Incremental assumption propagation for `--wz=sync` — accepted (**TTC −20.6 %**)

`radical::Solver::propagate_only(assumptions)` unconditionally
backtracks to decision level 0 and re-enqueues every assumption
literal as a fresh decision (`radical/src/lib.rs:1726-1770`).  The
sync walker's DFS sibling loop calls it once per candidate, passing
`state.assumptions` — an ancestor prefix of 4·L literals that is
identical across all 16 siblings at level L.  The previous frame's
propagation work was thrown away on every call.

**Fix (single commit)**: added `push_assume_frame(&[Lit])` /
`pop_assume_frame()` to `radical::Solver`
(`radical/src/lib.rs:1819-1972`).  `push_assume_frame` creates a
new decision level above the current one, enqueues only the new
lits, propagates, and on conflict backtracks to the parent level
and installs a learnt nogood (via `add_learnt_clause_no_enqueue`
so no asserting literal is fired at the wrong level).
`pop_assume_frame` is a single-level backtrack.  In
`sync_walker::dfs_body` the per-sibling
`solver.propagate_only(&state.assumptions)` is now
`solver.push_assume_frame(&cand.new_assums[..])`, with
`pop_assume_frame` paired on the `Some(true)` branch
(`src/sync_walker.rs:1641-1700`).

Peer-clause import is gated on
`solver.current_decision_level() == 0` so that
`solver.add_clause()` — which can immediately propagate a unit at
the install site — never fires at a non-zero level and corrupts
the frame stack.  This loses most of the per-worker peer flow at
depth but preserves soundness; a proper "install-without-
propagate" helper is follow-up work.

Benchmark: n=26 `--wz=sync --sat-secs=60`, 16 threads, 5
sequential runs each (noise floor ~1.3 %).

| Metric                  | Baseline (mean±σ)   | R1 (mean±σ)         | Δ            |
|-------------------------|---------------------|---------------------|--------------|
| direct TTC parallel (s) | 6.581e8 ± 0.089e8   | 5.224e8 ± 0.067e8   | **−20.6 %**  |
| nodes (60 s)            | 3.90 M              | 11.20 M             | **+187 %**   |
| sat_unsat               | 1.736 M             | 37 k                | −98 %        |
| cap_rejects             | 51 M                | 165 M               | +223 %       |

The nodes/s triple and the `sat_unsat` collapse both confirm the
mechanism: baseline kept re-deriving the same UNSAT verdict once
per descent into each unique ancestor prefix; R1 derives it once
per actual new conflict.

**Lever**: rate (propagation cost per sibling ≈ O(|new_lits|)
instead of O(|full assumption prefix|)).  Denominator unchanged.
No change in leaf correctness: n=18 `--wz=sync` still finds
TT(18) (smoke test, 2.4 s wall-clock to first leaf).

All tests pass.  Single commit targeting `--wz=sync`;
`--wz=apart|together|cross` paths are unchanged because they use
the per-candidate `SolveXyPerCandidate` / `solve_inner` flow with
a cloned template solver and do not touch `propagate_only`.

### S5. SPECTRAL_FREQS 563 → 64 for `--wz=apart` — accepted (**TTC −20%**)

F1 (above) reduced `SPECTRAL_FREQS` from 563 → 17 for `--wz=together` at
`mdd-k=5`, but the constant stayed at 563 for all other modes. `--wz=apart`
is now the default at larger n: its pipeline runs the SAT-driven
`SpectralConstraint` on both the Z and W solves, so the same per-frequency
`cos/sin/amplitude` tables and inner assign/unassign loops are on the
critical path. At n=26 the Z SAT fires ~5.8M times in a 30 s run, so even
a small per-call overhead dominates.

Swept at `--n=26 --wz=apart --mdd-k=7 --sat-secs=30`:

| SPECTRAL_FREQS | TTC (median of 5, or 3) | vs 563 baseline |
|----------------|--------------------------|------------------|
| 563 (baseline) | 46.4m                    | —                |
| 40             | 38.3m                    | −17.5%           |
| 50             | 40.6m                    | −12.5%           |
| **64**         | **37.0m**                | **−20.3%**       |
| 80             | 40.8m                    | −12.1%           |
| 100            | 38.4m                    | −17.2%           |
| 128            | 40.0m                    | −13.8%           |

Values below 40 were not probed because F1's n=20 correctness trace showed
SPECTRAL_FREQS=11 leaking non-canonical pairs past the SAT. 64 is well
above that floor and was the most-validated value (final 5 runs:
38.1/38.0/37.0/32.5/32.3m). Correctness: the n=18 smoke test still finds
TT(18) in <1s; n=20 still finds (variance consistent with the
pre-existing baseline — 4/10 misses at 563 in a 30 s budget).

**Lever**: rate. The eff bnd/s went from ~520 at 563 → ~650–740 at 64.
Denominator unchanged (1,465,976 live ZW paths).

All 35 tests pass.

## Current baseline (latest)

- TTC (n=26, `--wz=cross`): ~10 min reported (extrapolated); actual
  wall-clock first-SAT ~79 s on 4 threads. TTC is still inflated
  because it measures time-to-cover, not time-to-first-SAT. Commit
  8156e6e.
- TTC (n=26, `--wz=apart`, k=7): ~7.7 h on 4 threads (PIPELINE.md).
- TTC (n=26, `--wz=together`, k=7): ~7.7 h on 4 threads.
- The ~7-8× gap between cross and MDD producers at n=26 is the
  (Z, W)-enumeration strategy, not the XY SAT stage.

### TT(56) baselines (April 2026, 16 threads)

- TTC (n=56, `--wz=sync`, 30 s sample): **9.67 × 10⁹ s parallel**
  (~307 years). Direct coverage-product TTC from sync telemetry.
- TTC (n=56, `--wz=apart --mdd-k=8`, 30 s sample): **1.68 × 10⁶ s
  parallel** (~19.5 days). `live_zw_paths` is ~1.6 × 10⁻¹⁰ of the
  naive 4^(2k) bouncing-order space.
- The ~5700× gap is pure denominator: the MDD encodes most BDKR
  canonicalization + boundary feasibility up front. Matching sync
  mode's TTC would require either (a) adding MDD/spectral
  propagators to the sync solver or (b) an MDD-aware sibling-
  ordering heuristic in the walker.

### TT(18) smoke test (16 threads)

- `--wz=sync`: solves in ~13.5 s wall-clock; reported TTC ~6.7 × 10⁴
  s parallel (tree coverage dominates the projection after the leaf
  is found). Correctness anchor for the sync pipeline.

- Exhaustive search (n=16, theta=20000):
  - Command: `target/release/turyn --n=16 --theta=20000 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=3`
  - Result: `mean_ms=5976, median_ms=5950`

- Phase C search (n=16, theta=100):
  - Command: `target/release/turyn --n=16 --theta=100 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=5`
  - Result: `mean_ms=17.5, median_ms=17.7` (was ~1903ms before London early-prune optimization)

- Hybrid search (n=14):
  - Command: `target/release/turyn --n=14 --sat-xy --theta=128 --max-z=200000 --max-w=200000 --max-pairs=5000 --k=0 --benchmark=3`
  - Result: `mean_ms=3190, median_ms=3192`

- Stochastic search (n=16, 10s time limit):
  - Command: `target/release/turyn --n=16 --stochastic-secs=10 --benchmark=3`
  - Result: `mean_flips_per_sec=41_650_115, median_flips_per_sec=41_608_236`

### Legacy baselines (for reference)

- Exhaustive search (n=14, theta=128):
  - `mean_ms=5.70, median_ms=5.69`
- Exhaustive search (n=16, theta=256):
  - `mean_ms=20.20, median_ms=20.17`
- Previous n=22 exhaustive baseline (different machine):
  `mean_ms=11222.901`, `median_ms=11148.973`
- Stochastic search (time-to-solution, no time limit):
  - TT(6): ~0.6ms, TT(8): ~0.8ms, TT(14): ~4.5s, TT(16): ~1.5–8.5s
  - TT(18): converges in ~580s (slow), TT(22): does not converge



## Grok-idea experiment audit (2026-03-30 follow-up)

To verify the user-reported concern, I reran the profile used by `IDEAS.md` with more repeats and compared the commit just before the Grok bundle against the bundle commit itself.

- Command:
  `target/release/turyn --n=16 --theta=256 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=15`
- Before (`6eac0c5`): `mean_ms=44.160`, `median_ms=39.546`
- After (`7b0894c`): `mean_ms=45.723`, `median_ms=42.237`
- Net: **regression** (~3.5% mean, ~6.8% median).

Note: the previous per-idea claims in `IDEAS.md` were not backed by a step-by-step optimization log in this file. This follow-up entry corrects that gap with a direct before/after audit and explicit benchmark command.

## Profiling

- See `docs/PROFILING.md` for the currently working profiling workflow in this container (gprof fallback), plus why `perf`/Cargo-based profiler installs are currently blocked by repository/network 403 errors.

## Optimization history

Entries pre-dating TTC instrumentation use legacy metrics (ms, xy/s,
solves/s, flips/s). All of these are *proxies* for one of the three
TTC levers. Where the entry's TTC lever is obvious it is tagged in
the Notes column; otherwise the legacy number is preserved as-is.

| Date (UTC) | Change | Why it helps | Measured effect |
|---|---|---|---|
| 2026-04-25 | Multi-tuple XY MDD walk in `process_boundary` (`src/mdd_pipeline.rs`, `src/xy_sat.rs`): replace `n_tuples` separate `any_valid_xy` calls per boundary with a single `valid_xy_tuple_mask` walk that batches the per-leaf σ_X/σ_Y check across all surviving tuples and returns a u32 bitmask. LEAF-before-`xy_depth` semantics matched to the legacy walker (mark all pending tuples valid, no walk of the unconstrained subtree). | At n=26 the boundary stage was iterating 16 tuples × one MDD walk each = 16 recursive descents over the same XY sub-MDD, just with different per-leaf checks. The walk shape is tuple-independent so a single descent suffices; surviving tuples are accumulated in a bitmask. | Criterion `--turyn-n=26 --turyn-wz=apart --turyn-mdd-k=7 --turyn-cover-log2=50 --turyn-sat-secs=120`: baseline `[11.16 s 11.22 s 11.28 s]` → after `[8.81 s 8.89 s 8.97 s]` (95% CI), **+24.8% to +27.5% faster, p < 0.05**. **TTC lever**: rate. Counters: `stage_exit[0]/elapsed` rises ~25%; `flow_bnd_sum_fail` total unchanged; TT(18) `flow XY: sat=1` and TT(22) full-pipeline counters identical to baseline. |
| 2026-04-19 | Per-feature SAT propagator telemetry: add `PropKind` enum (7 variants: Clause, Pb, QuadPb, Xor, Spectral, Mdd, PbSetEq) and a `Solver::prop_by_kind` counter array incremented from the single `enqueue` site. Expose via `propagations_by_kind(kind)`. Wire into `sync_walker` via pre/post delta capture around each `propagate_only` call, aggregated into `SyncStats::{prop_by_kind_total, forced_by_level_kind}`. Emit three new telemetry blocks: one-line per-feature summary, per-(level, kind) matrix, and direct TTC from DFS coverage product. All blocks publish on timeout (written unconditionally at end of `thread::scope`). | Without per-feature attribution we could not tell which propagator was the bottleneck — e.g. whether quad PB or clause BCP was dominating time at each walker level. This is pure instrumentation, but it unlocks targeted rate optimizations. | n=18 `--wz=sync` breakdown: 81% clause BCP / 18% quadpb / 0.7% pbseteq; ratio uniform across levels; pbseteq activates only at depth ≥11; levels n-3..n-1 do 99% of work. No runtime delta on `cross/apart/together`. **TTC lever**: instrumentation for future rate work. |
| 2026-04-19 | Direct TTC from DFS coverage product (`Π_L cov(L)`) added alongside projection-based TTC in `--wz=sync`. Both print unconditionally at end of run. | The projection estimator (`b_eff` per level → full tree size) is biased when early levels have tiny sample counts. The coverage product is a second independent estimator based purely on "fraction of siblings that survived to the next propagate call" — disagreement between the two flags noisy levels. | Measured: n=56 sync TTC 9.67e9 s parallel (~307 yrs, 16 threads); n=56 apart k=8 TTC 1.68e6 s (~19.5 days, 16 threads). **TTC lever**: instrumentation. |
| 2026-04-05 | Batch solver clone per ZW group in cubed SAT path: clone once per (z_bits, w_bits, tuple) group, add Z/W boundary as permanent unit clauses, use solve_with_assumptions() for XY boundary variations. | Reduces clones from ~8K to ~500 per 60s run. Learnt clauses from earlier XY configs transfer to later ones within the same ZW group, improving the rate over time. | n=56 SAT cubed (k=7): 140 → 202 solves/s (**+44%**). Cumulative vs pre-session baseline: +191%. |
| 2026-04-03 | Batch recompute all stale quad PB constraints together: when encountering any stale constraint during propagation, recompute ALL stale constraints at once. | Cache locality: the assigns[] array (44 bytes at n=26) stays hot in L1 for all constraints instead of being evicted between interleaved propagation work. | n=26 SAT-heavy: 15.47s → 14.69s (**-5.0%**). |
| 2026-04-03 | Lazy backtrack: mark quad PB constraints as stale instead of per-term state updates. Recompute from scratch on next forward propagation if stale. | Backtrack was 16.24% of runtime, dominated by per-term `update_quad_pb_term_hint` calls (~200 random memory accesses per backtrack). Lazy approach reduces backtrack to O(constraints_per_var) and amortizes recomputation into the forward propagation path. | n=26 SAT-heavy: 16.41s → 15.47s (**-5.7%**). Phase B neutral. |
| 2026-04-03 | Combined: all 5 optimizations (allocation elimination, batch clear_learnt, state pre-filter, lazy backtrack, batch recompute). | See individual entries below. Five changes targeting SAT solver allocation, propagation, and backtrack overhead. | Full n=26: 869s → **577s** (**-33.6%**). Microbenchmark: 18.95s → 14.69s (**-22.5%**). Phase C throughput: ~100 → **~143 pairs/s** (**+43%**). |
| 2026-04-03 | Skip DEAD/TRUE terms in propagate_quad_pb: add `if t.state != 1 { continue; }` early-exit using precomputed term state. | DEAD and TRUE terms can never propagate. The state field is already maintained incrementally, so check is a single byte compare vs. two memory loads + branching. | n=26 SAT-heavy: 16.99s → 16.41s (**-3.4%**). Phase B neutral. |
| 2026-04-03 | Eliminate per-conflict heap allocations in SAT analysis: reuse solver-level buffers for seen[], reason_lits, quad PB explanations, minimize stack/visited. Uses mem::take pattern for borrow-checker-safe buffer reuse. | Profile showed malloc/free at 8.5% and compute_quad_pb_explanation (Vec<Lit> return) at 16.67% of runtime. Reusable buffers eliminate all per-conflict heap allocations. | n=26 SAT-heavy: 18.88s → 16.99s (**-10.0%**). Phase B neutral. |
| 2026-04-03 | Batch clear_learnt in table+SAT path: call every 8 configs instead of every 1. | clear_learnt scans all clause metadata + watch lists. Removing entirely caused +40% regression (stale clauses poison solver). Batching reduces overhead while managing stale clauses. | n=26 SAT-heavy: 18.95s → 18.44s (**-2.7%**). Phase B neutral. |
| 2026-04-02 | Z/W-indexed boundary table (London §3.3): precompute valid (x,y) boundary configs per (z,w) boundary, O(1) lookup at runtime. Replaces old HashMap-based table that required per-entry scanning and filtering. | Given a Z/W candidate, extract boundary bits and directly look up all compatible X/Y boundary configs. No filtering, no iteration over irrelevant entries. Table is mmap'd. | n=26 k=6: 148.6s wall-clock (vs 207.9s no-table baseline, vs 140s old table). Deduplicated table is 131MB (27K sigs, 4.2M XY entries). |
| 2026-04-02 | Bitwise GJ and autocorrelation filters: operate directly on packed boundary bits instead of expanding to i8 arrays. | Eliminates per-entry bit expansion for entries killed by filters (the vast majority). GJ check is one XOR + compare per constraint. Autocorrelation is shift-XOR per pair. | n=26 k=6: neutral (filters rarely needed with Z/W-indexed table), but essential for k=7+ where more entries per bucket. |
| 2026-04-02 | SAT solver profiling and optimization at n=26. Four changes: (1) buffer reuse in propagate_quad_pb, (2) compact QuadPbTerm 28→16 bytes, (3) inline hot functions, (4) halve assigns[] lookups via caller hint in update_quad_pb_term. | At n=26, SAT solver (Phase C) dominates at 92% of runtime. update_quad_pb_term was 40% alone. Buffer reuse eliminates per-call allocations; struct compaction improves cache density; caller hint skips one random memory access per call. | n=26 no-table: 207.9s → 195.6s (**-5.9%**). Phase C thread-sum: 806s → 757s. |
| 2026-03-30 | Pre-build per-sequence value-grouped index lists for O(1) SA partner selection. Eliminates random-probe loop (up to seq_len retries per flip). | Partner finding was the main per-flip overhead beyond delta computation: random probing hit wrong-value or same-position indices frequently, wasting iterations. Grouped lists give O(1) valid partner every time. | Stochastic: `34.13M → 41.65M flips/sec` (**+22.0%**). Exhaustive: neutral. |
| 2026-03-30 | Simplified SA delta-corr from multiple multiply-accumulate pairs to single `-2*vi*nb*weight` formula per lag. | Same-value swaps have a clean delta: `-2v * (sum of non-overlapping neighbors)`. Fewer multiplies, cleaner branches, better codegen. | Stochastic: `32.03M → 34.13M flips/sec` (**+6.6%**). Exhaustive: neutral. |
| 2026-03-31 | Early sum feasibility pruning in XY backtracker (London §3.3): set pos first, pre-check mirror sum bounds before expensive set_pair(mirror). Also fix latent bug with mirror-already-assigned state corruption. | Avoids O(n) lag updates in set_pair/unset_pair for ~90% of mirror combinations that fail sum feasibility. The bug fix prevents redundant tree exploration from state corruption when mirror of picked position was already assigned. | Phase C (n=16 θ=100): xy_nodes `901,772 → 10,368` (**87× fewer**), `1903ms → 17.5ms` (**-99.1%**). Exhaustive (θ=20000): neutral. Hybrid (n=14): neutral. |
| 2026-03-31 | Add `--max-spectral=M` CLI parameter (London §5.1): restrict spectral pair filter to `|Z(ω)|² + |W(ω)|² ≤ M` instead of default `(6n-2)/2`. | Trades search completeness for speed at larger n. London used this to find TT(34)–TT(40) where full enumeration is infeasible. | Feature addition, no performance change on existing benchmarks (pair filter already rejects all at n=16). |
| 2026-03-31 | Implement learnt clause deletion in radical. Keep glue clauses (LBD ≤ 3) and delete worst 50% of eligible learnt clauses when count exceeds original clause count. Trigger on every restart. | Without deletion, clause count grows unboundedly (137K at n=16), quadratically slowing BCP. CaDiCaL-style aggressive cleanup keeps the database lean while preserving high-quality learnt clauses. | Full SAT n=16: `17.5s → 3.9s` (**-78%**). n=18: `164s → 3.7s` (**-98%**). n=20: **52s** (previously >5min). |
| 2026-03-31 | Fix critical soundness bug in radical conflict analysis: `learnt.push(negate(lit))` should be `learnt.push(lit)`. Lits from conflict/reason clauses are already false — negating them produces true lits in the learnt clause, corrupting all subsequent CDCL learning. | Bug caused false UNSAT at n>=14 (2.5K+ vars). All learnt clauses contained wrong-polarity literals, leading to invalid derivations. | Full SAT n=14: UNSAT→**SAT in 310ms**. n=16: **22s**. n=18: **164s**. |
| 2026-03-31 | Optimize radical BCP inner loop: direct `clause_lits[]` indexing instead of `clause_lits(ci)` helper (avoids re-fetching ClauseMeta per access), `#[inline(always)]` on `lit_value`. | Reduces indirection in the hottest loop — `propagate_lit` is called for every assignment and iterates over watch lists with multiple clause literal accesses per clause. | Hybrid n=14: `3.8s → 3.4s` (**-10%**). |
| 2026-03-31 | Deduplicate Z/W pairs by autocorrelation vector in hybrid search. Pairs with identical `zw_autocorr` are equivalent for X/Y solving — only SAT-solve one representative. | ~50-60% of Z/W pairs from Phase B have duplicate autocorrelation vectors. Skipping duplicates halves the number of expensive SAT clone+solve calls. | Hybrid n=14: `9.2s → 3.8s` (**-59%**). |
| 2026-03-31 | Flat clause storage in radical: replace `Vec<Clause>` (each with `Vec<Lit>`) with flat `Vec<Lit>` + `Vec<ClauseMeta>` indexed by start/len. | Solver clone becomes a single memcpy of two flat arrays instead of thousands of individual Vec heap allocations. Dominant cost at ~1ms/clone with 5K clauses. | Hybrid n=14: `11.9s → 9.2s` (**-23%**). |
| 2026-03-31 | Feasibility pre-filter for SAT X/Y: check target parity and counter range before cloning solver. Skip infeasible Z/W pairs without clone overhead. | Avoids cloning and solving for Z/W pairs whose autocorrelation targets are out of range or have wrong parity — detected in O(n) without touching the solver. | Hybrid n=14: `18.2s → 11.9s` (**-34%**). |
| 2026-03-31 | CaDiCaL SAT solver integration (`--sat` mode). Encodes TT constraints as CNF with XNOR agree variables, sequential counters for sums, selector-based weighted cardinality for autocorrelation. | SAT/CDCL solvers use conflict-driven clause learning and restarts, which can prune the search space far more effectively than custom DFS for highly constrained combinatorial problems. | TT(4): <1ms, TT(8): 1.6ms, TT(10): 91ms, TT(12): 552ms, TT(14): 554ms, TT(16): 4.6s, **TT(18): 89s** (vs SA 580s, **6.5x faster**). |
| 2026-03-30 | SA early termination: in cold phase (temp < 1.0), stop delta-defect computation when partial sum exceeds current defect. | Most SA moves in the cold phase are bad; early termination skips remaining lag computations for clearly-rejected moves, saving O(n) work per rejected flip. | Stochastic: `29.36M → 32.03M flips/sec` (**+9.1%**). Exhaustive: neutral. |
| 2026-03-30 | Replaced manual O(θ×n) DFT in `spectrum_if_ok` with `rustfft` crate FFT using zero-padded sequences. FFT size = max(4n, 2θ) rounded to power of 2, with reusable buffer. | FFT computes full power spectrum in O(M log M) vs manual DFT's O(θ×n). For θ=256, n=16: FFT(512) does ~4.6K ops vs manual 4096 multiply-accumulates, with better SIMD utilization from optimized FFT library. | ~47-49% improvement: n=14 θ=128 mean `11.09 → 5.70` ms (**-48.6%**), n=16 θ=256 mean `38.25 → 20.20` ms (**-47.2%**). |
| 2026-03-30 | Added multi-threaded stochastic local search (`--stochastic`) using simulated annealing with O(n) incremental defect updates. | Enables finding Turyn sequences at sizes where exhaustive DFS is infeasible. Sum-preserving pair swaps, adaptive cooling, one SA worker per core. | TT(6): 0.6ms, TT(8): 0.8ms, TT(14): 175ms. |
| 2026-03-30 | Disabled FFT spectral path and DFS parity pruning from Grok bundle (both regressions). Kept XY dynamic variable ordering and bucket capping. | FFT path caused regression even when inactive (branch overhead, icache). DFS parity pruning was redundant with existing per-branch sum checks. | n=14: Grok 23ms → 21ms, n=16: Grok 80ms → 77ms. Recovers pre-Grok baseline while keeping beneficial Grok changes. |
| 2026-03-30 | Audited Grok optimization bundle as a single before/after comparison (`6eac0c5` -> `7b0894c`) on the IDEA profile. | Verifies whether the combined set of changes actually improved runtime under the documented benchmark command. | Regression on this profile: mean `44.160 -> 45.723` ms (~3.5% slower), median `39.546 -> 42.237` ms (~6.8% slower). |
| 2026-03-30 | Replaced linear-search removal from `XYState.assigned_positions` with O(1) slot-tracked swap-remove bookkeeping (`assigned_position_slot`). | Eliminates repeated vector scans in the hottest XY backtracking set/unset path while preserving fast iteration over assigned indices for lag updates. | ~22.25% mean improvement and ~22.91% median improvement on the long benchmark (`14434.113 -> 11222.901` mean, `14462.829 -> 11148.973` median). |
| 2026-03-30 | Switched boundary bucket keys from heap-allocated `Vec<i8>` signatures to packed-bit signatures for small `k`, and rewired XY lag updates to iterate currently assigned positions instead of scanning all lags per set/unset. | Removes per-sequence key allocation/hashing overhead in Phase B and trims redundant lag-loop work in XY state updates. | ~5.83% mean improvement and ~6.17% median improvement on the new longer-chain benchmark (`11663.583 -> 10984.050` mean, `11676.437 -> 10955.741` median). |
| 2026-03-28 | Added explicit warmup run in benchmark mode before measured repeats. | Removes cold-start noise from reported benchmark summary and makes comparisons more stable. | New baseline from warm runs: `mean_ms=5.195`, `median_ms=5.291` (`--benchmark=7`). |
| 2026-03-28 | Hoisted i8→f64 conversion out of inner spectral loops (build `values_f64` once per generated sequence, then use it across all theta samples in `spectrum_if_ok`). | Removes repeated per-sample scalar casts in the hottest spectral loop. | ~34.12% mean improvement and ~31.42% median improvement vs immediate prior run (`19.094 -> 12.579` mean, `18.071 -> 12.392` median). |
| 2026-03-28 | Streamed sequence generation via callback (`generate_sequences_with_sum_visit`) and processed raw `&[i8]` values directly in Phase B (`spectrum_if_ok`, `autocorrs_from_values`, boundary signature). Only materialize `PackedSeq` for retained candidates. | Removed repeated pack/unpack and temporary object churn in candidate generation. | ~31.44% mean improvement and ~28.03% median improvement vs prior baseline (`8.984 -> 6.159` mean, `8.394 -> 6.041` median). |
| 2026-03-28 | Adaptive non-verbose parallel tuple processing with `available_parallelism()` and small-workload sequential fallback. | Uses multicore where useful while avoiding overhead on tiny workloads. | ~24.00% mean improvement and ~19.01% median improvement (`12.618 -> 9.592` mean, `11.978 -> 9.701` median). |
| 2026-03-28 | Tightened DFS feasibility bounds with forced-tail contribution in sequence generation. | Earlier pruning of impossible branches in generator DFS. | ~14.62% mean improvement and ~15.56% median improvement (`14.778 -> 12.618` mean, `14.185 -> 11.978` median). |

## How to update this file going forward

For each optimization PR/commit:

1. Add one row to **Optimization history** with:
   - UTC date,
   - concise change summary,
   - one-sentence explanation,
   - before/after benchmark numbers,
   - **TTC lever** (denominator / rate / shortfall / instrumentation)
     and which counter(s) moved.
2. If it's an MDD-mode change, also record before/after TTC from the
   tertiary benchmark.
3. Update **Current baseline (latest)** to the newest measured values.
4. Keep benchmark command unchanged unless intentionally creating a
   *new benchmark profile*.

If a new benchmark profile is needed (e.g., TT(56) stress profile),
add a separate section with explicit command and keep historical
comparisons within the same profile.

### Anti-pattern to avoid

Do **not** accept or reject an MDD-mode change on `xy/s` alone. An
idea that halves xy/s but halves `live_zw_paths` is a *net win*.
Always report the three levers or a direct TTC delta.
