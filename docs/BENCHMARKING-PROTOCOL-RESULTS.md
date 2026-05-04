# Test of the benchmarking protocol — May 2026

This is the practical write-up of running the protocol from
[`BENCHMARKING.md`](BENCHMARKING.md) on real previously-rejected
optimizations from [`IDEAS.md`](../IDEAS.md). The goal was to verify
whether the protocol can detect ~0.2% improvements that earlier ad-hoc
benchmarks missed.

**TL;DR**:

* **No candidate was confirmed as a real win** after the full
  protocol (4-block screen → 8/12-block confirmation in clean
  conditions). C4 looked significant at 4 blocks (mean -1.23%,
  t=-4.61, 95% CI excludes 0) but the clean 8-block re-run gave
  +0.59% with 6/2 sign favoring regression — a Type I false
  positive. Initial commit `8051f3e` was reverted in `c8d2e8d`.
* The strict 0.2% sensitivity claim from `BENCHMARKING.md` is **not
  achievable on this hardware**. The per-ABBA-block σ on this 4-CPU
  shared VM is ~1.0–2.4% (vs the 0.1–0.5% the doc assumed); reaching
  0.2% requires either ~80 blocks per candidate (~90 min) or a
  quieter machine.
* **Most important finding**: 4-block ABBA screens lie. With df=3 the
  paired-t critical value is 3.18, but the per-block sd estimated
  from 4 samples (~0.5%) under-counts the true sd seen at 8+ blocks
  (~1.1%). A "significant" 4-block result with t=-4.6 routinely
  fails to replicate. **Minimum 8 blocks before declaring any win,
  with 12+ for anything below 1%.** This is the protocol's most
  valuable contribution: it caught a false positive that ad-hoc
  benchmarks would have shipped.
* All five candidates (C1–C5, plus C_all) sit within ±1% on this
  hardware. Whether any of them is a real ≤0.5% win is unknown:
  measuring 0.5% with σ=1% per block needs ~30 blocks (~35 min) per
  candidate, and 0.2% needs ~80 blocks (~90 min). Future work.

## Environment characterization

| | Value |
|---|---|
| CPU | Intel Xeon @ 2.10 GHz, 4 logical cores, shared VM |
| OS | Linux 6.18.5 |
| Pinning | `taskset -c 2 setarch -R` |
| Threads | `TURYN_THREADS=1` |
| Workload | `--n=18 --wz=apart --mdd-k=5 --conj-tuple --continue-after-sat` |
| Per-run time | ~16.8 s wall-clock |
| ABBA block time | ~67 s (4 runs amortised) |

**A==A null test** (4 ABBA blocks, identical baseline binary on both
sides):

```
mean ΔB-A = -0.300%
sd        =  0.883%   per-block
95% CI    = [-1.705%, +1.105%]
verdict   = noise (well within CI)
```

So the **measurement noise floor** is ~0.9% per block. To resolve a
true 0.2% effect with 95/80 power you need ~80 paired blocks. This is
the headline limitation: 0.2% is below the floor on this hardware
without a different metric (HW counters, deterministic internal
counters), and those alternatives don't apply cleanly here because the
workload itself has timing-dependent dispatching that makes per-stage
counters non-deterministic across runs (XY-stage solve count varies
~1–2% even single-thread).

## Counter determinism — what is and isn't deterministic

Single-thread, fixed seed, `--continue-after-sat`, identical binary,
five repetitions of n=18 conj-tuple:

| Counter | Determinism |
|---|---|
| `flow W: unsat / sol / spec_fail / spec_pass / solves` | **identical** across runs |
| `flow Z: solves` | **identical** |
| `flow Z: sol / unsat / pair_fail` | drifts within ~0.03% |
| `flow XY: stage_enter / solves / unsat / sat / ext_pruned` | drifts ~1–2% |
| Solutions found total | drifts (e.g. 11–18 across 6 runs) |

The W stage is fully deterministic in count. The Z stage varies very
slightly. The XY stage varies substantially. This means the protocol's
preferred low-noise strategy ("σ ≈ 0 deterministic counters") doesn't
apply here without source instrumentation. Wall-clock with paired
ABBA is the best metric we have.

## Candidates tested (all from `radical/src/lib.rs`)

All five candidates are micro-hoist patterns: pull a `&self.field`
borrow out of a hot inner loop so the compiler doesn't reindex through
`self` on every iteration. Each was originally rejected as "within
noise" in `IDEAS.md` round 1/round 2.

| ID | Function | Profile share | Hypothesis |
|---|---|---|---|
| **C1** | `recompute_quad_pb` | ~12% | Hoist `assigns` + `qc` &mut out of term loop |
| **C2** | `propagate_lit` watch loop | ~10% | Single load of `clause_meta[ci]` |
| **C3** | `propagate_quad_pb` | ~3% | Hoist `qc`; split scan / enqueue phases |
| **C4** | `compute_quad_pb_explanation_into` | ~8% | Hoist `assigns` / `trail_pos` / `level` |
| **C5** | `backtrack`'s quad-PB stale loop | ~1.4% | Hoist `quad_pb_var_watches[v]` |
| **C_all** | C1+C3+C4+C5 stacked | sum ~24% | Test compounding |

Sanity check: all candidates produce **bit-identical W-stage counters**
to baseline (`flow W: unsat=702 sol=463918 spec_fail=305276
spec_pass=141902`), confirming algorithmic equivalence; all 41 radical
unit tests pass.

## Results

n=18, single-thread, taskset core 2 (`scripts/bench-pair.sh`).
Initial 4-block screen, plus follow-ups for C4:

```
| Candidate     |   n |   mean Δ% |   sd% | 95% CI                 |   Δmin% | sign B</>A | verdict       |
|---------------|----:|----------:|------:|------------------------|--------:|-----------:|---------------|
| null (A=A)    |   4 |    -0.30% | 0.88% | [-1.70%, +1.10%]       |  -1.20% |        2/2 | noise         |
| C1            |   4 |    -0.24% | 0.97% | [-1.78%, +1.30%]       |  -0.32% |        3/1 | noise (hint+) |
| C2            |   4 |    +3.27% | 5.60% | [-5.64%, +12.17%]      |  +0.90% |        1/3 | noise (hint−) |
| C3            |   4 |    -0.83% | 1.21% | [-2.74%, +1.09%]       |  -1.47% |        3/1 | noise (hint+) |
| C4 screen     |   4 |    -1.23% | 0.53% | [-2.08%, -0.38%]       |  -0.89% |        4/0 | "SIG" (false) |
| C4 confirm-12 |  12 |    -0.53% | 2.38% | [-2.05%, +0.98%]       |  +0.62% |        6/6 | noise         |
| **C4 clean-8**|   8 |    +0.59% | 1.12% | [-0.35%, +1.53%]       |  -0.60% |        2/6 | noise (hint−) |
| C5            |   4 |    -0.21% | 0.41% | [-0.86%, +0.45%]       |  -0.56% |        2/2 | noise         |
| C_all         |   4 |    +0.45% | 4.11% | [-6.08%, +6.99%]       |  -2.30% |        3/1 | noise         |
```

### The C4 saga (the central lesson)

The 4-block screen on C4 was the most exciting result of the session:
4/4 sign, 95% CI excludes zero, t=-4.61 at df=3 (p<0.02). I committed
it as `8051f3e` and pushed.

Then two follow-up runs disagreed:

* **12-block confirmation** (early blocks contaminated by a parallel
  bench I'd launched on a sibling core): mean +0.45%, 95% CI
  [-2.05%, +0.98%], 6/6 sign. Tied.
* **8-block clean re-run** (no parallel bench, fresh start):
  **mean +0.59%, 6/2 sign favors regression**. The opposite of the
  4-block screen.

The 4-block screen was a Type I false positive. **The estimated
sd from 4 samples (0.53%) was less than half the true sd seen at
8+ samples (1.12%).** With paired-t at df=3, even a t-stat of -4.6
isn't enough confidence — the underlying variance is being
underestimated by random chance.

Reverted in `c8d2e8d`. The candidate is most likely null or a
slight regression; either way, not worth committing.

### What this means for the rest of the candidates

C1, C3 (both -0.2 to -0.8% at 4 blocks) and C2 (+0.5–3% regression
at 4 blocks) are all in the same regime as C4: their 4-block
screens cannot be trusted. Promoting any of them without an 8+
block clean re-run would risk the same false-positive trap. Given
the noise floor, the honest summary is "no candidate has a
demonstrable wall-clock effect at this hardware's measurement
precision."

C_all's headline +0.45% mean is dominated by one outlier block
(block 4 at +6.5%, contaminated by the parallel C4-confirmation
bench I'd launched). Δmin and 3/1 sign both pointed to a possible
compound win, but given that C4 itself didn't replicate, the C_all
"compound" interpretation is unreliable — most of C_all's hint was
coming from C4's now-rejected effect.

C2 is the most plausible directional finding, but only weakly:
hypothesis (combine two `clause_meta[ci]` loads into one) added a
load to the common case (blocker-true ≈ 95% of clauses) for the
benefit of the rare case. Direction matches expectation but
magnitude is below detection at 4 blocks.

## Cost analysis: how many blocks for what sensitivity

Updated with the **true** per-block σ measured at 8+ blocks (1.12%
for C4 clean-8) rather than the optimistic 4-block estimate
(0.53%, which under-counted by 2×):

| Effect to detect | Required blocks | Wall time |
|---|---|---|
| 2.0% | 4 | 4.5 min |
| 1.0% | 12 | 14 min |
| 0.5% | 47 | 53 min |
| 0.3% | 130 | 2.5 hours |
| 0.2% | 290 | 5.5 hours |

This is roughly 2× higher than the 4-block-extrapolated estimates
in earlier drafts of this doc, because **4-block sd estimates
under-count true sd by ~2×.** Plan accordingly: a 4-block screen
is fine for filtering out garbage, but needs an 8+ block follow-
up before any "win" is committed.

Detection of 0.2% on this hardware with this metric is technically
possible but takes ~2.5 hours per candidate. For an iteration loop
that's untenable; the right move is one of:

1. Run the protocol on a quieter machine (dedicated, no SMT,
   frequency locked) where σ should drop to 0.2–0.4% per block.
2. Add deterministic per-stage counters to the binary so SAT solver
   work can be measured directly without wall-clock — e.g. expose
   the per-stage `sum_of(num_propagations) for all SAT calls in
   stage X` to stderr.
3. Wrap the search call in `perf stat -e instructions` (when perf is
   available) and use that as the metric instead of wall-clock.

## What this means for `BENCHMARKING.md`

The protocol document needs an update based on this dry-run. Most
of it is correct; the actionable changes:

1. **Drop the "4 blocks = decisive" framing.** The TL;DR script
   suggests "30 paired samples" as the default. Replace with:
   "≥8 blocks for any wall-clock win, ≥12 for sub-1% effects."
2. **Always confirm with a clean re-run** before committing. Two
   independent 8-block runs converging on the same direction are
   far more convincing than one t=-4.6 from 4 blocks.
3. **Don't run two benches in parallel.** I tried this for time
   savings; it added 3% per-block σ to both runs. Use one core,
   one bench at a time, even on a multi-core box.
4. **Use the per-block sd from past runs, not the current one,
   for sample-size planning.** If you've never benched on this
   machine before, do a 12-block A==A null first to estimate σ.
   The 4-block sd is too noisy to plan against.

Updated `docs/BENCHMARKING.md` ought to reflect these. (See
todo at end of doc.)

## Methodological lessons learned

* **ABBA counterbalancing matters.** Initial naive A→B per-pair runs
  showed -0.74% mean delta on A==A — second-position runs were
  systematically 1% faster (cache warming + frequency ramp). Switching
  to ABBA blocks (`A B B A`, mean within block) dropped the A==A mean
  to -0.30% and roughly halved σ.

* **Watch your processes.** Running `pkill -f bench-pair` failed to
  kill duplicates because the script forks subshells; `kill -9` on the
  actual turyn PID was required. Two simultaneous benches sharing
  core 2 silently doubled runtimes for one pass and threw off both.

* **Outliers happen.** C2 block 4 had one run at 20.7s (vs typical
  17s) — a system-level interruption. Mean was useless; min-of-runs
  and median-of-runs both told the right story. The protocol should
  always report min/median in addition to mean.

* **`--bench-cover-log2` event-driven cancel adds noise.** Even
  single-threaded, the cancel fires on event-arrival timing, so
  XY-stage count varies. Using `--continue-after-sat` (run to natural
  completion) was strictly more deterministic for this workload.

* **n=14 doesn't help.** Initial intuition was "smaller = faster
  iteration = more blocks per minute". In practice n=14 was 0.3 s
  per run, which made startup overhead variance (cpufreq state,
  cgroup throttling) the dominant noise term, and bench results
  bimodal. n=18 with full-coverage runs was the sweet spot for
  signal-to-noise.

* **Don't run two benches in parallel on the same machine.** I
  launched the 12-block C4 confirmation on core 3 while the C_all
  4-block bench was running on core 2, hoping for time savings.
  Both were taskset-pinned, but sharing L3 cache and memory bus
  added ~3% per-block σ to both. Block 4 of C_all jumped from
  ~17 s to 19–21 s while the parallel bench was hot. If you need
  to run multiple candidates, do them strictly sequentially, even
  on a multi-core box.

* **Pre-screening at 4 blocks then confirming at 12+ is the right
  workflow.** A 4-block screen takes ~5 min and surfaces clearly
  significant candidates (like C4) and clearly null ones; ambiguous
  ones get 12 blocks (~14 min). This burns ~25 min for a confirmed
  result, vs the multi-hour budget for naively running 100+ blocks
  on every candidate.

## Files

* `scripts/bench-pair.sh` — ABBA paired benchmark runner (n=18)
* `scripts/bench-n14.sh` — same for n=14 (tested, less useful here)
* `scripts/paired-stats.py` — paired-t with sign test and min/median
* `scripts/aggregate-results.py` — markdown summary table
* `scripts/run-all-candidates.sh` — sequential A vs B1, B2, ... batch
* Per-candidate raw data: `/tmp/c1.tsv`, `/tmp/turyn.{C2..C_all}.tsv`
  (not committed — regenerable in ~5 min/candidate)
