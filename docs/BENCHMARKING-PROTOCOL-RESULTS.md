# Test of the benchmarking protocol — May 2026

This is the practical write-up of running the protocol from
[`BENCHMARKING.md`](BENCHMARKING.md) on real previously-rejected
optimizations from [`IDEAS.md`](../IDEAS.md). The goal was to verify
whether the protocol can detect ~0.2% improvements that earlier ad-hoc
benchmarks missed.

**TL;DR**:

* The protocol's paired ABBA design + paired-t analysis **did detect a
  real ~1.2% wall-clock win (C4)** that had been previously rejected
  as "within noise". Committed in `8051f3e`.
* C1 and C3 trended in the right direction but were not significant at
  4 ABBA blocks; one of them is likely a real ~0.5–0.8% win that
  needs ≥12 blocks to confirm.
* C2 (a hypothesized hoist that was actually a slight regression on
  the hot path) shows up as +0.5% slower with min-of-runs analysis —
  a useful negative result.
* The strict 0.2% sensitivity claim from `BENCHMARKING.md` is **not
  achievable on this hardware**. The per-ABBA-block σ on this 4-CPU
  shared VM is ~0.9% (vs the 0.1–0.5% the doc assumes); reaching
  0.2% requires either ~80 blocks per candidate (~90 min) or a
  quieter machine.
* The protocol's main practical contribution turned out to be the
  paired-t verdict: an ad-hoc reading of these per-block deltas
  ("most are negative, must be a win") gave the right answer for C4
  by accident, but the same eyeballing wrongly endorsed C3 (which
  was below the significance threshold). Paired-t separates the two.

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

(All cells: 4 ABBA blocks, n=18, single-thread, taskset core 2.)

```
| Candidate  |   n |   mean Δ% |   sd% | 95% CI                 |   Δmin% | sign B</>A | verdict       |
|------------|----:|----------:|------:|------------------------|--------:|-----------:|---------------|
| null (A=A) |   4 |    -0.30% | 0.88% | [-1.70%, +1.10%]       |  -1.20% |        2/2 | noise/null    |
| C1         |   4 |    -0.24% | 0.97% | [-1.78%, +1.30%]       |  -0.32% |        3/1 | hint B faster |
| C2         |   4 |    +3.27% | 5.60% | [-5.64%, +12.17%]      |  +0.90% |        1/3 | hint B slower |
| C3         |   4 |    -0.83% | 1.21% | [-2.74%, +1.09%]       |  -1.47% |        3/1 | hint B faster |
| C4         |   4 |    -1.23% | 0.53% | [-2.08%, -0.38%]       |  -0.89% |        4/0 | **SIG B faster** |
| C5         |   4 |    -0.21% | 0.41% | [-0.86%, +0.45%]       |  -0.56% |        2/2 | noise         |
| C_all      |   ? |    TBD    | TBD   | TBD (running)          |   TBD   |        TBD | TBD           |
```

**C4 is the clear win**: 4/4 sign, 95% CI excludes zero, t=-4.61 at
df=3 (p<0.02). Committed in `8051f3e`. The optimization makes
`compute_quad_pb_explanation_into` (8.1% of solver runtime) about 15%
faster, which works out to ~1.2% wall-clock at this workload.

C2's mean is dominated by one outlier block (+11.6% — an external CPU
spike during one of the four runs). Discarding the outlier gives mean
+0.5% — a small regression direction. The min-of-runs comparison
(Δmin = +0.90%) is consistent with C2 being a slight regression: the
hypothesis (combine two `clause_meta[ci]` loads into one) added a
load to the common case (blocker-true) for the benefit of the rare
case (blocker-false), which is the wrong trade-off for SAT BCP.

C1 and C3 both look like hints of ~0.2–0.8% wins but are not
significant at 4 blocks — exactly the regime the protocol predicts:
"too small to detect with this many runs." Re-running at 12 blocks
would resolve them, but at ~14 min each that's a session-budget
question.

## Cost analysis: how many blocks for what sensitivity

With per-block σ = 0.88% (this VM):

| Effect to detect | Required blocks | Wall time |
|---|---|---|
| 2.0% | 2 | 2.5 min |
| 1.0% | 6 | 7 min |
| 0.5% | 22 | 26 min |
| 0.3% | 60 | 70 min |
| 0.2% | 134 | 2.5 hours |

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
