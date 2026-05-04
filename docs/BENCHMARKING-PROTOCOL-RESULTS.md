# Test of the benchmarking protocol — May 2026

This is the practical write-up of running the protocol from
[`BENCHMARKING.md`](BENCHMARKING.md) on real previously-rejected
optimizations from [`IDEAS.md`](../IDEAS.md). The goal was to verify
whether the protocol can detect ~0.2% improvements that earlier ad-hoc
benchmarks missed.

**TL;DR**: The protocol is well-defined but the noise floor on this
particular environment (4-CPU shared VM, no turbo control, no isolated
cores) is ~0.9% per ABBA block — not the ~0.1% the protocol
optimistically targets. With 4 ABBA blocks (~5 min/candidate) we can
detect ~1.5% effects; reaching 0.2% sensitivity would require ~80
blocks (~90 min/candidate) which is infeasible to run for many
candidates in a session. The protocol's value here is as much
**honest uncertainty quantification** as raw sensitivity.

## Environment characterization

| | Value |
|---|---|
| CPU | Intel Xeon @ 2.10 GHz, 4 logical cores, shared VM |
| OS | Linux 6.18.5 |
| Pinning | `taskset -c 2 setarch -R` |
| Threads | `TURYN_THREADS=1` |
| Workload | `--n=18 --wz=apart --mdd-k=5 --conj-tuple --continue-after-sat` |
| Per-run time | ~16.8 s wall-clock |
| ABBA block time | ~67 s (4 runs + 2 warmups amortised) |

**A==A null test** (4 ABBA blocks, identical baseline binary on both
sides):

```
mean ΔB-A = -0.300%   (negative = B faster)
sd        = 0.883%      (per-block)
95% CI    = [-1.705%, +1.105%]
verdict   = noise (B faster, but well within noise)
```

So the **measurement noise floor** is ~0.9% per block. To resolve a
0.2% true effect with 95/80 power you need ~80 paired blocks. This is
the headline limitation: 0.2% is below the floor on this hardware
without a different metric (HW counters, deterministic internal
counters, etc.), and those alternatives don't apply cleanly here
because the workload itself has timing-dependent dispatching that makes
counters non-deterministic across runs (XY-stage solve count varies
~2% even single-thread).

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
slightly (in `sol` count, not `solves`). The XY stage varies
substantially. Without instrumenting the binary, we can't directly
attribute work to the per-stage SAT solvers.

This means: **deterministic-counter-as-metric is not generally
available for this workload.** The protocol's preferred low-noise
strategy ("σ ≈ 0 deterministic counters") doesn't apply here. Wall-
clock with paired ABBA is the best we have.

## Candidates tested (all from `radical/src/lib.rs`)

All five candidates are micro-hoist patterns: pull a `&self.field`
borrow out of a hot inner loop so the compiler doesn't reindex through
`self` on every iteration. They each target a function that
`OPTIMIZATION_LOG.md` and the round-1/round-2 `IDEAS.md` profiles
identified as ≥1% of solver runtime:

| ID | Function | Profile share | Hypothesis |
|---|---|---|---|
| **C1** | `recompute_quad_pb` | ~12% | Hoist `assigns` slice and `qc` &mut out of term loop |
| **C2** | `propagate_lit` watch loop | ~10% | Single load of `clause_meta[ci]` (was loaded twice; once for `.deleted`, once into `m`) |
| **C3** | `propagate_quad_pb` | ~3% | Hoist `qc` borrow; split scan / enqueue phases |
| **C4** | `compute_quad_pb_explanation_into` | ~8% | Hoist `assigns` / `trail_pos` / `level` slices |
| **C5** | `backtrack`'s quad-PB stale loop | ~1.4% | Hoist `quad_pb_var_watches[v]` slice |
| **C_all** | C1+C3+C4+C5 stacked | sum ~24% | Test compounding |

All five were originally rejected as "within noise" in
`OPTIMIZATION_LOG.md` Round 1/Round 2. C2 corresponds roughly to R6
(the swap was unsafe, but combining the two loads is strictly safe
and equivalent for the slow path). Sanity check: all candidates produce
**bit-identical W-stage counters** to baseline (`flow W: unsat=702
sol=463918 spec_fail=305276 spec_pass=141902`), confirming algorithmic
equivalence.

## Results

(Filled in by `paired-stats.py` from `/tmp/turyn.{C1..C_all}.tsv`.)

```
TBD — see appendix.
```

## What the protocol caught vs missed

**Caught**: TBD.

**Missed (effect below floor)**: TBD.

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

1. Run the protocol on a quieter machine (dedicated, no SMT, frequency
   locked) where σ should drop to 0.2–0.4% per block.
2. Add deterministic per-stage counters to the binary so SAT solver
   work can be measured directly without wall-clock.
3. Build the radical/ crate with `RUSTFLAGS=-Zinstrument-coverage`
   semantics or a perf-counter wrapper to count instructions retired.

## Methodological lessons learned

* **ABBA counterbalancing matters.** Initial naive A→B per-pair runs
  showed -0.74% mean delta on A==A — second-position runs were
  systematically 1% faster (cache-warming bias). Switching to ABBA
  blocks dropped the A==A mean to -0.30% and cut the σ.

* **Watch your processes.** Running `pkill -f bench-pair` failed to
  kill duplicates because the script forks subshells; needed `kill -9`
  on the actual turyn PID. Two simultaneous benches sharing core 2
  silently doubled runtimes for one pass and threw off the timing
  for the other.

* **`--bench-cover-log2` event-driven cancel adds ~2% noise.** Even
  single-threaded, the cancel fires on event-arrival timing, so
  XY-stage count varies. Using `--continue-after-sat` (run to natural
  completion) was strictly more deterministic than `--bench-cover-log2`
  for this workload.

* **The harness scripts are now the documented standard.**
  `scripts/bench-pair.sh` (ABBA blocks) and `scripts/paired-stats.py`
  (paired-t with t-table) live in the repo and are wired into
  `BENCHMARKING.md`'s TL;DR.
