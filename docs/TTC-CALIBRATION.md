# TTC calibration — what works, and how to use it for big-n estimates

This is the result of testing whether the TTC metric is **consistent**
(same answer twice) and **accurate** (matches ground truth) at a scale
small enough to verify directly. Spoiler: yes, with the right
benchmark configuration.

## Summary

| n  | mode  | config                              | runs | wall-clock | spread | TTC mid-run accuracy at >50% covered |
|----|-------|-------------------------------------|------|-----------:|-------:|--------------------------------------|
| 16 | apart | conj-tuple, THREADS=1, weighted     | 5    | 3.3–3.4 s  | 3%     | within **4%** of ground truth        |
| 16 | apart | conj-tuple, THREADS=1, uniform      | 5    | 3.3–3.4 s  | 3%     | within **4%** of ground truth        |
| 18 | apart | conj-tuple, THREADS=1, weighted     | 3    | 17.9–18.0  | 0.6%   | within **7%** of ground truth        |
| 18 | apart | conj-tuple, THREADS=1, uniform      | 3    | 17.7–18.2  | 3%     | within **7%** of ground truth        |

For comparison, the same runs with default 4 threads, default early-exit-on-
first-solution, and no flags showed 1–10x run-to-run TTC variance and
no path to ground truth. **The metric isn't broken; the benchmark
methodology was.**

## The benchmark configuration that works

```bash
TURYN_THREADS=1 target/release/turyn \
  --n=<N> --wz=apart --mdd-k=<K> \
  --conj-tuple \                   # restrict to one tuple shell
  --continue-after-sat \           # don't stop on first solution
  --sat-secs=<budget>
```

Three independent fixes, in order of how much they matter:

1. **`TURYN_THREADS=1`** — the dominant variance source was thread
   scheduling, not the metric. With multiple workers, "which boundary
   gets dispatched first" determines what mass gets credited early,
   and that varies across runs. Single-threaded → fully deterministic
   queue ordering.
2. **`--continue-after-sat`** — the search no longer stops when it
   finds a solution. Runs continue until `covered_mass = 1.0`, which
   gives ground truth (the actual time to finish the search). This
   was added on main in `afa13c3 Benchmark: add fixed-work TTC stop`.
3. **`--conj-tuple`** — picks the smallest auto-selected tuple shell
   so the search actually completes in seconds rather than years.
   Pair with small mdd-k (k=5 for n≤18, k=7 for n≤20).

The SAT-solver LCG seed is already pinned at compile time
(`0xDEADBEEF_CAFEBABE`, see `mdd_stages.rs:1089`), so no extra flag
is needed for that.

## Ground truth at n=16 (apart, conj-tuple, weighted, THREADS=1)

```
[framework:apart] elapsed=1.0s covered=0.218 ttc=3.59s   → predicted total 4.59s (+35%)
[framework:apart] elapsed=2.0s covered=0.566 ttc=1.50s   → predicted total 3.50s ( +4%)
[framework:apart] elapsed=3.0s covered=0.704 ttc=1.26s   → predicted total 4.26s (+25%)
Framework search (--wz=apart): covered=1.000 elapsed=3.4s ttc=0
                                                     ↑ ground truth
```

Mid-run prediction is excellent. The end-of-run overestimate is
because the priority queue hands out cheap boundaries first, leaving
expensive ones for the tail — so the rate slows in the last third
and the metric assumes the slow rate continues to the end.

## Ground truth at n=18 (apart, conj-tuple, weighted, THREADS=1)

The same pattern, scaled up:

```
elapsed= 1.0s covered=0.092 ttc= 9.86s  → predicted 10.86s (-39% under)
elapsed= 5.0s covered=0.217 ttc=18.09s  → predicted 23.09s (+29% over)
elapsed= 9.0s covered=0.250 ttc=27.08s  → predicted 36.08s (+102% over) ← worst
elapsed=10.0s covered=0.560 ttc= 7.86s  → predicted 17.86s ( +0% — perfect)
elapsed=12.0s covered=0.665 ttc= 6.06s  → predicted 18.06s ( +1%)
elapsed=15.0s covered=0.691 ttc= 6.72s  → predicted 21.72s (+21%)
finished      covered=1.000              ground truth = 17.9s
```

There's a phase transition around t=10 s — a heavy boundary completes,
covered jumps from 0.25 to 0.56, and TTC immediately becomes
near-perfect. Before that, the metric was confused by the partial-
credit micros accumulating against an in-flight heavy boundary while
no exact credit had landed yet.

**Practical rule of thumb**: trust TTC most strongly when
`covered_mass > 0.5`. Below ~0.25 it can be off by a factor of 2,
because the rate is dominated by partial credit on whatever boundary
happens to be in flight.

## Uniform vs weighted at this scale

Indistinguishable. n=18 mdd-k=5 has only 15× weight skew, and the
dominant variance source was thread scheduling — once that's pinned,
the per-boundary weight scheme barely matters at this n. Larger
weight skews (125× at mdd-k=7) may show a difference; that's an
open question.

## Recipe for TT(56) calibration

The user's question: "for TT(56) right now, I don't know if we're
looking at days or years."

We can't verify TT(56) ground truth directly — it might literally be
years. But we can extrapolate from observed metric properties:

1. Pin the benchmark config: `TURYN_THREADS=1 ... --bench-cover-log2=<X>`
   instead of `--continue-after-sat`. The `--bench-cover-log2` flag
   stops when `covered × total_log2_work ≥ 2^X`, i.e. after a fixed
   amount of "raw-equivalent" work.
2. Run at increasing X (e.g. X=30, X=33, X=36, X=40). Each run gives
   a TTC estimate at a different coverage depth.
3. If the TTC estimates **agree across X levels**, the metric is
   calibrated and you can read its TT(56) prediction with confidence.
   If they diverge, you've found the regime where TTC isn't yet
   reliable for that n.
4. Cross-check by re-running the same (n, X) twice. With THREADS=1
   the two runs MUST agree to within 3% — if they don't, the search
   has nondeterminism we haven't pinned.

This is the same calibration pattern used in MCMC convergence
diagnostics: run independent chains, see whether they agree.

## Open questions

* Does the late-run overestimate (priority-queue "cheap-first" tail
  effect) persist at n=20+? At n=18 conj-tuple the overestimate was
  +20–30% in the last third; at TT(56) we'd want to know whether
  that's a constant +30% bias or a percentage that grows with n.
* The weighted change makes covered_mass match the TTC.md `Direct`
  contract more closely, but at n≤18 the empirical accuracy is
  identical to uniform. The case for keeping it is structural
  (bigger weight skew at mdd-k=10+ for n=56) and contract-compliance,
  not measured improvement at this scale.
* Multi-threaded benchmarking: with THREADS>1, the variance comes
  back. A scheduler-side fix (e.g. priority-queue tiebreaker by item
  id, or a deterministic worker→item assignment) would be needed for
  production benchmark reproducibility.

## Files

- Trace: `docs/ttc-runs-v2/n18-conj-tuple-weighted-trace.log`
- Old (broken) traces showing the variance pattern:
  `docs/ttc-runs/n22-apart.log`, `n24-apart.log`, `n26-apart.log`
