# Queue-theory view of TTC

A retrospective on why the TTC ("time to cover") metric was unreliable
at n ≥ 20 in earlier measurements, what fixed it, and what's still
fragile. The framing throughout is queue-theoretic: the search is a
multi-server queue draining a fixed-size workload, and TTC is a Little's-
Law-style estimate of remaining time.

## 1. The basic model

The MDD pipeline is:

```
seed_boundaries (1.4 M of them at n=26 mdd-k=7)
       │
       ▼
  ┌───────────────┐
  │ priority queue │  ← gold-then-work scheduler
  └───────────────┘
       │
       ▼ workers pull
  ┌─────────────────┐
  │  4 worker threads│  → run SolveW → SolveZ → SolveXY
  └─────────────────┘
       │ each completes
       ▼
  covered_mass += weight[i] / total_weight
```

Each boundary is a job. Jobs have wildly different service times —
service time is dominated by SAT solver work, and a single boundary
can span anywhere from microseconds (immediate UNSAT on spectral
filter) to minutes (long XY enumeration). The published metric is

```
TTC = (1 − covered_mass) × elapsed / covered_mass
    = remaining_mass / rate         where rate = covered_mass / elapsed
```

This is a Little's-Law-style projection: assume the rate observed so
far continues, and tell me how much more elapsed time I need.

## 2. Why the original metric drifted

Three independent queue effects, all violating the "stationary rate"
assumption:

### 2.1 Bias from uniform job weighting

Originally `covered_mass = boundaries_done / total_boundaries`. Every
boundary contributed `1/N` regardless of actual work content. Two
boundaries that take 1 µs and 100 ms credit the same fraction. The
priority queue — by design — dispatches cheap-looking work first
(spectral-prefilter passes, small `|σ_W|` shells), so the early rate
samples *systematically over-represent* fast jobs. As the queue's
fast lane drains, average service time climbs, observed rate falls,
and TTC has to climb to match. That's the classic "TTC drifts upward"
pattern we saw at n=22: 2.6 k → 4.7 k over the run, with no actual
slowdown — just sample composition changing.

The fix is to weight each job by its real share of the workload. We
changed `covered_mass` to a Σ over completed boundaries of `weight[i]
/ total_weight`, where `weight[i]` is each boundary's live XY-path
count from the MDD. Now the early-cheap-first priority no longer
biases the rate estimator; cheap boundaries credit small mass, and
the rate stays statistically stationary.

### 2.2 Variance from low job count

At low `covered_mass` the metric is the ratio of two small noisy
quantities. Specifically, when `covered_mass = ε`, TTC ≈ elapsed / ε,
so a 10% wobble in ε is a 10% wobble in TTC. With weights, individual
job completions have variance proportional to `weight_i / total_weight`,
which can be ~1/100 for a single heavy boundary. So at coverage
< 0.05, TTC swings by Θ(1) on every completion.

The cure isn't a metric change — it's running long enough that the
law of large numbers takes hold. Empirically: TTC becomes stable once
`covered_mass > 0.5` (10 %), and within ~7% of truth above that.
Below ~0.25, expect Θ(2x) wobble.

### 2.3 Two non-stationary regimes

Even with weights and enough samples, two known sources of bias remain:

* **Cheap-first priority bias** at the *tail*: the priority queue
  saves expensive work for last (because the cheap stuff already ran).
  So in the last third of a run, rate slows further than the early
  trajectory predicted, and TTC over-estimates by ~20–30 %. Visible
  in the n=18 ground-truth trace: covered=0.730 at t=17, predicting
  +6.3 s remaining, actual remaining was 0.9 s.
* **Partial-credit floor** at the *head*: while no boundary has
  completed yet, `covered_mass` consists entirely of XY-timeout
  partial credit — the SAT solver reporting "I eliminated 30 % of
  this sub-cube before the conflict budget hit." That credit caps at
  `1.0 × weight[i]` per boundary and is bounded above by
  `Σ live_partial_weight`. Once it saturates, additional elapsed time
  *cannot* increase covered_mass until a boundary actually closes.
  TTC then divides "remaining ≈ 1" by "rate ≈ saturated_partial /
  elapsed" → TTC grows linearly in elapsed. **This is the broken
  regime at n ≥ 24** with default settings: covered stays at 0.000
  forever and TTC just reports `elapsed × scale_factor`.

## 3. Sources of variance, ranked

When the same problem runs twice with different TTCs, the candidate
explanations in order:

1. **Thread scheduling.** Multi-worker queue dispatch is non-
   deterministic. Two runs see different early job mixes → different
   early rates → different TTC trajectories. **Dominant variance source.**
   Pin with `TURYN_THREADS=1`.
2. **LCG path order.** The boundary walker picks a permutation of
   path positions via an LCG. Already deterministic in current code
   (`mdd_stages.rs:1089`, seed `0xDEADBEEF_CAFEBABE`).
3. **Priority-queue tiebreaker.** Items with equal priority are
   pulled in arrival order, which can vary with thread interleaving.
4. **Boundary weight skew.** Heavy boundaries credit big jumps;
   landing on one early vs late changes the trajectory. The weighted
   change *amplifies* this per-event variance (each event weighs
   more) but reduces *bias*. The variance washes out at large N;
   the bias does not.
5. **SAT solver's internal randomness.** Already pinned via the LCG.

In our final calibrated config (`TURYN_THREADS=1` + everything else
default), 5 runs at n=16/n=18 conj-tuple agree within 3 %. That's the
floor for run-to-run variance under the current scheduler.

## 4. Why "consistency" and "accuracy" are different metrics

A measurement can be:

|             | accurate          | inaccurate (biased) |
|-------------|-------------------|---------------------|
| consistent  | ✓ goal            | "broken clock"      |
| inconsistent | "honest noise"   | "broken metric"     |

Uniform-weight TTC under multi-threading was inconsistent **and**
biased — a broken metric. Uniform-weight TTC under single-threading
was consistent but biased — a broken clock that happens to give a
useful relative comparison if you stop optimizing things that change
the bias. Weighted TTC under single-threading is consistent and
unbiased once `covered_mass > 0.5`, the only regime where it can be
checked against ground truth.

The right benchmark goal for TT(56) is therefore: get to a regime
where `covered_mass > 0.5`. That doesn't necessarily mean covering
half the search space — `--conj-tuple` restricts the space so the
covered fraction ramps faster. We verified this at n=18 conj-tuple
(ran to covered=1.0 in 18 s) and n=22 conj-tuple (still running as of
this writing, expected ~20 min).

## 5. Why the TT(56) probe was uninformative

At TT(56) with default settings, no single boundary completes within
~150 s of observation. So `covered_exact = 0` throughout, and the
only signal is in-flight partial credit, which saturates per-boundary
at `weight_i × 1.0`. The metric is in the "broken" regime described
in §2.3. The numbers it reports (12 d, 26 d, etc.) are dominated by
how the partial-credit denominator interacts with elapsed time, not
by any actual rate measurement.

For meaningful TT(56) numbers we need either (a) hours of observation
so that boundaries do close, (b) a stronger conjecture restriction
like `--conj-tuple --conj-zw-bound`, or (c) a separate
throughput-based estimator that doesn't depend on `covered_mass`.

## 6. The right benchmark recipe

Given everything above, the calibrated benchmark configuration for
turyn is:

```bash
TURYN_THREADS=1 target/release/turyn \
    --n=<N> --wz=apart --mdd-k=<K> \
    --conj-tuple \                    # restrict to one tuple shell
    --continue-after-sat \            # don't stop on first solution
    --sat-secs=<budget>
```

This is the only configuration where TTC has been verified to
predict ground truth within ~10 %. Anything with multiple threads,
without `--continue-after-sat`, or in the partial-credit-only regime
should be treated as "we don't know yet."

## 7. Open queue-theory questions

* The cheap-first priority bias (+20–30 % overestimate at >70 %
  covered) is fixable by either re-ordering the queue to interleave
  cheap and expensive (round-robin by weight) or by smoothing the
  rate via EWMA so the late-run slowdown gets predicted earlier.
* Multi-threaded determinism would require a deterministic worker→
  job assignment, e.g. partition the boundary list mod N_threads
  rather than using a shared queue. Cost: less load balancing.
* The partial-credit-only regime at large n is a structural blind
  spot of the metric. The framework's `bench_target_reached` flag
  helps bound the runtime but not the metric's reliability —
  `--bench-cover-log2=X` will trigger as soon as
  `total_log2 + log2(covered) ≥ X`, even if `covered` is just
  partial-credit noise. Need a separate "real coverage seen yet?"
  gate before publishing TTC, or report `Projected` instead of
  `Hybrid` until then.

## 8. References

- `docs/TTC.md` — the normative spec for TTC (`Direct`/`Hybrid`/
  `Projected` quality labels, additivity invariants, etc).
- `docs/TTC-CALIBRATION.md` — empirical recipe + ground-truth at
  n=16/n=18.
- `docs/TTC-ACCURACY-MEASUREMENT.md` — the original "everything is
  broken" investigation across all four `--wz` modes.
- `docs/ttc-runs-v2/` — verified ground-truth traces.
- `docs/ttc-runs/` — pre-calibration traces showing the broken regime.
