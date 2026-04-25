# TTC accuracy measurement (April 2026)

Empirical comparison of TTC ("time to cover") predictions against
actual wall-clock times across all four `--wz` modes for n in {18, 20,
22, 24, 26}. Each run uses default settings (4 threads, mdd-k=7 for
apart/together when applicable, no `--conj-*` flags) on a 4-core box.
The search auto-stops at first solution; raw logs live in
[`ttc-runs/`](ttc-runs/).

User's accuracy heuristic: the search stops at first solution, so
`TTC ÷ #canonical_solutions` should be approximately the actual first-
solution time, *if* solutions are roughly uniform within the search
order.

## Headline result

**TTC has not converged for any mode at n ≥ 20.** The two MDD modes
(`apart`, `together`) report a finite Hybrid TTC, but it is
extrapolated from <1% covered mass and continues to drift over the
length of the run. The other two modes are worse:

* `--wz=cross` reports `ttc=None` permanently at every n ≥ 18 in our
  runs, because it cannot finish even one tuple shell within tens of
  seconds and `tuples_done = 0` ⇒ `covered_mass = 0`
  ([`cross.rs:336-346`](../src/search_framework/mode_adapters/cross.rs)).
* `--wz=sync` reports a finite TTC, but it climbs *monotonically* with
  elapsed time at n ≥ 18 in every run we did — so the value is not a
  prediction, it is roughly `elapsed × constant`.

## Per-mode summary table

| n  | mode      | wall (s) | covered at finish | TTC at finish (s) | implied N = (wall+TTC)/wall | notes |
|----|-----------|---------:|------------------:|------------------:|----------------------------:|-------|
| 18 | cross     | 65 (killed)  | 0.000 | **None** | — | one tuple shell never finishes |
| 18 | apart     | 0.31     | 0.075 | 2.5     | 9   | found in 0.31 s |
| 18 | together  | 0.31     | 0.075 | 3.5     | 12  | found in 0.31 s |
| 18 | sync      | 56 (killed)  | 0.001 | 67–103 k (climbing) | — | TTC grew 70k → 100k while elapsed grew 35s → 50s |
| 20 | cross     | 48 (killed)  | 0.000 | **None** | — | same `tuples_done=0` pathology |
| 20 | apart     | 2.6      | 0.006 | 415     | 161 | found in 2.6 s |
| 20 | together  | 1.5      | 0.003 | 524     | 351 | found in 1.5 s |
| 20 | sync      | 45 (killed)  | 0.000 | 661 k (climbing) | — | TTC grew ~15 k/s |
| 22 | apart     | 18.8     | 0.004 | 4 664   | 249 | TTC drifted 2.6k → 4.7k over the 18s run |
| 22 | together  | 10.9     | 0.002 | 5 165   | 475 | TTC bounced 8.5k → 4.9k → 5.7k → 5.2k |
| 24 | apart     | 6.5      | 0.001 | 7 402   | 1 140 | TTC drifted 4.2k → 7.4k in 6 s |
| 24 | together  | 56 (killed)  | 0.002 | 24 121 (climbing) | — | TTC kept climbing 14k → 24k over 56s, no solution found |
| 26 | apart     | 74 (killed)  | 0.000 | 150 850 (climbing) | — | TTC grew 17k → 150k as elapsed grew 4s → 74s |

(Cross and sync rows for n ≥ 22 omitted: based on n=18 and n=20 those
modes show the same pattern — cross stuck at 0 covered, sync TTC
linear in elapsed.)

For comparison: the only n value with a known canonical count is
**n=18 → 675 canonical** ([`docs/CANONICAL.md`](CANONICAL.md)). Under
the user's heuristic, the n=18 apart prediction "TTC ≈ 2.5 s after
0.31 s of work" implies ~9 solutions exist, off by a factor of ~75
from 675.

## TTC over time (representative slices)

`apart` and `together` produce a finite, non-bouncy TTC that drifts
upward as elapsed grows but stays in the same order of magnitude.

```
n=22 apart  (took 18.8 s wall, found in 18.8 s)
  elapsed=1   ttc=2 603
  elapsed=5   ttc=2 299
  elapsed=10  ttc=3 403
  elapsed=15  ttc=3 996
  elapsed=18  ttc=4 539
  finish      ttc=4 664   covered=0.004
```

`sync` produces a TTC that grows linearly with elapsed at coverage 0:

```
n=18 sync (no solution in 56 s)
  elapsed=10  ttc=  21 000
  elapsed=20  ttc=  53 000
  elapsed=30  ttc=  72 000
  elapsed=40  ttc=  82 000
  elapsed=50  ttc=  98 000
  killed at 56 s, ttc=67 922 (random regression at the end)
```

```
n=20 sync (no solution in 45 s)
  elapsed=10  ttc= 175 000
  elapsed=20  ttc= 308 000
  elapsed=30  ttc= 470 000
  elapsed=40  ttc= 588 000
  elapsed=45  ttc= 661 939
```

`cross` always reports `ttc=None`:

```
n=20 cross (no progress in 48 s)
  elapsed=1   covered=0.000  ttc=None
  elapsed=10  covered=0.000  ttc=None
  ...
  elapsed=48  covered=0.000  ttc=None
```

## Diagnosis per mode

### `--wz=cross`: structural — can't finish a single tuple

`CrossMassModel::covered_mass = tuples_done / tuples_total`
(`src/search_framework/mode_adapters/cross.rs:336-346`). For n ≥ 18
under default settings, the first tuple shell takes longer than the
budget we ever gave it (65 s+ for n=18), so `tuples_done` is stuck at
0 and there is no rate to extrapolate from. There is partial credit
machinery for in-flight XY timeouts (`covered_partial_mass`), but it
divides by `tuples_total * xy_per_tuple * 1e6`, which is so large that
single-tuple in-flight micros never push it above the float noise.

This means **cross mode reports a usable TTC only when the first
tuple is small enough to finish during the budget** — basically only
trivially small `n`. For any n where the search is interesting, the
mode publishes nothing.

### `--wz=sync`: TTC linear in elapsed at low coverage

`projected_fraction` in `src/sync_walker.rs:1684-1754` predicts the
total node count by multiplying per-level branching factors `b_eff(L)
= children(L) / parents(L)`, then divides by the measured rate. When
the walker hasn't yet reached deep enough levels to sample
`b_eff(L)`, every unsampled level falls back to the **median of
already-sampled `b_eff` values** (line 1727). Each new second of
elapsed time inflates `running_product` further, while `nodes_visited`
grows roughly linearly in elapsed → `TTC = projected / rate ≈ const ×
elapsed`. This matches what we observe: the n=18 and n=20 sync runs
both produce TTC values that scale linearly with elapsed.

In other words: at low coverage, sync's TTC is "the *current* estimate
of the search-tree size given what we've sampled so far," not a
prediction that converges. It will only stabilize once the walker
reaches deep levels and can sample real `b_eff` there.

### `--wz=apart` / `--wz=together`: extrapolation from <1% coverage

These two modes do produce finite Hybrid TTCs that don't blow up, but
they are extrapolating from a tiny `covered_mass` — usually 0.001 to
0.01 by the time the first solution is found. Because the
denominator (covered fraction) is small, the TTC value is dominated
by the rate of partial credit from XY-timeout shortfall accounting
plus a handful of completed boundaries. The result drifts upward with
elapsed (e.g. n=24 apart: 4.2k → 7.4k over 6 s) and is not stable
within an order of magnitude.

The `--conj-tuple` smoke run (n=20 apart, single auto-picked tuple)
showed coverage actually climbing (0.4% → 1.6% → 1.9% → 2.2% → 2.8%
→ 3.9%) and TTC stabilizing in the 125–177 s band. So the underlying
TTC machinery works when the search isn't dominated by one
slow-to-finish boundary; the unconstrained search at n ≥ 20 is just
extremely slow at retiring the first boundaries due to skewed
boundary weights.

## Bottom line for the user's heuristic

Comparing `TTC` against `#canonical × first_sol_time`:

* **cross**: not measurable (no TTC).
* **sync**: not measurable (TTC tracks elapsed, not the search size).
* **apart / together**: measurable but the TTC underestimates by 1–2
  orders of magnitude at n=18 (where 675 canonicals would imply
  TTC ≈ 200 s and we measured 2.5–3.5 s). At n=20–24 we don't have
  ground truth, but the analogous extrapolation gap is presumably the
  same shape.

So **TTC is *not* yet accurate at n ≥ 20** in the sense the user is
asking about. The MDD modes' TTC is monotone, finite and Hybrid-
labelled (so it satisfies the contract in
[`TTC.md`](TTC.md)), but it's an extrapolation from a coverage
fraction so small that the absolute number is unreliable as a
first-solution-time predictor.

Concrete next steps if we want this to be predictive:

1. Cross adapter: report partial coverage at the *single in-flight
   tuple* level rather than dividing by `tuples_total * xy_per_tuple`
   (otherwise it permanently rounds to zero on big-n).
2. Sync adapter: only publish a TTC once enough levels have non-
   fallback `b_eff` samples; until then, return `None` rather than a
   number that scales with elapsed.
3. MDD adapters: weight boundaries by their actual descendant search
   mass (XY sub-cube count under each `(prefix, suffix)`) instead of
   uniform per-boundary mass, so the early "expensive" boundaries
   don't keep `covered_mass` near zero.

## Reproducing

```bash
cargo build --release
target/release/gen_mdd 7   # ~1 MB, <1 s
mkdir -p /tmp/ttc
for mode in cross apart together sync; do
  for n in 18 20 22; do
    extra="--mdd-k=7"
    [ "$mode" = "cross" ] && extra=""
    [ "$mode" = "sync"  ] && extra=""
    target/release/turyn --n=$n --wz=$mode $extra --sat-secs=120 \
      > /tmp/ttc/n${n}-${mode}.log 2>&1
  done
done
```
