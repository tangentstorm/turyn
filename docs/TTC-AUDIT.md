# TTC audit: is the reported coverage real? (August 2026)

This is an independent audit of the TTC metric for every search mode,
asking two questions the earlier calibration work
([`TTC-ACCURACY-MEASUREMENT.md`](TTC-ACCURACY-MEASUREMENT.md),
[`TTC-CALIBRATION.md`](TTC-CALIBRATION.md)) did not separate:

1. **Is `covered_mass` true?** When a mode says `covered=1.000`, did it
   actually search the whole space?
2. **Is TTC calibrated?** Does `t + TTC(t)` predict the observed finish
   time `T`?

Question 2 is meaningless if question 1 fails, and question 1 had never
been tested directly. It is testable: for every `n <= 32` the published
catalogue in [`data/`](../data) lists every canonical `TT(n)`. A run that
claims full coverage must have found all of them.

The tool for that is [`src/bin/check_coverage.rs`](../src/bin/check_coverage.rs):

```bash
target/release/turyn search --n=16 --wz=apart --mdd-k=5 --all \
  --threads=1 --seed=0 > run.log
target/release/check_coverage 16 run.log
```

It canonicalizes every quadruple the run printed, canonicalizes every
catalogued class, and diffs the sets. A class counts as missing only when
**no member of its 1024-element symmetry orbit** appears anywhere in the
run's output, so the verdict does not depend on `canonicalize` picking the
same representative.

> **STATUS: the accounting defects below are FIXED as of the commit that
> added this banner.** Sections 1-8b describe the metric as it was when
> audited, and are kept as the evidence trail; **section 12 records what
> changed and what the numbers look like now.** The `check_coverage`
> tool and the reproduction steps still work — run them.

## Headline

**`--wz=apart` reports `covered=1.000` on runs that searched as little as
13 % of the space.** The number is not a measurement of coverage; it is
decoupled from what was searched. `--wz=together` is honest, `--wz=cross`
is honest but unusable at interesting `n`, `--wz=sync` is honestly
labelled `Projected`.

The n=56 headline benchmark in `README.md`, `CLAUDE.md` and `IMPROVE.md`
is `--wz=apart --mdd-k=10` — the affected mode, in the regime where the
defect is largest. At n=56 the reported TTC moves **3.2×** (7.5 d → 23.5 d)
purely by changing a truncation cap that does not change the search
space, and it moves in the *flattering* direction as the truncation gets
more aggressive (section 8b).

Summary of what each mode's `covered` number is worth:

| mode | `covered` trustworthy? | why |
|---|---|---|
| `apart` | **no** | W/Z caps close boundaries cleanly; `covered=1.000` observed on runs that found 13–71 % of the catalogue |
| `together` | yes | re-queues capped work; but 45× slower and rarely finishes |
| `cross` | yes below n=22, **no** at n>=22 | `max_z`/`max_w` truncate silently once `C(n-1,r) > 200 000` |
| `sync` | n/a | `Projected` by design; also contradicts its own telemetry by 14× |
| stochastic | n/a | hard-wired to 0, correctly |

**After the §12 fixes** every mode's `covered` reflects what was
searched, and `apart`/`together` reproduce the catalogue exactly at
every (n, k) in `scripts/check-coverage-suite.sh --full` — including
the small-`k` cases that used to lose a third of the classes (§12.2b)
— provided the Z spectral propagator stays off, which is now the
default.

## 1. The mechanism: truncation credited as completion

`MddStagesAdapter` credits a boundary's mass when its descendant search
closes. `BoundaryProgress` is careful about *timeouts*: a SAT
conflict-budget exhaustion sets `*timed_out`, the stage calls
`mark_abandoned`, and the boundary never receives exact credit. That is
correct and matches [`TTC.md`](TTC.md) §4.1.

But timeouts are not the only way the descendant search ends early. Two
hard iteration caps also cut it off, and **neither sets the taint**:

| cap | value | where | on hit |
|---|---|---|---|
| W middles per boundary | 128 (`TURYN_MAX_W_PER_BND`) | `mdd_pipeline.rs`, `process_solve_w` | plain `break` |
| Z middles per (boundary, W) | **16, hardcoded** (`cfg.max_z.min(16)`) | `mdd_pipeline.rs`, `process_solve_z` | plain `break` |

Both paths fall through to a clean closure, so the boundary bumps
`completed_weight` and contributes its **full** weight to
`covered_exact` — as though its subtree had been exhausted.

`--wz=together` does not have this problem. `process_solve_wz` sets
`more_possible = true` on the same cap and re-queues the item at lower
priority, with the comment *"NO CAP on attempts — we defer hard
boundaries to lower priority slots but never abandon them."* That is
exactly the right behaviour; it just was never applied to the `apart`
stages.

Note `cfg.max_z.min(16)`: the Z cap is **hardcoded at 16** and
`--max-z=64` cannot raise it.

### Why every previous calibration missed this

The W cap only engages on the SAT-based W path, chosen when
`middle_m = n - 1 - 2k > 20`:

| config | `middle_m` | W path | 128-cap active? |
|---|---|---|---|
| n=18, k=5 | 7 | brute force | no |
| n=26, k=7 | 11 | brute force | no |
| n=56, k=7 | 41 | SAT | **yes** |
| n=56, k=10 | 35 | SAT | **yes** |

Every calibration run ever recorded (n=16, 18, 22, 26) used the
brute-force path. **The only configuration that exercises the broken
accounting is the n=56 one the project actually cares about**, and it is
the one configuration where ground truth cannot be checked.

The Z cap is worse: it engages whenever `2^(n - 2k) > 16`, i.e. from
`n = 2k + 5` up. At k=5 that is n >= 15 — so it is active in almost every
run, including the n=18 and n=22 calibration runs.

## 2. Dose-response: coverage is decoupled from the search

`--max-z` only ever *lowers* the Z cap (the hardcoded `.min(16)` sets the
ceiling), which makes it a clean experimental knob: it changes how much
of the space is searched without changing the space itself. If
`covered_mass` measured coverage, it would move with the knob.

`--n=16 --wz=apart --mdd-k=5 --all --threads=1 --seed=0`, run to the
mode's own idea of completion:

| `--max-z` | reported `covered` | canonical classes found | true coverage |
|---:|---|---:|---:|
| 2  | **1.000** | 99 / 739 | 13 % |
| 4  | **1.000** | 193 / 739 | 26 % |
| 8  | **1.000** | 329 / 739 | 45 % |
| 16 (default) | **1.000** | 526 / 739 | 71 % |
| 64 (clamped to 16) | **1.000** | 518 / 739 | 70 % |

The reported number is pinned at 1.000 across a 5.3× swing in real
coverage. This is the whole finding in one table.

## 3. Per-mode coverage honesty

All runs `--all --threads=1 --seed=0`, single-threaded, to the mode's own
stopping point. `mdd-k=5` where applicable.

| run | reported `covered` | quality | classes found | catalogue | verdict |
|---|---|---|---:|---:|---|
| `apart` n=14 | 1.000 | Hybrid | 184 | 186 | 2 missing, orbit-confirmed |
| `apart` n=16 | **1.000** | Hybrid | 522 | 739 | **217 missing (29 %)** |
| `apart` n=18 | **1.000** | Hybrid | 430 | 675 | **245 missing (36 %)** |
| `together` n=14 | 1.000 | Hybrid | 184 | 186 | 2 missing, orbit-confirmed |
| `together` n=16 | 0.229 | Hybrid | 250 | 739 | honest: did not claim completion |
| `cross` n=10 | 1.000 | Hybrid | 43 | 43 | **complete** |
| `cross` n=12 | 1.000 | Hybrid | 127 | 127 | **complete** |

Every quadruple every mode printed passes full Turyn verification, is in
BDKR canonical form, and is in the catalogue. Nothing is spurious and
nothing is duplicated — the modes only ever *under*-report.

At n=16 the holes are spread across all eight sum-tuple shells, not
concentrated in one, which is consistent with a per-boundary cap rather
than a missing tuple. The hole grows with `n` exactly as the Z-cap
mechanism predicts — the Z middle space is `2^(n-2k)` against a fixed cap
of 16:

| n (k=5) | Z middle space | cap | classes found | missing |
|---:|---:|---:|---|---:|
| 14 | 2^4 = 16 | 16 | 184 / 186 | 1 % |
| 16 | 2^6 = 64 | 16 | 522 / 739 | 29 % |
| 18 | 2^8 = 256 | 16 | 430 / 675 | **36 %** |

The 2 missing classes at n=14 are a **separate, smaller bug**: at n=14,
k=5 the Z middle has only `2^4 = 16` values, exactly the cap, so nothing
can be truncated — and `together`, which handles caps correctly, misses 2
as well (a different 2, so the union is 3 classes). Root cause not yet
identified. It is not the XY product law: rebuilding the MDD with
`--xy-raw` and running `MDD_XY_RAW=1 --no-xy-product` reproduces 184/186
exactly.

## 4. Calibration: TTC predicts the wrong quantity accurately

For runs that reach their own stopping point, the observed `T` is ground
truth and a calibrated metric satisfies `t + TTC(t) = T` at every tick.
Error is `(t + TTC(t) - T) / T`.

| run | T (s) | ticks | error range | ticks with abs err > 25 % |
|---|---:|---:|---|---|
| `apart` n=14 | 3.93 | 3 | −7.9 % … +4.2 % | 0 / 3 |
| `apart` n=16 | 19.39 | 19 | −33.4 % … +6.8 % | 1 / 19 |
| `together` n=14 | 174.95 | 174 | −68.5 % … +47.1 % | **77 / 174** |

`apart` looks well calibrated — and this is the trap. Its `T` is the time
to reach a `covered=1.000` that is 29 % false at n=16. **The prediction
and the ground truth are computed over the same truncated space, so they
agree with each other while both under-describe the real search.** A
metric can be perfectly self-consistent and still not measure the thing
you care about. That is the single most important thing to understand
about the existing calibration results: they validate internal
consistency, not coverage.

`together`, whose coverage accounting is honest, is the mode whose TTC is
*badly* calibrated — it swings from −69 % to +47 % and is off by more than
25 % on 44 % of its ticks. The honest mode has the noisy metric; the
flattering mode has the smooth one.

### The regime that actually matters

At n=26 and n=56 the MDD modes never leave `covered < 0.001`, so only the
first tick of a completed small-n run is the matched regime:

| run | covered at t=1s | predicted total | true T | prediction / truth |
|---|---:|---:|---:|---:|
| `apart` n=14 | 0.276 | 3.6 s | 3.9 s | 0.92× |
| `apart` n=16 | 0.078 | 12.9 s | 19.4 s | 0.67× |
| `together` n=14 | 0.018 | 55.0 s | 175.0 s | **0.31×** |

The bias is one-directional: at low coverage TTC **under**-predicts, by up
to 3.2× in the sample above, because the scheduler hands out cheap
boundaries first and extrapolates their rate to the expensive tail.

So the published n=56 figure of ~1.68 × 10⁶ s parallel (≈19.5 days,
`--wz=apart --mdd-k=8`) should be read as a **lower bound with two
independent inflation factors stacked against it**:

1. low-coverage extrapolation bias — empirically up to ~3× optimistic;
2. the W/Z caps crediting truncated boundaries as complete — unbounded,
   and specific to `apart`, and largest exactly at n=56.

"19.5 days" is not an estimate of the time to search TT(56). It is the
time for `--wz=apart` to reach its own idea of done, which is not the
same thing.

## 5. Per-mode structural verdict

### `--wz=apart` — coverage is not a measurement

`covered_exact = completed_weight / total_weight` with per-boundary
weights seeded from live XY-path counts. The weighting is good; the
closure rule is not: capped boundaries close clean. **Do not use the
number.**

### `--wz=together` — honest, and the slowest

Same mass model, but `process_solve_wz` re-queues capped items instead of
closing them, so coverage tracks reality. The price is throughput:
together took 175 s where apart took 3.9 s at n=14 (**45×**), and timed
out at 900 s having covered 0.229 at n=16 where apart "finished" in 19 s.
Part of the historical apart-vs-together throughput gap is not a real
speed difference — it is apart getting credit for work it skipped.

### `--wz=cross` — honest, correct, and unusable at interesting n

The only mode that reproduced the catalogue exactly (43/43 at n=10,
127/127 at n=12). Three separate problems keep it from being the
reference oracle:

1. **Silent enumeration truncation.** `build_w_candidates` and the Z
   stream pass `cfg.max_w` / `cfg.max_z` (default 200 000) as a hard
   `limit` to `generate_sequences_permuted`, which visits
   `min(limit, total)` sequences and returns. No warning is emitted, the
   tuple is still marked done, and coverage still reaches 1.000. The cap
   binds from **n = 22** up:

   | n | max `C(n-1, r)` | vs cap 200 000 |
   |---:|---:|---|
   | 20 | 92 378 | ok |
   | 22 | 352 716 | **truncates** |
   | 26 | 5 200 300 | **truncates 26×** |
   | 30 | 77 558 760 | **truncates 388×** |

   Demonstration at n=10, where the true answer is known: `--max-z=10
   --max-w=10` finds **1 of 43** classes and still reports
   `covered=1.000`.

2. **Uniform tuple weighting.** `covered = tuples_done / tuples_total`
   treats every sum-tuple shell as equal. They are not: at n=26 the
   17 shells span 3.4e26 to 9.9e27 configurations, and the largest single
   shell is **50 % of the entire space** while being credited 1/17 = 5.9 %.
   Coverage can read 0.94 with half the work left.

3. **Coverage never leaves zero at n >= 18**, because the first shell does
   not finish, so `tuples_done = 0` and TTC is `None` — the failure the
   April measurement already recorded.

### `--wz=sync` — honestly labelled, unverifiable

`covered = elapsed / TTC_parallel` from a per-level branching-factor
product, labelled `Projected`. Substituting into the engine's formula
gives `TTC = TTC_parallel - elapsed`, so the round-trip is at least
self-consistent. The estimator has been improved since the April
measurement (it now uses per-parent branching
`children_by_level[L] / nodes_by_level[L]`, which is unbiased on a
partial DFS, instead of the level-ratio estimator that was
downward-biased). It is a tree-size extrapolation with a median fallback
for unsampled levels, and it has no self-validating ground truth because
it never reaches `covered = 1.0`. The `Projected` label is the correct
one and should be believed literally.

### stochastic — correct by construction

`covered_mass` is hard-wired to `ZERO` with `Projected`, so TTC is
`None`. Non-exhaustive mode, honestly reported. No issues.

## 6. `total_log2_work` is wrong for every mode

All three exhaustive adapters return `total_log2_work = 2n`
(`cross.rs:439`, `sync.rs`, `mdd_stages.rs:1222`). [`TTC.md`](TTC.md)
§1.1 defines it as `log2(total raw-equivalent configurations)`, but the
raw space is `X, Y, Z` (n bits each) plus `W` (n−1 bits) = `4n − 1` bits.
At n=26 the real figure is 2^103, not 2^52.

Consequences:

* `--bench-cover-log2=X` stops at `covered >= 2^(X - 2n)`, so at n=26,
  `X=38` means "covered ≥ 6.1e−5", not "2^38 configurations". The docs'
  description of the flag is off by 2^51 at n=26.
* Because the implied fraction is `2^(X - 2n)`, holding `X` fixed while
  raising `n` by 2 shrinks the target fraction **16×**. Fixed
  `--bench-cover-log2` is therefore *not* fixed work across `n`, and
  benchmark numbers must not be compared across `n`.
* Within one mode at one `n` it is still a valid fixed-fraction stop,
  which is why counter-mode A/B comparisons remain sound. That part of
  `IMPROVE.md` is fine.

## 7. Reproducibility: `--threads=1 --seed=0` — FIXED

[`IMPROVE.md`](../IMPROVE.md) builds its acceptance procedure on this
claim:

> Counter totals are **bit-exact** across reruns of one binary, so any
> non-zero delta between binaries is real signal.
> [...] **Accept if the predicted counter moved >= 0.2 %** in the
> predicted direction.

It was false in two different ways. Both are now fixed; the claim holds.

### 7.1 What was wrong

**Run-ahead against the bench stop.** The report channel is unbounded, so
the worker kept popping and handling items while its reports queued up.
The coordinator only evaluated `bench_target_reached` as it drained them,
by which point the worker had handled an unbounded number of extra items
— how many depending purely on thread timing. Measured at n=26
`--wz=together --mdd-k=7 --bench-cover-log2=34 --threads=1 --seed=0`,
three runs: boundary count **221 486 / 253 218 / 245 780**, and at a
deeper stop **338 828 / 274 693 / 219 716** (1.54×), while `covered` and
the W/Z/XY solve counters were stable.

**The spectral propagator.** `--wz=apart` was nondeterministic even in
the solve counters — 79 181 / 79 974 / 79 725 XY solves over three
identical runs at n=16, ~1 % against a 0.2 % acceptance bar. That was a
symptom of the mirror desync in §12.2b, not of the engine: the
propagator's verdict depended on propagation order, so any timing
variation changed which solutions the search found.

### 7.2 The fix

`Lockstep` in `search_framework/engine.rs`: with one worker, the next
pop waits until the coordinator has fully applied the previous report —
mass credited, children queued, stop condition evaluated. The run then
stops on the same item every time. It engages only for
`worker_count == 1` **with a bench stop configured**, i.e. exactly the
benchmarking configuration whose purpose is reproducibility; ordinary
searches and multi-worker runs keep their unsynchronised throughput.
`TURYN_NO_LOCKSTEP=1` disables it.

The §12.2b spectral fix removed the other source.

### 7.3 Measured after

| config | before | after |
|---|---|---|
| n=26 together, cover-log2=85, 3 runs | varied | **33 / 33 / 33** boundaries |
| n=26 together, cover-log2 shallow, 5 runs | 3666 / 6820 / 12321 | **1 / 1 / 1 / 1 / 1** |
| n=16 apart, cover-log2=60, 4 runs | — | **13 765 XY solves ×4**, covered 1.251e-1 ×4 |
| n=16 apart, run to completion, 3 runs | 79 181 / 79 974 / 79 725 | **identical** |
| n=12 apart k=2, run to completion, 3 runs | varied | **identical** |

Cost: about 17 % per item in the benchmark configuration only. The
lock-stepped run also does *less* total work, because it stops on the
target instead of over-running it — at n=16 cover-log2=60 it handles
13 765 XY solves where the unsynchronised run handled 14 547–15 598 (and
varied by 7 %).

`bench_stop_is_bit_exact_under_a_single_worker` pins it, and fails with
`TURYN_NO_LOCKSTEP=1`.

### 7.4 What this means for the protocol

Counter-mode A/B at `--threads=1 --seed=0` is now sound in both modes and
at any `--bench-cover-log2` depth, so `IMPROVE.md`'s procedure is valid
as written. Two caveats remain:

* **Multi-worker runs are still not reproducible** and never will be by
  this route — worker interleaving decides which boundary retires first.
  Use `--threads=1` for A/B, and `docs/BENCHMARKING.md`'s paired
  wall-clock protocol for anything measured with threads > 1.
* **`--bench-cover-log2` values from before the `total_log2_work` fix
  (§6) mean something different now.** Raise old targets by `2n - 1`
  (51 at n=26) to select the same work.

## 8. `--wz=sync` contradicts itself in the same run

`--n=10 --wz=sync --all --threads=1 --seed=0` terminates in 0.25 s with
its tree exhausted (level 10 has 0 children). Three lines of its own
output disagree:

```
Per-level: cumulative root-coverage (∏ cov) = 1.000e0
Per-level: direct TTC (from coverage product) ≈ 2.504e-1s parallel
Framework search (--wz=sync): covered=0.070/1.000 ... ttc=Some(3.358229904s)
```

The walker's own per-level telemetry says it covered the tree completely
(TTC 0.25 s, already elapsed); the `projected_fraction` that reaches the
universal mass model says 7 % (TTC 3.36 s). A 14× disagreement between
two coverage numbers printed by the same run, three lines apart.

Separately, "covering the sync walker's tree" is not the same as covering
the TT search space: with its tree exhausted at n=10 it had found **1 of
43** classes. Whatever `--wz=sync`'s coverage measures, it is not the
fraction of `TT(n)` ruled out, and its TTC must not be compared with the
MDD modes' as though it were the same quantity.

| run | reported covered | wall | classes found | catalogue |
|---|---|---:|---:|---:|
| `sync` n=10 | 0.070 | 0.3 s (tree exhausted) | 1 | 43 |
| `sync` n=12 | 0.231 | 1.5 s | 0 | 127 |
| `sync` n=14 | 0.046 | 80.7 s | 1 | 186 |

## 8b. The n=56 number moves 3.2x with a truncation knob

The cleanest demonstration that the `apart` TTC measures truncation
rather than search. `TURYN_MAX_W_PER_BND` changes how many W middles each
boundary enumerates before the loop breaks. **It does not change the
search space** — only how much of each boundary is skipped before the
boundary is (incorrectly) credited as complete.

`--n=56 --wz=apart --mdd-k=7 --sat-secs=60 --threads=1 --seed=0`, three
repeats per condition:

| `TURYN_MAX_W_PER_BND` | reported TTC (median) | in days | within-condition spread |
|---:|---:|---:|---:|
| 8 | 6.44e5 s | **7.5 d** | 5 % |
| 128 (**default**) | 2.03e6 s | **23.5 d** | 3 % |
| 512 | 2.44e6 s | **28.2 d** | 121 % (one outlier) |

Tightening the truncation 16× (128 -> 8) improves the reported TTC by
**3.2×**, far outside the ~3-5 % run-to-run spread. The search got
*worse* — it skips more work per boundary — and the metric got *better*,
because each truncated boundary still books its full weight as exact
coverage.

This is the mechanism behind the `N1` entry in
[`OPTIMIZATION_LOG.md`](OPTIMIZATION_LOG.md), which introduced the 128
cap and recorded a **"21.5× TTC improvement (53923d -> 2509d)"** at n=56.
Some of that is real — capping W does unblock stuck workers, which was
the stated motivation, and boundaries/s genuinely rose. But the TTC
number it was scored on cannot distinguish that from the accounting
artifact, and the artifact alone is worth at least 3.2× in the same
direction.

The published TT(56) estimate of ~19.5 days should therefore be read as:
"the time for `--wz=apart` to reach its own idea of done, under the
current cap settings" — a quantity that can be improved arbitrarily by
lowering the cap, and which is not an estimate of the time to search
TT(56).

## 9. What to do

Ordered by how much they change the numbers, not by effort.

> **This list is the audit's original recommendations, kept as written
> for the record. Items 0-8 have all been implemented — see §12 for
> what each fix actually did and what it measured. Read §12.7 and
> §12.2b for what is still open; do not treat anything below as
> outstanding work.**

0. **Re-check any `--wz=apart` optimization accepted on a sub-2 %
   counter delta** (section 7). Counter-mode A/B is sound for
   `--wz=together` solve counters and unsound for `apart`; `IMPROVE.md`
   should say which counters are stable in which mode rather than
   claiming bit-exactness in general.

1. **Stop crediting truncated boundaries as complete (`--wz=apart`).**
   The minimal honest fix is one line per cap: set the abandoned taint
   when breaking on `max_w_per_boundary` or `ctx.max_z`, exactly as the
   conflict-budget path already does. Coverage then stops at the true
   fraction and TTC reflects it. The better fix is to copy
   `process_solve_wz`'s `more_possible` re-queue into `process_solve_w`
   and `process_solve_z`, which restores both honesty *and* completeness
   — `together` shows it works.

   Expect the reported n=56 TTC to get **much worse** when this lands.
   That is the point: the current number is the artifact.

2. **Raise or remove the hardcoded `cfg.max_z.min(16)`.** Even with the
   taint fixed, a Z cap of 16 against a `2^(n-2k)` middle space means
   `apart` can never finish anything at interesting `n`. At minimum let
   `--max-z` raise it.

3. **Warn on every silent truncation.** `cross`'s `max_z`/`max_w` limits
   and both MDD caps should emit a one-line warning naming the cap and
   the affected count, and the final summary should refuse to print
   `covered=1.000` when any truncation fired. SPEC.md already forbids
   silently removing valid solutions; the code needs to be able to say
   when it did.

4. **Weight `cross`'s tuples by their binomial product** instead of
   uniformly. The numbers are already computed and printed by
   `turyn tuples`.

5. **Fix `total_log2_work` to `4n - 1`** (or `4n - 7` after rule (i)) and
   correct the `--bench-cover-log2` description in `TTC.md` §1.1 and
   `IMPROVE.md`. Note this changes what a given `X` means, so old
   benchmark numbers are not comparable across the change.

6. **Find the residual n=14 hole** (2 classes, present in both `apart`
   and `together`, unrelated to the caps and to the XY product law).
   `check_coverage` names the exact missing quadruples.

7. **Reconcile `--wz=sync`'s two coverage numbers**, and stop
   publishing `projected_fraction` as if it were comparable to the MDD
   modes' fraction. Either make it the same quantity or give it a
   distinct name in the output.

8. **Wire `check_coverage` into CI.** `--wz=cross --n=10` runs in 2 s and
   reproduces the catalogue exactly; `--wz=apart --n=16` takes 20 s. Both
   are cheap enough to run on every commit, and either would have caught
   this.

## 10. Reproducing

```bash
cargo build --release
target/release/gen_mdd 5

# The dose-response table (section 2) -- the core result.
for mz in 2 4 8 16; do
  target/release/turyn search --n=16 --wz=apart --mdd-k=5 --all \
    --threads=1 --seed=0 --max-z=$mz > /tmp/mz.$mz 2>&1
  echo -n "max-z=$mz reported: "
  grep -o 'covered=[0-9.]*/[0-9.]*' /tmp/mz.$mz | tail -1
  target/release/check_coverage 16 /tmp/mz.$mz | grep 'distinct canonical'
done

# Per-mode coverage honesty (section 3).
target/release/turyn search --n=16 --wz=apart --mdd-k=5 --all \
  --threads=1 --seed=0 > /tmp/a16.log 2>&1
target/release/check_coverage 16 /tmp/a16.log

# cross reproduces the catalogue exactly at n=10 and n=12.
target/release/turyn search --n=10 --wz=cross --all --threads=1 --seed=0 \
  > /tmp/x10.log 2>&1
target/release/check_coverage 10 /tmp/x10.log

# cross truncates silently when the caps bind.
target/release/turyn search --n=10 --wz=cross --all --max-z=10 --max-w=10 \
  > /tmp/x10cap.log 2>&1
target/release/check_coverage 10 /tmp/x10cap.log   # 1 of 43, covered=1.000
```

## 11. Relationship to the earlier TTC documents

* [`TTC-ACCURACY-MEASUREMENT.md`](TTC-ACCURACY-MEASUREMENT.md) (April) is
  still correct on what it measured: TTC drifts and does not converge at
  n >= 20 when run to first solution. It did not test coverage honesty.
* [`TTC-CALIBRATION.md`](TTC-CALIBRATION.md) (April) concluded TTC is
  calibrated to ~10 % on `--wz=apart` runs to `covered=1.0`. That
  conclusion stands *as stated* — the document is explicit that it does
  not claim the solution count is right, and it flagged the mode
  disagreement at n=14 as unexplained. This audit is the follow-up it
  asked for: the disagreement is real, the cause is the uncredited
  caps, and it means those `covered=1.0` runs were finishing a truncated
  search. **The calibration was measuring self-consistency, not
  coverage.**
* [`TTC.md`](TTC.md)'s contract is not at fault. §4.1 already requires
  that exact credit means no residual work remains; `apart` violates it.
  The fix is in the adapter, not the spec.

## 12. What was fixed (August 2026)

### 12.1 `--wz=apart`: the W and Z caps are now batch sizes, not truncation

`process_solve_w` and `process_solve_z` gained the `attempt` +
`prior_blocks` machinery `process_solve_wz` already had. Hitting the
per-boundary W cap (`TURYN_MAX_W_PER_BND`, 128) or the Z batch cap
(`ctx.max_z`, 16) now:

* accumulates the blocking clauses for the middles enumerated so far,
* re-queues the remainder as a fresh `SolveW` / `SolveZ` item at low
  priority carrying those blocks, so the next attempt continues instead
  of repeating, and
* leaves the boundary's pending count above zero, so it cannot be
  credited as complete.

A boundary is now credited only when SAT genuinely returns `Some(false)`.
One related bug fixed on the way: the Z loop skipped the blocking clause
for the last middle of each batch (`if z_count < ctx.max_z`), which was
harmless only while the remainder was being discarded — with the batch
resumed it would have made every later attempt re-find the same Z.

**The dose-response from section 2 is now flat.** Same command, same
knob, run to completion:

| `--max-z` | reported `covered` | classes found | before this fix |
|---:|---|---:|---:|
| 2  | 1.000 | **730** / 739 | 99 |
| 4  | 1.000 | **730** / 739 | 193 |
| 8  | 1.000 | **730** / 739 | 329 |
| 16 | 1.000 | **730** / 739 | 526 |

Coverage across `n`, `--wz=apart --mdd-k=5`:

| n | before | after | remaining gap |
|---:|---:|---:|---:|
| 14 | 184 / 186 | 184 / 186 | 2 |
| 16 | 522 / 739 | **730 / 739** | 9 |

The cost is real work that used to be skipped: n=16 goes from 19.4 s to
~26-28 s. That is the correct direction — the old time was the time to
finish a truncated search.

### 12.2 The XY stage returned one middle per boundary

Root cause of the coverage holes, found by bisecting one missing class
through the pipeline with `--outfix` and `TURYN_TRACE_BND`:

* the boundary was **live in the MDD** and **emitted by
  `enumerate_live_boundaries`**;
* the exact target `(Z, W)` pair **reached the XY stage**;
* the XY solve at the target's XY boundary **returned SAT** — but with a
  *different* X/Y middle than the catalogued one.

`SolveXyPerCandidate::try_candidate` (and the parallel hand-rolled solve
in `process_solve_wz`, which `--wz=together` uses) called
`solve_with_assumptions` once and took the single model. One XY boundary
can extend to several distinct XY middles, and every one after the first
was silently dropped while the boundary was still credited as fully
searched.

That explains every symptom at once: both modes affected (they share the
XY fast path), immune to the caps, the product law, the spectral filters,
`--mdd-extend` and the MDD range pruning, and **strongly `k`-dependent** —
the XY middle is `n - 2k` positions, so a larger `k` leaves fewer middles
to collide on a shared boundary.

Both paths now enumerate to UNSAT, blocking the full `(X, Y)` assignment
each round (boundary literals included, so a clause can never bite on
another boundary). Cost is one extra solve per solution found, and
solutions are rare — 184 SAT in ~200k solves at n=14 — so there is no
cap, which would be the very bug this fixes.

One trap worth recording: the blocking clause **must** be added after
`Solver::reset()` (= `backtrack(0)`). Adding it on a live trail corrupts
the watch lists and makes later solves report spurious UNSAT; the first
version of this fix did that and made coverage *worse* (n=14: 184 → 162).
The W and Z enumeration loops already did `reset(); add_clause(...)` for
the same reason.

| run | before caps fix | after caps fix | after XY fix | catalogue |
|---|---:|---:|---:|---:|
| `apart` n=14 k=4 | 182 | 182 | **186** | 186 |
| `apart` n=14 k=5 | 184 | 184 | **186** | 186 |
| `apart` n=16 k=5 | 522 | 730 | **739** | 739 |
| `apart` n=18 k=6 | — | 673 | **675** | 675 |
| `together` n=14 k=5 | 184 | 184 | **186** | 186 |

### 12.2b The Z spectral propagator lost the rest — two bugs

The remaining hole (n=18 k=5 found 427 of 675) traced to the Z-middle
solver's native per-frequency propagator, the one enforcing
`|Z(ω)|² ≤ (3n−1) − |W(ω)|²`. Two separate defects, found with a
sub-second reproducer: **n=12 --mdd-k=2 finds 96 of 127**, and the
common factor across every failing case is `middle_n = n − 2k ≥ 8`,
which is exactly the gate on building the Z spectral tables.

**Bug 1: the propagator's mirror lagged the trail.** `SpectralConstraint`
keeps its own copy of the assignment (`assigned` / `values`), updated
lazily inside the propagation loop one literal at a time. Whenever
another propagator enqueued spectral variables that the loop had not
reached yet, the mirror fell behind — 14,511 desyncs in a single n=12
run. Both `check_conflict`'s verdict and the conflict clause built from
`spec.values` then described a state the solver was not in. Fixed by
mirroring the assignment in `Solver::enqueue`, which makes it exactly
inverse to the per-trail-entry `unassign` that `backtrack` already did.
A `debug_assert` in the propagation path now pins the invariant.

That alone took n=12 k=2 from 96 to 121 of 127.

**Bug 2: something still prunes.** With the mirror provably exact (the
audit reports 0 desyncs and 0 non-falsified clause literals) the
propagator still lost ~5 %. The check itself is sound — a test walks a
catalogued TT(12) through it and asserts no conflict on **any** of the
2^8 subsets of its middle assignment — and the solver's setup was
verified to match an independent computation to six decimals
(`min_pfb=11.085643@fi=46`, identical). The residual is unidentified.

**So the propagator is now off by default** (`TURYN_Z_SPECTRAL=1` opts
back in). It buys roughly 2.5× throughput and costs solutions, which is
the wrong trade for a mode whose coverage number is supposed to mean
something. The post-hoc `spectral_pair_ok` check still filters every
emitted pair, so enabling it never yields a *wrong* solution — only a
missing one.

| run | before | after |
|---|---:|---:|
| `apart` n=12 k=2 | 96 / 127 | **127 / 127** |
| `apart` n=14 k=3 | 143 / 186 | **186 / 186** |
| `apart` n=14 k=5 | 184 / 186 | **186 / 186** |
| `apart` n=16 k=4 | 611 / 739 | **739 / 739** |
| `apart` n=16 k=5 | 522 / 739 | **739 / 739** |
| `apart` n=18 k=5 | 427 / 675 | **675 / 675** |
| `together` n=14 k=5 | 184 / 186 | **186 / 186** |

n=18 k=5 goes from 164 s to 724 s. That is the price of searching the
space instead of a subset of it.

**`--mdd-k >= 6` is no longer needed** — small `k` is complete now.

### 12.2z Tooling this needed

Three hooks, all kept:

* `TURYN_TRACE_BND=<zhex>,<whex>` — reports whether a boundary is live in
  the MDD and whether the enumeration emitted it, and turns on the
  per-boundary SolveW/SolveZ/XY tracing (which W middles were generated,
  which (Z, W) pairs reached XY, which XY boundaries were tried and with
  what verdict, and why each Z enumeration loop exited).
* `TURYN_AUDIT_SPECTRAL=1` — checks, at every spectral conflict, that the
  propagator's mirror matches the solver's assignment and that the
  conflict clause is actually falsified.
* `TURYN_Z_SPECTRAL=1` / `TURYN_NO_Z_SPECTRAL` — the bisection lever that
  isolated the propagator in the first place, now the opt-in switch.

The bisection that found it: the missing class's boundary was live and
emitted; its `(Z, W)` pair reached the XY stage; its XY boundary was
tried and returned SAT at n=14 — that was the multiplicity bug of §12.2.
At n=18 the same trail showed the target `Z` and target `W` each
appearing but **never together**, which put the fault in the Z
enumeration rather than anywhere downstream.

### 12.2c `--mdd-extend=0` was silently ignored

`main.rs` forced `mdd_extend = 1` for apart/together whenever it was 0,
so the flag could not turn the extension pre-filter off — which makes
bisecting a coverage hole impossible. An explicit `--mdd-extend=0` is now
honoured; the default when the flag is absent is unchanged.

### 12.3 `--wz=cross`: space-weighted tuples, pro-rata truncation credit

* `covered_mass` is now `Σ_tuples weight_t · fraction_enumerated_t`, with
  `weight_t` the tuple's exact binomial shell size normalized to 1,
  replacing `tuples_done / tuples_total`. At n=26 the largest shell is
  half the space and was being credited 1/17.
* `generate_sequences_permuted` now returns `(visited, total)` and is
  `#[must_use]`, so a `cfg.max_z` / `cfg.max_w` truncation cannot be
  silently discarded again. `build_w_candidates` and `for_each_zw_pair`
  thread it through, and a truncated shell is credited pro-rata.
* A truncated run prints an explicit `WARNING: ... this run is a SAMPLE,
  not an exhaustive search`.

Verified at n=10: default settings still give `covered=1.000` and
43/43 classes; `--max-z=10 --max-w=10` now reports **`covered=0.355`**
plus the warning, where it used to report `covered=1.000` while finding
1 of 43.

### 12.4 `--wz=sync` is labelled non-exhaustive

Sync exhausts its own walker tree at n=8 having found 1 of the 6
catalogued classes, and 1 of 43 at n=10. Its TTC line now reads
`TTC (NON-EXHAUSTIVE walker: covers the walker tree, not the TT space)`,
and the per-level telemetry line that used to say "cumulative
root-coverage" now says `walker-DFS completion (∏ processed/children)`
and states that reaching 1.0 is not coverage of the TT space. The two
numbers no longer read as competing estimates of the same quantity.

### 12.5 `total_log2_work` and the `--bench-cover-log2` contract

All three exhaustive adapters now use
`search_framework::mass::raw_log2_work(n) = 4n - 1` instead of `2n`.
Every run that sets `--bench-cover-log2` prints, before searching:

```text
[framework:apart] bench stop: total_log2_work=71 target=2^60 => stop at covered >= 4.883e-4
```

so the target fraction is never ambiguous. **Benchmark targets recorded
before this change must be raised by `2n - 1`** to select the same
amount of work (51 at n=26).

### 12.6 Low-coverage extrapolation is now labelled

`covered` prints in scientific notation (it used to round to `0.000`,
which hid exactly the cases that need care), and a TTC computed from a
tiny fraction says so:

```text
covered=6.536e-6/1.000 ttc=Some(6928682s) (quality=Hybrid)
  [EXTRAPOLATED >10000x from covered<1e-4: order-of-magnitude only]
```

### 12.7 What is still not trustworthy at n=56

The accounting is honest now, but n=56 remains a hard extrapolation
problem, and the number moved in the direction the audit predicted:
`--wz=apart --mdd-k=7 --sat-secs=60` used to report ~2.0e6 s at the
default cap and now reports 2.6e6-7.7e6 s. Two caveats stand:

* **Run-to-run variance is large.** Two repeats of the identical
  command at the default cap gave 2.6e6 s and 7.7e6 s (3×). That is the
  scheduler nondeterminism of section 7, not the mass model.
* **It still varies with the batch cap** (cap 8: ~5-9e5 s; cap 512:
  ~7.8e6 s), because at `covered ≈ 6e-6` essentially no boundary has
  completed and the figure is driven by XY-timeout *partial* credit,
  whose per-boundary rate depends on how the batches are cut. This is
  the `Hybrid` label doing its job, and it is why the extrapolation
  note above exists.

The honest reading of any n=56 TTC today is "order of magnitude, from a
sample of ~1e-5 of the space, ±3× run to run". Getting a number worth
more than that needs the section 7 nondeterminism fixed and enough
budget for boundaries to actually complete — not a change to the metric.
