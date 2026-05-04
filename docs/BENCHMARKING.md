# Benchmarking protocol — detecting ~0.2% performance changes

This guide is the methodology we use when an optimization "looks like a small
improvement" but every casual A/B run rejects it as noise. The premise: a
0.2% effect is real and detectable, but only if both (a) your *metric* has a
noise floor well below 0.2% and (b) your *experiment design* has enough
statistical power. Most failed A/B runs miss on (a) — the metric itself
varies more than the effect — so collecting more samples cannot save them.

Read this with [`TTC-CALIBRATION.md`](TTC-CALIBRATION.md) and
[`benchmark-sat.md`](benchmark-sat.md). Those tell you *what* configs to run;
this tells you *how* to compare two binaries.

## TL;DR — the protocol

```bash
# A. Build both binaries
git checkout main          ; cargo build --release          ; cp target/release/turyn /tmp/turyn.A
git checkout my-feature    ; cargo build --release          ; cp target/release/turyn /tmp/turyn.B

# B. Pin everything (single-thread, single tuple shell, fixed work budget,
#    deterministic LCG seed already baked in at compile time)
ENV='TURYN_THREADS=1'
ARGS='--n=18 --wz=apart --mdd-k=5 --conj-tuple --bench-cover-log2=24'

# C. Run alternating pairs on a pinned core, discarding 2 warmups
scripts/bench-pair.sh /tmp/turyn.A /tmp/turyn.B 30   # 30 paired samples

# D. Read the paired-t result. Reject the change if the 95% CI on the
#    relative delta crosses zero, or if the effect doesn't replicate at a
#    second (n, --bench-cover-log2) configuration.
```

The rest of this document explains the four ingredients that make this work.

## 1. Why most A/B comparisons can't see 0.2%

Wall-clock noise floor on a "quiet" Linux desktop is ~0.5–2% per run. Mid-run
TTC variance with `THREADS=1` and a fixed tuple shell is **3–7%** at n=16/18
([`TTC-CALIBRATION.md` §"Ground truth"](TTC-CALIBRATION.md#ground-truth-at-n18-apart-conj-tuple-weighted-threads1)).
End-of-run wall-clock at `covered=1.0` was 0.6–3% across the same runs.

So the cheapest A/B comparison — "run twice, compare TTC at finish" — has a
σ floor in the 1–3% range. To detect a 0.2% effect against σ=1% with 95%
confidence and 80% power, the paired-t formula

$$n \;\approx\; \left(\frac{(z_{0.975} + z_{0.80})\,\sigma}{\delta}\right)^2 = \left(\frac{2.80 \times 1.0\%}{0.2\%}\right)^2 \approx 196$$

says you need **~200 paired samples** per comparison. At σ=3% it's ~1800.
That's why your runs keep coming back "noise."

The fix is *not* to run more — it's to switch to a metric with σ ≤ 0.1%, at
which point ~10 paired samples suffice.

## 2. Choose a metric with the lowest possible noise floor

Pick the *highest* row in this table that your hypothesis can be expressed
in. Going up by one row typically buys you 5–10× less noise.

| Metric | Typical σ | Pros | Cons |
|---|---|---|---|
| Wall-clock TTC mid-run | 3–7% | Universal, mode-agnostic | Drifts, biased by queue tail |
| Wall-clock at `covered=1.0` (`--bench-cover-log2`) | 0.5–3% | True "time to finish fixed work" | Still wall-clock; needs system quieting |
| **Hardware counters (`perf stat -e instructions`)** | 0.05–0.2% | Very low noise; immune to thermal/freq | Needs `perf` |
| **Internal counters at fixed work** | **≈ 0%** (deterministic) | Bit-identical across runs | Only sees changes that move counter values |

The last row is the lever you're missing. Turyn already emits deterministic
counters — every `[framework:apart] flow W/Z/XY ...` line in
`src/main.rs:545–574` is a count. With `TURYN_THREADS=1`, a pinned LCG seed,
and `--bench-cover-log2=X`, **these counts are bit-identical across runs of
the same binary** (verify this once on your box: it's the assumption the
whole protocol rests on).

What this gives you:

* **"Does the optimization change behavior?"** Diff the counter block. If
  conflicts/propagations/stage-exit numbers are identical, the change is a
  pure speed win — measure it with the next-best metric (HW counters or
  wall-clock).
* **"Did we prune more / propagate less?"** The counter delta *is* the
  effect, with zero noise. A 0.2% reduction in `total conflicts` is
  unambiguous.

So the rule is: **for any optimization that's supposed to reduce work, the
primary metric is a deterministic internal counter, not time.** Time is the
fallback for optimizations that change how fast each unit of work runs (data
layout, cache, branch prediction, instruction selection).

### Adding new counters

If the optimization you're testing isn't visible in the existing counter set
(e.g. you cached something and want to see hit/miss rates), add atomic
counters next to the relevant call sites and emit them in the same end-of-run
block. They cost a `fetch_add(_, Relaxed)` and pay back enormously in
benchmarking sensitivity.

## 3. Pin every source of nondeterminism

Single-thread already gets you most of the way. Full checklist:

1. `TURYN_THREADS=1` — defeats scheduler-induced queue ordering (the dominant
   variance source per [`TTC-CALIBRATION.md` §"benchmark configuration"](TTC-CALIBRATION.md#the-benchmark-configuration-that-works)).
2. `--conj-tuple` — single auto-selected tuple shell. Picking different
   tuples is itself a variance source if you forget this.
3. `--bench-cover-log2=<X>` — fixed-work stop. Without this the search exits
   on first solution, and "first solution wall-clock" inherits the variance
   of whichever boundary happened to be in flight.
4. `--continue-after-sat` — implied by `--bench-cover-log2`, but say it
   explicitly when reading scripts.
5. Same `mdd-<k>.bin` on disk for both binaries (they're produced by
   `gen_mdd <k>` — re-running it should be bit-identical, but verify with
   `sha256sum mdd-*.bin` if you're paranoid).
6. SAT solver LCG seed: pinned at compile time
   (`0xDEADBEEF_CAFEBABE`, `mdd_stages.rs:1089`). No flag needed.
7. `--conflict-limit=<N>` if your config can hit it — without a limit, "did
   it time out" can flip across builds and dominate the comparison.
8. Same `--n`, `--wz`, `--mdd-k`, and any `--sat-*` flags.

After step 1–6 a binary should produce **bit-identical stdout** when run
twice on the same machine (modulo timestamps and elapsed-time fields). If it
doesn't, find the leak before benchmarking anything.

## 4. Quiet the system (when wall-clock is the metric)

Steps in roughly decreasing order of impact:

1. **Disable turbo boost** — biggest single source of wall-clock variance on
   modern CPUs. Frequency scales with thermal headroom, which depends on
   neighboring cores and ambient temperature.
   ```bash
   echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo   # Intel
   echo 0 | sudo tee /sys/devices/system/cpu/cpufreq/boost           # AMD
   ```
2. **Lock CPU governor to `performance`**:
   ```bash
   sudo cpupower frequency-set -g performance
   ```
3. **Pin to a single physical core** (avoids sibling SMT contention):
   ```bash
   taskset -c 2 ./turyn ...     # pick a core that isn't core 0
   ```
   On NUMA boxes also use `numactl --cpunodebind=0 --membind=0`.
4. **Disable address space randomization** so cache-line alignment doesn't
   flip between runs:
   ```bash
   setarch "$(uname -m)" -R ./turyn ...
   ```
5. **Disable transparent huge pages** during the run, or fix it `always`.
   Flipping THP states between runs can move 1% of wall-clock around.
   ```bash
   echo never | sudo tee /sys/kernel/mm/transparent_hugepage/enabled
   ```
6. **Quiesce**: stop browser/IDE/cron/Docker daemon/desktop indexer; close
   long-lived terminals; run from a TTY if possible.
7. **Warm caches**: discard the first 1–2 runs. The first run pays for cold
   filesystem cache on `mdd-<k>.bin` and on shared libraries.

These steps only matter when you're stuck with wall-clock or HW-counter time
metrics. If you're comparing internal counters (§2), skip the whole list.

## 5. Experiment design — paired, alternating, with warmups

Even with everything pinned, a "run A 30 times, then B 30 times" comparison
loses to slow drift (thermal, background processes, your laptop deciding to
index something). Always **interleave**:

```
warmup A; warmup B;     # discarded
A; B; A; B; A; B; ...   # 30 paired samples
```

For each pair `i`, compute `delta_i = (B_i - A_i) / A_i`. Report the **mean
of `delta_i`** with a paired-t 95% CI, *not* `mean(B) / mean(A) - 1`. Paired
analysis cancels common-mode drift and gives you ~2× better sensitivity for
free.

If you are using a metric with non-Gaussian tails (wall-clock during a noisy
session can have heavy upper tail), use BCa bootstrap on `delta_i` instead of
paired-t. `scipy.stats.bootstrap` does this in two lines.

**Sample size.** With paired alternation, the effective per-pair σ is the σ
of `delta_i`, which is typically 2–3× smaller than the σ of either run alone:

| Per-pair σ on the metric | Samples to resolve 0.2% (95/80) |
|---|---|
| 1.0% | ~200 |
| 0.3% | ~18 |
| 0.1% | **~3** |
| Counter-deterministic (0%) | **1** |

This is the table to keep on your desk. It tells you whether to invest in
better metrics or in more runs. **Going from a noisy metric to a quiet one
beats running 10× more samples.**

**Min-of-k.** For wall-clock specifically, also report `min(A_i)` vs
`min(B_i)`. Wall-clock has a hard physical lower bound (the work the CPU
must do), and the minimum across runs is the cleanest estimator of it. If
the means agree but the mins disagree by 0.2%, the means are seeing
background noise floor, not the effect.

## 6. Multi-scale replication

A single (n, X) result at 0.2% is one experiment. Before believing it,
require the same direction and roughly the same magnitude at *two* other
configurations:

* `n=16, --bench-cover-log2=20`
* `n=18, --bench-cover-log2=24`
* `n=20, --bench-cover-log2=28`

A real micro-optimization typically scales: it shows up as ~0.2% at all three
scales (or grows with work). A spurious win shows up at one scale and
disappears at the others. This is the cheapest sanity check there is — it
costs you 3× more compute but eliminates ~95% of false positives.

Cross-mode replication (same change, run under `--wz=apart` *and*
`--wz=together`) is also strong evidence when the change is in code that
both modes share.

## 7. Reading the result

Decision rule for accepting a 0.2% improvement:

1. Pre-register the metric and the configurations *before* running B. (If
   you run B first and then go shopping for a metric where it wins, you've
   p-hacked.)
2. Internal-counter metric: a single deterministic run with a non-zero delta
   in the expected direction is sufficient. Verify the delta is consistent
   with your hypothesis (e.g. an "earlier prune" should reduce stage-3
   `flow_xy_solves`, not just `total conflicts`).
3. Wall-clock / HW-counter metric: 95% CI on per-pair `delta_i` excludes 0,
   *and* the same direction holds at ≥2 of 3 multi-scale configurations.
4. If (3) fails on multi-scale but passes on the headline config, the
   optimization is config-specific. That's still useful information — write
   it up as such, don't promote it to a general win.

## 8. A reference `bench-pair.sh`

This is the script the TL;DR refers to. It captures the protocol in code so
you don't have to reconstruct it every time.

```bash
#!/usr/bin/env bash
# Usage: bench-pair.sh <turyn.A> <turyn.B> <pairs>
# Emits TSV: pair, build, wall_s, ttc_s, total_conflicts, xy_solves
set -euo pipefail
A="$1"; B="$2"; N="${3:-30}"
ENV="TURYN_THREADS=1"
ARGS="--n=18 --wz=apart --mdd-k=5 --conj-tuple --bench-cover-log2=24"
PIN="taskset -c 2 setarch $(uname -m) -R"

run() {
  local bin="$1" tag="$2" pair="$3"
  local out
  out=$(env $ENV $PIN "$bin" $ARGS 2>&1)
  local wall ttc conf solves
  wall=$( echo "$out" | awk '/elapsed=/  {for(i=1;i<=NF;i++) if($i~/^elapsed=/){split($i,a,"="); print a[2]+0; exit}}')
  ttc=$(  echo "$out" | awk '/ttc=/      {for(i=1;i<=NF;i++) if($i~/^ttc=/){split($i,a,"="); print a[2]+0; exit}}')
  conf=$( echo "$out" | awk '/Total conflicts/ {print $NF; exit}')
  solves=$(echo "$out" | awk '/flow XY/  {for(i=1;i<=NF;i++) if($i~/^solves=/){split($i,a,"="); print a[2]+0; exit}}')
  printf '%d\t%s\t%s\t%s\t%s\t%s\n' "$pair" "$tag" "$wall" "$ttc" "$conf" "$solves"
}

# Warmup (discarded)
run "$A" warmup_A 0 >/dev/null
run "$B" warmup_B 0 >/dev/null

printf 'pair\tbuild\twall_s\tttc_s\ttotal_conflicts\txy_solves\n'
for i in $(seq 1 "$N"); do
  run "$A" A "$i"
  run "$B" B "$i"
done
```

Pipe the TSV into Python/R for the paired-t. Example one-liner with `awk`
gives a quick sanity check on the relative delta:

```bash
awk -F'\t' 'NR>1 && $2=="A"{a[$1]=$3} NR>1 && $2=="B"{b[$1]=$3}
            END{n=0;s=0;for(i in a){if(i in b){d=(b[i]-a[i])/a[i]; s+=d; n++}}
                printf "mean delta = %.4f%% (n=%d)\n", 100*s/n, n}' results.tsv
```

## 9. Anti-patterns to avoid

* **Comparing different `--wz` modes** as if they were the same benchmark.
  They navigate different state spaces; an optimization that helps `apart`
  may hurt `together`. Always fix the mode.
* **Dropping outliers post hoc** ("ignore that one slow B run"). Either
  pre-register an outlier rule (e.g. trimmed mean at 10%) or report all
  data. Cherry-picking is the easiest way to manufacture a 0.2% effect.
* **One long run instead of many short runs.** A single 30-minute run gives
  you σ=0; you have no idea what the σ would be. Many short runs at fixed
  work give you σ and let you compute a CI.
* **Comparing TTC at first-solution.** First-solution time is a function of
  *which* solution surfaces first, which depends on queue order, which
  depends on threading. Use `--bench-cover-log2` instead.
* **Trusting a 0.2% result that doesn't replicate.** The literature on
  compiler micro-optimizations is full of ~0.2% claims that vanished on a
  different machine. Multi-scale replication (§6) is non-negotiable at this
  effect size.
* **Ignoring counter changes.** If the deterministic counters move at all
  between A and B, the change is not a pure speed optimization — it's also
  a behavior change. Investigate the counter delta before benchmarking
  time.

## 10. When 0.2% is below your noise floor and you can't get there

Sometimes the metric just won't go below ~1% σ — e.g. you're benchmarking
something that requires multi-threaded scheduling, or a genuine wall-clock
behavior that moves with cache state. Options in decreasing order of
preference:

1. Re-express the optimization's prediction as a counter change, even if
   the counter is "instructions retired" via `perf stat -e instructions`.
   Instructions are deterministic up to ASLR and shared-library variation.
2. Run at a longer time horizon (`--bench-cover-log2` two notches higher).
   σ scales as `1/√t`, so 4× longer runs cut σ in half.
3. Stack multiple optimizations into a single A/B and report the joint
   effect. A 2% combined effect is detectable where four separate 0.2%
   effects are not. The cost is you can't attribute the win.
4. Accept that the change is below your detection threshold. Keep it on a
   branch. Revisit when you have a faster machine, a quieter environment,
   or a deterministic counter that captures it.

The honest answer is sometimes "we cannot prove this is a win." That's a
valid result. What this protocol prevents is the opposite failure: rejecting
real wins as noise because the metric wasn't sharp enough.
