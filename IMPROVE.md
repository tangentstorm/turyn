Your goal is to improve Turyn search performance, measured by fixed-work
coverage benchmarks and explained through the TTC levers in `docs/TTC.md`.

The long-term target is TT(56) — finding it would let us construct a
Hadamard matrix of order 668. Do not optimize for a single proxy counter
unless you can explain why that counter should move TTC.

## First Read

Before changing code, read:

- `docs/TTC.md`
- `IDEAS.md`
- `docs/OPTIMIZATION_LOG.md`
- the relevant code path for the mode you are touching

For MDD modes, start with:

- `src/search_framework/engine.rs`
- `src/search_framework/mode_adapters/mdd_stages.rs`
- `src/mdd_pipeline.rs`
- `src/xy_sat.rs`
- `radical/src/lib.rs` if the idea touches SAT propagation/search

For sync mode, start with:

- `src/search_framework/mode_adapters/sync.rs`
- `src/sync_walker.rs`
- `radical/src/lib.rs`

### Prerequisite: MDD scratch files

Apart/together/cross modes load `mdd-<k>.bin` from the working
directory and panic if it's missing. Before benchmarking with a given
`--mdd-k=K`, ensure `mdd-K.bin` exists; run `target/release/gen_mdd K`
to generate it if it doesn't. `gen_mdd 7` is ~1 MB and <1 min;
`gen_mdd 10` (used at n=56) is ~262 MB and ~2 min.

Sync mode does not use the MDD and skips this step.

## Benchmark Principle

Use **fixed-work coverage** as the primary signal, not "found a solution"
and not one-off wall-clock runs.

The benchmark target is:

```text
covered_log2_work >= X
```

This means "cover about `2^X` raw-equivalent configurations." The search
should print SAT solutions if it finds them, but it must keep going
until the fixed coverage target is reached.

### Primary harness: Criterion fixed-work

```text
cargo bench --bench fixed_work_criterion -- --turyn-n=26 --turyn-wz=together --turyn-mdd-k=7 --turyn-cover-log2=34
```

Useful variants:

```text
cargo bench --bench fixed_work_criterion -- --turyn-n=26 --turyn-wz=apart --turyn-mdd-k=7 --turyn-cover-log2=34
cargo bench --bench fixed_work_criterion -- --turyn-n=56 --turyn-wz=apart --turyn-mdd-k=10 --turyn-cover-log2=34 --turyn-sat-secs=120
cargo bench --bench fixed_work_criterion -- --turyn-n=56 --turyn-wz=sync --turyn-cover-log2=34 --turyn-sat-secs=120
```

Criterion gives confidence intervals out of the box. The acceptance bar
below requires CIs that clear zero; do not try to substitute "5-run mean"
arithmetic on a divan run.

#### Tuning `--turyn-cover-log2`

Adjust so samples take long enough to measure but short enough to repeat.

- If a sample is sub-second or saturated (no signal), **raise**
  `cover-log2` by 4 and rerun.
- If samples take too long to iterate, **lower** `cover-log2` by 2.
- If Criterion still reports a CI wider than ±20 % of the median after
  `cover-log2 ≥ 38`, raise `n` (n=26 → n=56) or lower `mdd-k` instead —
  the bench is saturating early and there's no signal to extract.

### Secondary harnesses (rate proxies — never decide on these alone)

```text
cargo bench --bench turyn_bench       # divan micro-benches
target/release/turyn --n=22 --wz=apart --mdd-k=5 --sat-secs=60
target/release/turyn --n=22 --wz=sync --sat-secs=60
target/release/turyn --benchmark=N --n=...   # legacy exhaustive-search ms
```

These are useful when a change is purely inside a tight inner loop
(e.g. a SAT propagator) and you want to confirm the inner loop got
faster. They measure rate, not TTC. **Never accept or reject an
MDD-mode or sync-mode change on these numbers alone** — fewer SAT
solves per boundary is a TTC win even at lower xy/s, and the legacy
`--benchmark=N` paths can show speedups for ideas that regress TTC.

## Session Loop

1. **Brainstorm a batch.** Skim `IDEAS.md` and add or surface 10
   single-commit candidate ideas before touching any code. Each
   should fit the Idea Format below. The point is to think across
   the search before fixating on the first promising-looking thing,
   and to give yourself a backlog if the first 2-3 don't pan out.

2. **For each idea, state the expected TTC mechanism explicitly:**

   - **denominator**: shrinks the live search space
   - **rate**: covers the same mass faster
   - **shortfall**: reduces timeout/partial-credit loss
   - **instrumentation**: makes future claims measurable

3. **Establish a baseline** with the fixed-work Criterion harness.
   Record:

   - exact benchmark command
   - median and 95 % CI from Criterion
   - `Framework search` summary line if useful
   - relevant counters from stderr/stdout

4. **Implement the smallest code change** that tests the idea.

5. **Verify the code path is actually exercised.** Do not rely on
   comments or intent. Use grep, direct reads, or targeted
   assertions/logging.

6. **Re-run the same fixed-work benchmark.**

7. **Decide:**

   - Accept only if the change has a statistically credible
     improvement on the fixed-work benchmark **and** the moved
     counters match the stated mechanism. CIs should not overlap.
   - Treat anything around 1 % as real only if repeated/interleaved
     runs support it. Single-run 1 % wins are noise.
   - Reject or keep iterating if the change only improves a proxy
     counter but does not improve fixed-work coverage time.
   - **Beware of metric-change traps.** If you find yourself
     rejecting because xy/s went down, stop and check whether it
     pulled the *denominator* lever instead — fewer solves per
     boundary is a TTC win at lower xy/s. The "boundaries/s
     paradigm shift" notes in `IDEAS.md` exist because we kept
     making this mistake.

8. **Update `IDEAS.md`:**

   - If accepted, mark it accepted and summarize the evidence.
   - If rejected, mark it rejected with the measured reason and the
     counter that moved against the theory.
   - If inconclusive, say exactly what additional measurement is
     needed.

9. **If accepted, update `docs/OPTIMIZATION_LOG.md`** with:

   - command(s)
   - before/after timing (median + CI)
   - speedup percentage
   - TTC mechanism
   - counters that moved
   - correctness validation

10. **Commit only accepted changes.** Commit messages must include
    the local benchmark delta, the mechanism, **and the cumulative
    TTC delta from the start of the session** so the optimization
    log stays auditable. Example:

    ```text
    MDD: cache boundary spectral prep

    fixed-work n=26 together k=7 2^34: -3.2% median (95% CI -2.5%/-3.9%)
    cumulative session TTC: -8.1% (3 commits)
    mechanism: rate; fewer SolveZ prep allocations
    ```

11. **End-of-batch decision.** If none of the 10 ideas in this
    batch produced a TTC win, brainstorm another 10 before giving
    up. Several historically-rejected ideas in this repo (E1
    extension check, quad PB, XY dedup) were rejected on bnd/s
    before being accepted on a deeper metric — don't quit on one
    failed batch, but also don't lower the bar.

## Measurement Discipline

Many "wins" recorded in `IDEAS.md` and `docs/OPTIMIZATION_LOG.md` were
rendered on shared rigs whose run-to-run wall-clock CV is **8–30 %**.
A naive 5-run mean cannot distinguish a 1 % effect from thermal jitter
on those rigs.  Two principles keep small wins honest:

1. **Wall-clock is the sanity check, not the verdict.**  Prefer
   deterministic counters (see below) as the primary signal.  The
   verdict is "the counter moved by the right amount in the right
   direction"; wall-clock is "and the change also did not regress
   sample time".
2. **When wall-clock *is* the verdict, use paired interleaved
   samples**, not independent baselines.  Random noise inside one
   sample cancels at the pair-level even when each sample's CV is
   large.

### Deterministic-by-default RNGs

`--seed=N` (default `0`) feeds every per-stage xorshift state, the
sync walker's per-worker shuffle seed, and the stochastic-mode RNG.
With a fixed `--seed`, the order of boundaries dispatched by the
walker is the same across before/after binaries, so the only
remaining source of cross-run variation is parallel-dispatch jitter
(which affects *which worker handled which boundary*, not the
totals).  Counter ratios at fixed-work coverage stop are then
stable to within a fraction of a percent across reruns of the
same binary.

When evaluating a change, report at least one of:

- a counter ratio that the change is supposed to move
  (e.g. `flow_xy_decisions / flow_xy_solves`,
  `flow_xy_root_forced / flow_xy_solves`,
  `flow_z_propagations / flow_z_solves`); or
- a counter total at fixed-work coverage stop (e.g. `flow_xy_solves`
  at `bench-cover-log2 = 40`).

Both should be measured at `--seed=0` (or any other fixed seed) on
both the before and after binaries.

### Paired interleaved benchmark

For wall-clock comparisons, build the before and after binaries
side-by-side and run alternating samples on the same idle box:

```bash
cp target/release/turyn /tmp/turyn_after          # after building "after"
git stash && cargo build --release --bin turyn
cp target/release/turyn /tmp/turyn_before
git stash pop && cargo build --release --bin turyn

echo "pair,before,after" > /tmp/paired.csv
for i in $(seq 1 20); do
  bs=$( { time /tmp/turyn_before search --n=26 --wz=together --mdd-k=7 \
            --bench-cover-log2=40 --sat-secs=120 --seed=0 > /dev/null 2>&1; } \
        2>&1 | grep real | awk '{print $2}')
  as=$( { time /tmp/turyn_after  search --n=26 --wz=together --mdd-k=7 \
            --bench-cover-log2=40 --sat-secs=120 --seed=0 > /dev/null 2>&1; } \
        2>&1 | grep real | awk '{print $2}')
  echo "$i,$bs,$as" | tee -a /tmp/paired.csv
done
```

Then evaluate `(after - before)` *per pair*, not the marginal
medians.  Even on a rig with 10 % marginal CV, 20 paired samples
typically detect a 1 % effect with 95 % CI clearing zero, because
inter-pair drift cancels.

A long single-sample wall-clock comparison ("baseline vs after,
both 5 runs") only stays honest at large effect sizes — `≥ 5 %` if
the marginal CV is `≈ 10 %`.

### Tuning sample length on a noisy rig

When the marginal CV stays above 10 % even with `cover-log2 = 40`,
the rig itself is the bottleneck.  Options in rough cost order:

1. Run the bench at a quieter time (no other CPU contention).
2. Pin the binary to specific cores (`taskset -c 0-3`).
3. Raise `cover-log2` by 4 (each step roughly doubles the per-sample
   work, halving the relative noise of fixed cold-start overhead).
4. Switch from a wall-clock harness to a counter ratio.

`cover-log2 = 44` typically gives one ~60 s sample at n=26, which is
long enough that even shared-machine noise drops below 5 % CV.

## Acceptance Bar

Do not commit "in-noise" changes.

- `>= 5 %` with matching counters and non-overlapping CIs:
  acceptable after a sanity rerun.
- `2-5 %`: rerun/interleave before accepting; need overlapping
  evidence from at least 2 independent benchmark profiles **or** a
  paired-interleaved run with the per-pair delta CI clear of zero.
- `< 2 %`: not acceptable on wall-clock alone.  Require either
  a deterministic counter movement of the predicted shape **or** a
  paired-interleaved run of `≥ 30` pairs with the per-pair delta
  CI clear of zero.
  A 1 % real win needs enough samples that the CI clears zero —
  don't accept it because one run looked faster.
- regression or unclear mechanism: reject or keep investigating.

### Counter-driven acceptance (preferred for sub-2 % wins)

State the predicted counter movement *before* implementing the
change.  After implementing, run with `--seed=0` and confirm the
predicted counter moved by the predicted amount in the predicted
direction.  If it did and wall-clock is in noise, the win is real
but small; record both the counter delta and the wall-clock-noise
verdict.  Compounding several "real but small" wins is one of the
ways the search has historically improved at sizes where each
individual lever was sub-percent.

### Suspicious wins: improbably-good TTC suggests a soundness bug

If a change makes TTC implausibly good — order-of-magnitude jumps
without a corresponding mechanism — suspect soundness before
celebrating. False-UNSAT bugs silently *inflate* TTC by giving
full credit to walked-but-not-actually-explored boundaries. The
February 2026 XOR/QuadPB false-UNSAT chain is the canonical example.

Mitigation: re-run the known-TT(n) regression for any `n` the change
touches:

```text
target/release/turyn --n=18 --wz=sync --sat-secs=30
target/release/turyn --n=22 --wz=apart --mdd-k=5 --sat-secs=20
target/release/turyn --n=24 --wz=together --mdd-k=8 --sat-secs=30
```

These should still report `found_solution=true` for the n's where TT(n)
exists and is reachable in the budget. If they don't, the speedup is
fake.

## Idea Format

When adding ideas to `IDEAS.md`, write each as a one-commit experiment:

```markdown
### Idea: short name

- **Change**: concrete code change.
- **TTC mechanism**: denominator | rate | shortfall | instrumentation.
- **Expected counters**: exact counters or measurements that should move.
- **Benchmark**: exact fixed-work command.
- **Risk**: soundness, memory, determinism, or complexity risk.
- **Status**: untested | accepted | rejected | inconclusive.
```

Counters to consider:

- `stage_exit[0..3]`
- `flow_{w,z,xy}_{decisions,propagations,root_forced,free_sum,solves}`
- `flow_xy_{sat,unsat,timeout,timeout_cov_micro}`
- `flow_w_timeout`
- `flow_z_timeout`
- `extensions_pruned`
- `live_zw_paths`
- `covered_mass`
- fixed-work sample time

If no existing counter fits the idea, add instrumentation as part of the
experiment.

## Correctness Discipline

Soundness matters more than speed. A false-UNSAT bug can make TTC look
amazing by crediting work that was never validly ruled out.

For SAT/MDD changes, run at least:

```text
cargo test -q -p radical
cargo build -q --workspace
```

When the change touches known TT acceptance paths, also run an affected
known-TT regression or a small search that must find a solution (see
the "improbably-good" mitigation list above).

If a full workspace test fails for environmental MDD scratch-file reasons
(e.g. `mdd-9.bin` not present), record the exact failure and still run
the narrow tests relevant to your change.

## Debugging Discipline

When stuck:

1. List every assumption you are making, plus every assumption the code
   appears to be making (look at comments and data flow, not just
   function signatures).
2. For each assumption, list the evidence you actually have — "the docs
   say so" is not evidence; "I just read line 3458 of `src/main.rs` and
   saw the call" is.
3. Probe the unsupported assumptions first.
4. Re-profile only after you have a reproducible benchmark case.

Historical hot spots include:

- SAT propagation
- `recompute_quad_pb`
- `compute_quad_pb_explanation_into`
- `solve_inner`
- MDD boundary setup and SolveZ preparation

## Output At The End Of Each Tick

Report:

- ideas brainstormed this batch
- ideas attempted (with each one's accepted/rejected/inconclusive verdict)
- files changed
- benchmark command(s) and before/after numbers
- validation commands run
- commit hashes for accepted ideas
- cumulative TTC delta since the start of the session

If no idea produced a win, leave the repo cleaner than you found it:
revert your own failed code changes, keep only useful documentation /
instrumentation updates, and record the failed experiment in `IDEAS.md`
so the next session doesn't retry the same dead end.
