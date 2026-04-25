Your goal is to improve Turyn search performance, measured by fixed-work
coverage benchmarks and explained through the TTC levers in `docs/TTC.md`.

The long-term target is TT(56). Do not optimize for a single proxy counter
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

## Benchmark Principle

Use fixed-work coverage as the primary signal, not "found a solution" and not
one-off wall-clock runs.

The benchmark target is:

```text
covered_log2_work >= X
```

This means "cover about `2^X` raw-equivalent configurations." The search should
print SAT solutions if it finds them, but it must keep going until the fixed
coverage target is reached.

Primary harness:

```powershell
cargo bench --bench fixed_work_criterion -- --turyn-n=26 --turyn-wz=together --turyn-mdd-k=7 --turyn-cover-log2=34
```

Useful variants:

```powershell
cargo bench --bench fixed_work_criterion -- --turyn-n=26 --turyn-wz=apart --turyn-mdd-k=7 --turyn-cover-log2=34
cargo bench --bench fixed_work_criterion -- --turyn-n=56 --turyn-wz=apart --turyn-mdd-k=10 --turyn-cover-log2=34 --turyn-sat-secs=120
cargo bench --bench fixed_work_criterion -- --turyn-n=56 --turyn-wz=sync --turyn-cover-log2=34 --turyn-sat-secs=120
```

Adjust `--turyn-cover-log2` so samples take long enough to measure but short
enough to repeat. If a sample is sub-second or saturated, increase it. If it
takes too long to iterate, decrease it.

## Session Loop

1. Pick one idea from `IDEAS.md`, or add a new small idea if the file lacks a
   good candidate.

2. State the expected TTC mechanism:

   - **denominator**: shrinks the live search space
   - **rate**: covers the same mass faster
   - **shortfall**: reduces timeout/partial-credit loss
   - **instrumentation**: makes future claims measurable

3. Establish a baseline with the fixed-work Criterion harness. Record:

   - benchmark command
   - median/mean timing from Criterion
   - `Framework search` summary line if useful
   - relevant counters from stderr/stdout if the run prints them

4. Implement the smallest code change that tests the idea.

5. Verify the code path is actually exercised. Do not rely on comments or
   intent. Use grep, direct reads, or targeted assertions/logging.

6. Re-run the same fixed-work benchmark.

7. Decide:

   - Accept only if the change has a statistically credible improvement on the
     fixed-work benchmark and the moved counters match the stated mechanism.
   - Treat anything around 1% as real only if repeated/interleaved runs support
     it. Single-run 1% wins are noise.
   - Reject or keep iterating if the change only improves a proxy counter but
     does not improve fixed-work coverage time.

8. Update `IDEAS.md`:

   - If accepted, mark the idea as accepted and summarize the evidence.
   - If rejected, mark it rejected with the measured reason.
   - If inconclusive, say exactly what additional measurement is needed.

9. If accepted, update `docs/OPTIMIZATION_LOG.md` with:

   - command(s)
   - before/after timing
   - speedup percentage
   - TTC mechanism
   - counters that moved
   - correctness validation

10. Commit only accepted changes. The commit message must include the benchmark
    delta and the mechanism, for example:

    ```text
    MDD: cache boundary spectral prep

    fixed-work n=26 together k=7 2^34: -3.2% median
    mechanism: rate; fewer SolveZ prep allocations
    ```

## Acceptance Bar

Do not commit "in-noise" changes.

Use this rule of thumb:

- `>= 5%` with matching counters: usually acceptable after a sanity rerun
- `2-5%`: rerun/interleave before accepting
- `< 2%`: require strong repeated evidence and very low complexity
- regression or unclear mechanism: reject or keep investigating

For a real 1% improvement, run enough samples to show the confidence interval
clears zero. Do not accept it because one run looked faster.

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

Soundness matters more than speed. A false-UNSAT bug can make TTC look amazing
by crediting work that was never validly ruled out.

For SAT/MDD changes, run at least:

```powershell
cargo test -q -p radical
cargo build -q --workspace
```

When the change touches known TT acceptance paths, also run an affected known-TT
regression or a small search that must find a solution.

If a full workspace test fails for environmental MDD scratch-file reasons,
record the exact failure and still run the narrow tests relevant to your
change.

## Debugging Discipline

When stuck:

1. List every assumption you are making.
2. For each assumption, list the evidence you have from code or measurement.
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

- idea attempted
- files changed
- benchmark command(s)
- before/after result
- accepted/rejected/inconclusive
- validation commands
- commit hash, if committed

If no idea produced a win, leave the repo cleaner than you found it: revert your
own failed code changes, keep only useful documentation/instrumentation updates,
and record the failed experiment in `IDEAS.md`.
