Your goal is to optimize the "time to cover" metric, so that we can tackle
searching for longer and longer Turyn-type sequences, and eventually find TT(56), which in turn will let us produce an Hadamard matrix of order 668!

Start by running gen_mdd for sizes 5, 6, 7, 8... Then run the divan benchmarks to see how the system performs in the current environment.

Next, review the ideas in the IDEAS file, and update it with new ideas as you go along. Always consider the *evidence* you would need to actually measure whether an idea has impact.

Try to select (or brainstorm) 10 possible improvements during this session.
Document your findings. If none lead to a speedup, try 10 more.

Ideally try to focus on --wz=sync ... It's not the fastest approach we have at the moment, but I feel like it *should* be. :)

## Adding ideas

Add the list of ideas to IDEAS.md. Write each idea as a small change
you could make in a single commit. For each idea, write a brief but
explicit annotation:

- **TTC mechanism**: which lever does it pull?
  - *denominator* — shrinks live_zw_paths (MDD pruning, larger k,
    tighter spectral / sum filters at boundary-gen time) or
    est_total_xy (cross mode).
  - *rate* — speeds up any stage (MDD walk, SolveW, SolveZ, SolveXY)
    so stage_exit[*]/elapsed rises.
  - *shortfall* — reduces XY SAT timeouts so each walked boundary
    contributes a full 1.0 to eff instead of a fraction.
  - *instrumentation* — doesn't change runtime, makes future TTC
    experiments measurable.
- **Detection plan**: which counter(s) should move? Pick from
  stage_exit[0..3], `flow_{w,z,xy}_{decisions,propagations,
  root_forced,free_sum,solves}, flow_xy_{sat,unsat,timeout,
  timeout_cov_micro}, extensions_pruned, live_zw_paths`,
  effective_coverage_metric. If none fit, you may need to add an
  atomic counter as part of the change.

## Working an untested idea

For each untested idea in IDEAS.md:

1. **Establish a clean baseline.** Make sure nothing else is using the
   CPU. Use the benchmark whose lever your idea targets:
   - **MDD-mode TTC** (preferred for any change inside the unified
     pipeline):
     ```
     target/release/turyn --n=26 --wz=apart --mdd-k=7 --sat-secs=60
     target/release/turyn --n=56 --wz=apart --mdd-k=10 --sat-secs=30
     ```
     Record the Time to cover: line **and** the underlying
     eff bnd/s, live ZW paths, XY-timeout %, and per-stage
     pruning block — so the win (or loss) is decomposable.
   - **Cross-mode TTC**:
     ```
     target/release/turyn --n=26 --wz=cross --sat-secs=60
     ```
   - **SAT microbench** (only when the idea is purely inside radical
     and unrelated to the pipeline; rare):
     ```
     target/release/turyn --n=22 --wz=apart --mdd-k=5 --sat-secs=60
     ```
   - **Generation-side benchmarks** (--benchmark=N exhaustive runs)
     are *proxies for rate only* — never accept or reject an MDD-mode
     change on --benchmark numbers alone.

2. **Verify the change actually went in.** Don't trust your own
   description, the docs, or earlier IDEAS.md entries. Confirm with
   grep / Read against src/main.rs, src/sat_z_middle.rs,
   src/mdd_zw_first.rs, or radical/src/lib.rs that the new code
   path is reachable and exercised by the benchmark you ran.

3. **Run the benchmark again.** Compare TTC and the three levers
   (denominator / rate / shortfall) line-by-line.

4. **Iterate while there's headroom.** As long as you can see a way
   to make the same idea pull harder on its lever, implement and
   re-benchmark. Re-profile if you've stalled — propagate,
   recompute_quad_pb, compute_quad_pb_explanation_into,
   solve_inner are the historical hot spots; if your idea moves a
   different one, say so.

5. **Decide.**
   - If TTC dropped clearly and decisively (the change isn't in the
     noise on the relevant benchmark) AND you understand which
     lever moved AND the per-lever decomposition agrees with your
     theory:
     - move the idea to docs/OPTIMIZATION_LOG.md with TTC
       before/after, the lever tag, and the moved counters,
     - report the speedup % and the lever to the user in chat,
     - commit with TTC delta and implementation notes.
   - If the change is "within noise" or only moves xy/s / bnd/s
     without moving TTC: don't commit. Consider whether you missed
     an optimization within the same idea, and don't be afraid to
     pull out the profiler. Sometimes an idea needs two or three
     rounds before it stops fighting itself.
   - If after iteration there's still no TTC win: move to the
     "rejected" / "tried" section of IDEAS.md with the measured
     lever changes (e.g. "+30% rate, –40% denominator, net 0
     TTC") so future readers know which trade-off killed it.

6. **Always note cumulative TTC.** Every commit message should
   reference the running TTC since the start of the session, not
   just the local delta.

## Earn the win

Don't commit "in-noise" changes even when they look like wins on a
single proxy metric. Earn it on TTC. If it wasn't a clear and
decisive win but you still believe in the idea, re-profile and
iterate. Several historically-rejected ideas in this repo (E1
extension check, quad PB, XY dedup) were rejected on bnd/s before
they were accepted on a deeper metric — so don't give up on the
first try, but also don't lower the bar.

## Beware of metric-change opportunities

If you find yourself rejecting an idea because xy/s went down, stop
and check whether it pulled the *denominator* lever instead — fewer
solves per boundary is a TTC win even at lower xy/s. The "boundaries/s
paradigm shift" section in IDEAS.md exists exactly because we kept
making this mistake.

If a benchmark becomes so easy that you can't easily tell whether
the run improved, increase the difficulty (raise n, raise
--sat-secs, lower --mdd-k). Don't try to extract signal from a
TTC of "0s" or a saturated-fast pipeline.

## Debugging discipline

When debugging:

1. **List every assumption you're making**, plus every assumption
   the code seems to be making (look at the comments and the data-
   flow, not just function signatures).
2. **List the evidence you actually have** for each assumption —
   "the docs say so" is not evidence; "I just read line 3458 of
   src/main.rs and saw the call" is. Distinguish carefully.
3. Use the gap between (1) and (2) to decide which assumptions to
   probe first. The unsupported ones are usually wrong.
4. Soundness bugs (e.g. the XOR/QuadPB false-UNSAT chain in Feb
   2026) silently *inflate* TTC by giving full credit to walked-
   but-not-actually-explored boundaries. If a "speedup" makes TTC
   improbably good, suspect soundness before celebrating — re-run
   the known-TT(n) regression tests for the affected n.

