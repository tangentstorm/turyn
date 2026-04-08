# Theory of Constraints Analysis: MDD Pipeline

## The Problem

The unified MDD pipeline (commit 30af1e9) finds TT(12) and TT(16) but FAILS to find TT(18) in 30s, where the old brute-force pipeline finds it in <5s. This is a regression.

### Survey Results

| n  | Old pipeline | MDD pipeline | MDD k |
|----|-------------|-------------|-------|
| 12 | instant     | 40ms        | 4     |
| 14 | instant     | found       | 4     |
| 16 | instant     | found       | 4-5   |
| 18 | <5s         | NOT FOUND   | 4-7   |
| 20 | <20s        | NOT FOUND   | 4-7   |
| 22 | >60s        | NOT FOUND   | 4-7   |
| 56 | N/A (hangs) | 780 xy/s    | 10    |

### Root Cause Analysis

The old pipeline finds solutions because:
1. **Exhaustive W enumeration**: tries ALL valid W sequences per boundary
2. **Spectral pair filtering**: rejects (Z,W) pairs where combined power exceeds bound at ANY frequency
3. **Systematic coverage**: processes all boundaries for each tuple before moving on
4. **Priority by spectral quality**: best (Z,W) pairs processed first

The MDD pipeline fails because:
1. **SAT-based W generation**: finds W's via SAT with random phases — may miss the spectrally-optimal W's
2. **Random MDD walk**: LCG-permuted path indices visit boundaries in arbitrary order
3. **No systematic coverage**: never exhausts all boundaries for a given tuple
4. **W SAT has spectral constraint**: but it only checks individual W spectrum, not the pair quality with Z

### The Constraint (Goldratt Analysis)

The system's throughput is measured in "solutions found per second." The constraint is NOT the XY SAT solver (it's fast at 5800/s for n=18). The constraint is **the quality of (Z,W,boundary) combinations reaching the XY solver**.

Even at 5800 xy/s, if none of the 58K items are solvable, throughput is zero. The system is generating enormous volume of low-quality work.

Analogy: a factory producing 5800 widgets/second, all defective. The bottleneck isn't production speed — it's the quality of raw materials (boundaries + W + Z combinations).

### Phases of the Pipeline

```
Monitor (MDD path) → Boundary → SolveW → SolveZ → SolveXY
          ↓              ↓          ↓        ↓          ↓
     nanoseconds    microseconds  ~1ms     ~1ms      ~0.2ms
     
Quality filter points:
  MDD: boundary autocorrelation constraints (structural)
  W SAT: individual spectral constraint (necessary but not sufficient)
  Z SAT: per-frequency pair bounds against W (good!)
  XY: boundary + zw_autocorr (the final check)
```

The quality degradation happens at:
1. **MDD → Boundary**: random path selection. No preference for "good" boundaries.
2. **W SAT**: finds A valid W, not the BEST valid W. Random phase selection.
3. **Z SAT**: constrained by W's spectrum, but only at 16 frequencies. The full spectral check has θ=128 frequencies.

## Ideas to Try

### Idea 1: Fallback to old pipeline for small n — EXPECTED: find n=18-20
For n < threshold (e.g., n < 40), use the old brute-force pipeline (`run_hybrid_search`). It's proven to work for these sizes. The MDD pipeline is for n=56+ where brute-force W enumeration fails.

### Idea 2: Exhaustive W enumeration in SolveW for small n — EXPECTED: find n=18
When `middle_m` is small enough that brute-force W enumeration is feasible (e.g., C(middle_m, r) < 1M), use `generate_sequences_permuted` instead of SAT. This is what the old pipeline does and it works.

### Idea 3: Sequential MDD walk instead of LCG shuffle — EXPECTED: better coverage
Walk the MDD in DFS order instead of random LCG paths. This ensures systematic coverage of the boundary space and hits all boundaries for each MDD subtree before moving on.

### Idea 4: Increase spectral frequency count in Z solver — EXPECTED: better Z quality
The Z SAT solver uses `num_freqs=16` for the spectral constraint. Increase to 32 or 64. More frequencies = tighter constraint = fewer bad Z's reaching XY.

### Idea 5: Post-hoc spectral pair check before emitting SolveXY — EXPECTED: fewer wasted XY solves
After finding Z, compute `spectral_pair_ok(z_spectrum, w_spectrum, pair_bound)` using the full θ=128 FFT spectrum. Reject pairs that fail. Currently this check is skipped ("Z spectral constraint already enforces pair bounds at 16 frequencies").

### Idea 6: Multiple W's per boundary before moving on — EXPECTED: find better W's
Currently SolveW finds W's sequentially with blocking clauses. For small n, enumerate ALL W's for a boundary, compute pair quality for each, and only emit the best N as SolveZ items.

### Idea 7: Batch boundaries per tuple — EXPECTED: systematic coverage
Instead of interleaving all tuples across random boundaries, process one tuple at a time. Exhaust all boundaries for tuple 0, then tuple 1, etc. This matches the old pipeline's strategy.

### Idea 8: Use brute-force W for SolveW, SAT only for SolveZ — **ACCEPTED**
Brute-force W enumeration for middle_m <= 20 (small problems). SAT for larger.
This matches the old pipeline's proven strategy for small n. Results:
n=22 k=5: FOUND (60s) — NEW! n=56: 1974 xy/s (+10% from ~1800).

### Idea 5: Post-hoc spectral pair check — **ACCEPTED** (critical fix)
Without this, bad (Z,W) pairs flood the XY solver and solutions are never found
for n≥18. Hard pair check for middle_n ≤ 20, skip for larger n (too tight at 16 freqs).
Fixes: n=18 found (<1s), n=20 found, n=56 maintained throughput.

### Idea 3: Sequential MDD walk — **REJECTED**
Sequential walk gets stuck in one MDD region. LCG shuffle is essential for
coverage diversity. n=18 regression when used.

### Idea 9: Adaptive gold queue threshold — EXPECTED: better quality selection
Track the distribution of spectral pair powers in the gold queue. Set acceptance threshold at the 10th percentile (adaptive). Only process items better than 90% of what we've seen.

### Idea 10: Drop the dual-queue, go back to single PQ — **REJECTED**
Single PQ starves the pipeline: stage 3 items always have highest priority, so workers
only do XY SAT and never generate new W/Z items. n=56 dropped from ~1800 to 89 xy/s.
The dual-queue's coinflip mechanism is necessary to balance generation vs consumption.

### Idea 6: Multiple W ranking per boundary — **REJECTED**
W spectral quality as SolveZ sub-priority didn't help. "Better W" doesn't
predict "more likely to produce valid Z." High variance, no clear win.

### Idea 7: Batch boundaries per tuple — **SKIPPED**
More relevant for small n (already working). For n=56 diversity matters more
than deep-diving one tuple. The current interleaved approach is correct.

### Idea 11: Tuple-aware priority in gold queue — **SKIPPED**
Some tuples are "easier" (fewer valid W's needed, smaller search space). Track which tuples produce solvable items and prioritize those.

### Idea 12: Larger k for better boundary pruning — TESTED
Larger k means more of the sequence is fixed by the boundary, leaving less for SAT. The MDD prunes more aggressively. For n=18 k=8: boundary is 16 of 18 positions, only 2 free. If the MDD has valid paths, they're very likely solvable.

## Throughput Optimization Ideas (April 2026)

### Profiling baseline (n=56, k=10, 4 workers, 30s)

Baseline: **2487 xy/s** (commit 90557ce)
After optimizations: **~3700 xy/s** (commit c3fd62c, +458%)

Callgrind profiling shows the SAT solver dominates:
- 34.7% `recompute_quad_pb` — recomputing term states from assigns[]
- 20.1% `propagate` — main BCP loop
- 15.1% `compute_quad_pb_explanation_into` — lazy explanation for conflict analysis
- 11.2% `solve_inner` — CDCL decision/conflict loop
- 7.2% `propagate_pb` — PB constraint propagation
- 4.3% `backtrack` — undoing assignments
- 3.3% `propagate_quad_pb` — quadratic PB propagation/search
- 0.3% `compute_lbd` — LBD computation (allocates Vec per call!)
- 0.6% `malloc/free` — heap allocation overhead

### Idea T1: Eliminate Vec allocation in compute_lbd — use reusable bitset
`compute_lbd` allocates `vec![false; decision_level+1]` on every conflict. Replace with a solver-level reusable buffer (like `analyze_seen`). This is called on every learnt clause.

### Idea T2: SIMD-accelerate recompute_quad_pb inner loop
`recompute_quad_pb` is 34.7% of runtime. The inner loop does: load aa/ab from assigns[], table lookup, accumulate sums[state]. This is a perfect target for SIMD: batch 8 terms at a time, gather aa/ab from assigns[], vectorized table lookup, horizontal sum.

### Idea T3: Reduce stale recomputation by tracking dirty constraint set
`recompute_stale_quad_pb` scans ALL constraints to find stale ones. Replace with an explicit dirty-set (Vec of stale constraint indices). This avoids touching clean constraints during the scan.

### Idea T4: Pack QuadPbTerm tighter — merge var_a/var_b into state byte
Currently QuadPbTerm is 16 bytes. The `state` and `tv_offset` fields are only 1 byte each. Explore whether we can pack the struct to 12 bytes for better cache density in the recompute loop.

### Idea T5: Conflict limit per XY solve — fail fast on hard instances
Many XY SAT instances are UNSAT and take many conflicts to prove. Set a per-instance conflict limit (e.g., 10K conflicts). If exceeded, skip to the next candidate. Most SAT instances resolve quickly; hard ones are unlikely to be SAT anyway.

### Idea T6: Batch recompute_quad_pb with SIMD gather from assigns[]
Instead of per-term `assigns[var_a]` + `assigns[var_b]` (random memory access), sort terms by variable proximity and process in cache-friendly order. Or pre-gather all assigns into a contiguous buffer before the loop.

### Idea T7: Eliminate GJ candidate equalities — use assumptions instead
`gj_candidate_equalities` does Gauss-Jordan on every candidate. This is O(n^3) in worst case. Instead, add the GJ-derived equalities as unit assumptions to the solver, using solve_with_assumptions().

### Idea T8: Skip trivially UNSAT candidates before solver clone
Before cloning the template solver, check if any lag target is out of range (infeasible). The `is_feasible` check exists but could be strengthened with parity and GJ-derived contradictions earlier.

### Idea T9: Cache GJ results by zw_autocorr hash
Many candidates share the same zw_autocorr vector (since Z/W from same boundary have correlated autocorrelations). Cache GJ equalities by autocorr hash to avoid redundant O(n^2) GJ computation.

### Idea T10: Reduce solver clone cost — share immutable clause database
Each XY solve clones the entire template solver. Instead, use a copy-on-write approach: share the immutable initial clause database and only copy mutable state (assigns, trail, activity, etc.).

### Idea T11: Reduce quad PB constraint count — merge lags with same parity
Lags with the same target value could potentially share constraint structures, reducing the number of quad PB constraints the propagator must check.

### Idea T12: Incremental XY solver — add/remove per-candidate constraints
Instead of clone+dispose per candidate, keep a persistent solver and use checkpoint/restore to add/remove the per-candidate quad PB constraints. This avoids the clone overhead entirely.

### Idea T13: Reduce propagate_pb overhead — skip trivially satisfied PB constraints
If a PB constraint's current slack is large (all coefficients are 1 and many vars still free), skip the per-literal propagation check. Track min-slack incrementally.

### Idea T14: Branchless lit_value using lookup table
`lit_value` is called millions of times in propagate. Currently has two branches. Replace with `LBool::from(assigns[v] as u8 ^ (lit < 0) as u8)` or a 6-entry lookup table.

### Idea T15: Avoid re-cloning spectral constraints in Z solver
The Z solver creates a new SpectralConstraint per boundary. Pre-compute the boundary-independent parts and only update the boundary contribution.

### Idea T16: Reduce gold queue lock contention — use lock-free queue
The dual queue uses Mutex<BinaryHeap>. Workers contend on this lock. Use a lock-free concurrent priority queue or per-worker local queues with work-stealing.

### Idea T17: Batch XY boundary walks — emit multiple XY items per Z solve
Currently `walk_xy_sub_mdd` emits XY items one at a time through a closure. Batch them into a Vec and push all at once, reducing lock acquisitions on the work queue.

### Idea T18: Pre-sort quad PB terms by variable index for cache locality
Terms in a quad PB constraint are in lag order, not variable order. Sorting by `var_a` could improve cache locality when accessing `assigns[]` during recompute.

### Idea T19: Eliminate XOR constraint propagation overhead for small n
XOR constraint propagation has a linear scan per variable to find the unassigned var. For small constraints, use a branchless approach or precompute.

### Idea T20: Reduce warm-start overhead — skip clause injection
The warm-start mechanism extracts and injects learnt clauses between solves. Profile whether this actually helps or just adds overhead.

### Idea T21: Reduce template build cost — cache across tuples
SatXYTemplate is built per tuple. If tuples share the same n, the lag_pairs structure is identical. Only the PB targets differ. Share the lag structure and only vary the PB bounds.

### Idea T22: Use smaller data types in SAT solver — u16 for clause indices
If clause count stays under 65K, use u16 for clause metadata indices to improve cache density in watch lists.

### Idea T23: Parallelism tuning — use N-1 workers for pipeline, 1 for monitor
Currently all workers share the pipeline. Dedicate one thread exclusively to feeding boundaries, preventing starvation when all workers are doing XY SAT.

### Idea T24: GJ + quad PB fusion — apply GJ equalities directly to quad PB terms
Instead of adding GJ equalities as extra clauses, fold them into the quad PB constraints by substituting equal variables. This reduces the number of terms in quad PB constraints.

## Testing Protocol

For each idea:
1. Baseline: current pipeline, `--n=18 --sat-secs=10` (should NOT find solution)
2. Intervention: apply change, same parameters
3. Success criterion: finds TT(18) within 10s
4. Also test: `--n=56 --sat-secs=30` (should maintain 700+ xy/s)
