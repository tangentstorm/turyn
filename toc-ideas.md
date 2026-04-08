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

### Idea 8: Use brute-force W for SolveW, SAT only for SolveZ — HYBRID
Enumerate W's via brute-force (with spectral filtering), use SAT only for Z (which benefits from the spectral constraint against known W). This combines the old pipeline's W quality with the new pipeline's Z efficiency.

### Idea 9: Adaptive gold queue threshold — EXPECTED: better quality selection
Track the distribution of spectral pair powers in the gold queue. Set acceptance threshold at the 10th percentile (adaptive). Only process items better than 90% of what we've seen.

### Idea 10: Drop the dual-queue, go back to single PQ — EXPECTED: simpler, maybe faster
The dual-queue adds complexity. If spectral ranking doesn't differentiate items (all near bound), the gold queue just adds overhead. A single PQ with stage priority might be faster.

### Idea 11: Tuple-aware priority in gold queue — EXPECTED: find solutions faster
Some tuples are "easier" (fewer valid W's needed, smaller search space). Track which tuples produce solvable items and prioritize those.

### Idea 12: Larger k for better boundary pruning — EXPECTED: fewer but higher-quality boundaries
Larger k means more of the sequence is fixed by the boundary, leaving less for SAT. The MDD prunes more aggressively. For n=18 k=8: boundary is 16 of 18 positions, only 2 free. If the MDD has valid paths, they're very likely solvable.

## Testing Protocol

For each idea:
1. Baseline: current pipeline, `--n=18 --sat-secs=10` (should NOT find solution)
2. Intervention: apply change, same parameters
3. Success criterion: finds TT(18) within 10s
4. Also test: `--n=56 --sat-secs=30` (should maintain 700+ xy/s)
