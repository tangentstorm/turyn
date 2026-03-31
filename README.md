# turyn

Searches for **Turyn-type sequences** TT(n) -- four {+1, -1} sequences (X, Y, Z, W) of lengths (n, n, n, n-1) whose combined aperiodic autocorrelations vanish at every nonzero shift. These are building blocks for constructing Hadamard matrices of order 4(3n-1) via the base-sequence → T-sequence → Goethals-Seidel pipeline.

The long-term goal is TT(56), which yields a **Hadamard matrix of order 668**.

## Current results

| n | Hadamard | full SAT | hybrid | z-sat | stochastic | best |
|---|---|---|---|---|---|---|
| 4 | 44 | 0.7ms | **0.6ms** | 0.5ms | — | hybrid |
| 6 | 68 | 5.8ms | **0.8ms** | 3.4ms | — | hybrid |
| 8 | 92 | 3.1ms | **1.7ms** | 1.9ms | 2.1ms | hybrid |
| 10 | 116 | 23ms | **1.6ms** | 11ms | 9.7ms | hybrid |
| 12 | 140 | 61ms | **8ms** | 81ms | 101ms | hybrid |
| 14 | 164 | 462ms | **40ms** | 851ms | 676ms | hybrid |
| 16 | 188 | 3.9s | **203ms** | 25s | 157ms | hybrid |
| 18 | 212 | 3.8s | **3.1s** | timeout | timeout | hybrid |
| 20 | 236 | 51s | **1.4s** | timeout | timeout | hybrid |
| 22 | 260 | timeout | **32s** | timeout | — | hybrid |
| 24 | 284 | timeout | **4.7s** | timeout | — | hybrid |

Hybrid is now the default mode and runs in parallel across all available cores. Just run `target/release/turyn --n=N` to search.

All solved with **radical**, a pure Rust CDCL SAT solver included as a subcrate. No external C/C++ dependencies. Timeout = 2 minutes wall-clock. Stochastic is nondeterministic; times vary between runs.

**Test machine:** 4-core Intel Xeon @ 2.10 GHz, 16 GB RAM, Linux x86_64. Hybrid search parallelizes Phase B + SAT solving across cores (one thread per sum-tuple). Full SAT and z-sat are currently single-threaded.

For comparison, London (2013) enumerated all 3,523 TT(24) sequences in ~1 hour and all 3,753 TT(26) in ~9 hours on a 6-core Intel i7 3930K @ 3.2 GHz, using a highly optimized custom C++ backtracker. Our hybrid solver finds a single TT(24) in 4.7s on a slower 4-core machine but cannot yet enumerate all solutions or reach n=26 within 2 minutes.

Known solutions exist in the literature for all even n up to 44 (London-Kotsireas 2025). The current bottleneck for n >= 26 is SAT solver performance at scale.

### Benchmarking rules

When regenerating this table:

1. Build once with `cargo build --release`.
2. Run each strategy for each even n from 4 to the largest n where at least one strategy succeeds.
3. Timeout is **2 minutes** wall-clock per run. Record "timeout" for any run exceeding this.
4. Record "—" for strategies known to not apply (e.g., stochastic at very small n where it doesn't converge).
5. Bold the winning time in each row. Record the winning strategy name in the "best" column.
6. Commands per strategy:
   - **hybrid** (default): `target/release/turyn --n=N`
   - **full SAT**: `target/release/turyn --n=N --sat`
   - **z-sat**: `target/release/turyn --n=N --z-sat --theta=128 --max-z=50000`
   - **stochastic**: `target/release/turyn --n=N --stochastic`
7. Times are single-run wall-clock (not benchmark-mode averages). For noisy results, take the median of 3 runs.
8. Continue increasing n past the main table until all strategies timeout, to find the frontier.

## Quick start

```bash
cargo build --release

# Default: hybrid search (best overall, parallelized across cores)
target/release/turyn --n=24

# Full SAT search (competitive for n <= 18)
target/release/turyn --n=14 --sat

# Z-SAT: DFS generates Z, SAT solves X/Y/W (bypasses spectral pairing)
target/release/turyn --n=14 --z-sat --theta=128 --max-z=50000

# Stochastic search via simulated annealing
target/release/turyn --n=16 --stochastic

# Exhaustive DFS search (original method, small n only)
target/release/turyn --n=8 --dfs --theta=64 --max-z=200000 --max-w=200000 --max-pairs=2000

# Benchmark mode
target/release/turyn --n=14 --benchmark=3
target/release/turyn --n=16 --stochastic-secs=10 --benchmark=3
```

## Search architecture

The core constraint: find X, Y (length n), Z (length n), W (length n-1) with `N_X(k) + N_Y(k) + 2*N_Z(k) + 2*N_W(k) = 0` for all k = 1..n-1.

### Phase A: Sum-tuple enumeration

Enumerate all integer 4-tuples (x,y,z,w) satisfying `x^2 + y^2 + 2z^2 + 2w^2 = 6n-2`, where x,y,z are even and w is odd. These fix the required sum of each sequence, partitioning the search space. Typically ~100-300 tuples.

### Phase B: Z/W candidate generation + spectral filtering

For each tuple, generate Z and W sequences via DFS (depth-first enumeration of {+1,-1} sequences with the required sum). Each candidate is **spectrally filtered**: compute the power spectrum via FFT and reject sequences whose spectral power exceeds the Parseval budget at any frequency. Then attempt to **pair** Z and W whose combined spectral power stays within budget.

At n >= 28, no Z/W pairs survive the spectral pair filter -- this is the Phase B wall.

### Phase C: X/Y completion

Given a valid (Z,W) pair, find X and Y. Three approaches:

- **Custom backtracker** (`backtrack_xy`): DFS with autocorrelation bounds pruning. The original method.
- **SAT X/Y** (`--sat-xy`): Encode X/Y constraints as CNF with totalizer cardinality encoding, solve with radical. Proves UNSAT in milliseconds vs hours for the backtracker.
- **SAT X/Y/W** (`--z-sat`): Skip W from Phase B. Generate only Z via DFS + spectral filtering, then SAT-solve X/Y/W jointly. Bypasses the spectral pairing bottleneck entirely.

### Full SAT (`--sat`)

Encode all four sequences as SAT variables with XNOR agree/disagree auxiliaries, totalizer counters for sum and autocorrelation cardinality constraints, and selector variables for the weighted (XY + 2*ZW) decomposition. Best for n <= 20.

### Stochastic (`--stochastic`)

Multi-threaded simulated annealing: random initialization, sum-preserving pair swaps, O(n) incremental defect updates, Luby restarts. Works up to TT(18). Independent of the Phase A/B/C pipeline.

## radical: pure Rust CDCL SAT solver

The `radical/` subcrate is a minimal CDCL (Conflict-Driven Clause Learning) SAT solver written from scratch in Rust, inspired by CaDiCaL. ~700 lines, zero dependencies, 18 tests.

### Feature comparison: radical vs CaDiCaL

| Feature | CaDiCaL | radical |
|---|---|---|
| **Core CDCL** | | |
| Two-watched-literal BCP | ✅ | ✅ |
| Blocker literals in watch lists | ✅ | ✅ |
| 1-UIP conflict analysis | ✅ | ✅ |
| Non-chronological backjumping | ✅ | ✅ |
| VSIDS with activity decay | ✅ | ✅ |
| Phase saving | ✅ | ✅ |
| Learnt clause minimization | ✅ | ✅ |
| LBD-based clause deletion | ✅ | ✅ |
| **Restarts** | | |
| Luby restarts | ✅ | ✅ |
| EMA-based (glucose-style) restarts | ✅ | ❌ |
| Rephasing / target phases | ✅ | ❌ |
| **Preprocessing / Inprocessing** | | |
| Bounded Variable Elimination (BVE) | ✅ | ❌ |
| Subsumption / self-subsumption | ✅ | ❌ |
| Failed literal probing | ✅ | ❌ |
| Vivification | ✅ | ❌ |
| **Clause management** | | |
| Flat clause storage | ✅ | ✅ |
| Tier-based retention (glue ≤ 2/6) | ✅ | ❌ |
| Clause compaction / GC | ✅ | ❌ |
| **Extensions (radical only)** | | |
| Native PB constraints (`sum >= k`) | ❌ | ✅ |
| Assumptions API | ✅ | ✅ |
| Solver cloning (for templates) | ❌ | ✅ |
| Pure Rust, zero C deps | ❌ | ✅ |

Compile with `--features cadical` to use CaDiCaL as the Phase C backend for comparison.

## Docs

- `docs/OPTIMIZATION_LOG.md` -- benchmark protocol and change-by-change performance history
- `docs/PROFILING.md` -- how to profile in this environment
- `IDEAS.md` -- experiment log with per-idea measurements (Grok/Gemini contributions credited)

## References

- Kharaghani & Tayfeh-Rezaie (2005). A Hadamard matrix of order 428. *J. Combin. Des.* 13(6), 435-440.
- Best, Djokovic, Kharaghani, Ramp (2013). Turyn-Type Sequences: Classification, Enumeration and Construction. [arXiv:1206.4107](https://arxiv.org/abs/1206.4107)
- London & Kotsireas (2025). New Turyn-type sequences. *Cryptogr. Commun.*
