# turyn

Searches for **Turyn-type sequences** TT(n) -- four {+1, -1} sequences (X, Y, Z, W) of lengths (n, n, n, n-1) whose combined aperiodic autocorrelations vanish at every nonzero shift. These are building blocks for constructing Hadamard matrices of order 4(3n-1) via the base-sequence → T-sequence → Goethals-Seidel pipeline.

The long-term goal is TT(56), which yields a **Hadamard matrix of order 668**.

## Current results (hybrid SAT solver)

| n | Hadamard | hybrid |
|---|---|---|
| 2 | 20 | 0.6ms |
| 4 | 44 | 0.8ms |
| 6 | 68 | 0.9ms |
| 8 | 92 | 0.8ms |
| 10 | 116 | 1.0ms |
| 12 | 140 | 2.5ms |
| 14 | 164 | 10ms |
| 16 | 188 | 34ms |
| 18 | 212 | 588ms |
| 20 | 236 | 1.0s |
| 22 | 260 | 3.2s |
| 24 | 284 | 1.0s |
| 26 | 308 | **129s** |

Hybrid is now the default mode and runs in parallel across all available cores. Just run `target/release/turyn --n=N` to search. Z/W sequences are cached by sum value across tuples, and a priority queue dispatches spectrally-tightest pairs first.

All solved with **radical**, a pure Rust CDCL SAT solver included as a subcrate. No external C/C++ dependencies. Timeout = 2 minutes wall-clock (except n=26 which takes ~2 min). Stochastic is nondeterministic; times vary between runs.

**Test machine:** 4-core Intel Xeon @ 2.10 GHz, 16 GB RAM, Linux x86_64. Hybrid search parallelizes Phase B + SAT solving across cores via a coordinator with shared priority queue.

For comparison, London (2013) enumerated all 3,523 TT(24) sequences in ~1 hour and all 3,753 TT(26) in ~9 hours on a 6-core Intel i7 3930K @ 3.2 GHz, using a highly optimized custom C++ backtracker. Our hybrid solver finds a single TT(24) in 1.0s and TT(26) in 129s on a slower 4-core machine.

Known solutions exist in the literature for all even n up to 44 (London-Kotsireas 2025). The current bottleneck for n >= 28 is search space size and SAT solver performance at scale.

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
cargo run --release -- --n=24

# Full SAT search (competitive for n <= 18)
target/release/turyn --n=14 --sat

# Z-SAT: DFS generates Z, SAT solves X/Y/W (bypasses spectral pairing)
target/release/turyn --n=14 --z-sat --theta=128 --max-z=50000

# Stochastic search via simulated annealing
target/release/turyn --n=16 --stochastic

# Dump DIMACS CNF for external solvers
target/release/turyn --n=14 --dump-dimacs=tt14.cnf

# Solve a DIMACS file with radical
target/release/radical tt14.cnf

# Benchmark mode
target/release/turyn --n=14 --benchmark=3
```

## Flags

### Search mode (mutually exclusive)

| Flag | Description |
|---|---|
| *(default)* | Hybrid search: Phase B + SAT X/Y, parallelized across cores |
| `--sat` | Full SAT encoding of all four sequences |
| `--z-sat` | DFS generates Z only, SAT solves X/Y/W jointly |
| `--stochastic` | Multi-threaded simulated annealing |
| `--sat-xy` | Legacy alias for hybrid (no-op, hybrid is now default) |

### Problem parameters

| Flag | Default | Description |
|---|---|---|
| `--n=N` | 56 | Problem size (search for TT(n)) |
| `--theta=SAMPLES` | 128 | Number of frequency samples for spectral filtering |
| `--max-z=N` | 200000 | Max Z sequences to enumerate in Phase B |
| `--max-w=N` | 200000 | Max W sequences to enumerate in Phase B |
| `--max-spectral=M` | *(auto)* | Tighter spectral bound (London §5.1, default = (6n-2)/2) |
| `--conflict-limit=N` | 0 | Max SAT conflicts per solve (0 = unlimited) |

### Stochastic options

| Flag | Default | Description |
|---|---|---|
| `--stochastic-secs=SECS` | 10 | Time limit for stochastic search (implies `--stochastic`) |

### Benchmarking

| Flag | Default | Description |
|---|---|---|
| `--benchmark[=REPS]` | 5 | Run REPS times, report mean/median timing |

### Diagnostics and testing

| Flag | Description |
|---|---|
| `--phase-a` | Print sum-tuples only (no search) |
| `--phase-b` | Print Z/W pairs only (no Phase C) |
| `--tuple=x,y,z,w` | Test a specific sum-tuple only |
| `--verify=X,Y,Z,W` | Verify a known solution (comma-separated +/- strings) |
| `--test-zw=Z,W` | Test SAT X/Y solving with known Z,W |
| `--xy-table=PATH` | Load XY boundary table from binary file |

### DIMACS export

| Flag | Description |
|---|---|
| `--dump-dimacs=PATH` | Write the full SAT encoding as a DIMACS CNF file instead of solving |

## Search architecture

The core constraint: find X, Y (length n), Z (length n), W (length n-1) with `N_X(k) + N_Y(k) + 2*N_Z(k) + 2*N_W(k) = 0` for all k = 1..n-1.

### Phase A: Sum-tuple enumeration

Enumerate all integer 4-tuples (x,y,z,w) satisfying `x^2 + y^2 + 2z^2 + 2w^2 = 6n-2`, where x,y,z are even and w is odd. These fix the required sum of each sequence, partitioning the search space. Typically ~100-300 tuples.

### Phase B: Z/W candidate generation + spectral filtering

For each tuple, generate Z and W sequences via DFS (depth-first enumeration of {+1,-1} sequences with the required sum). Each candidate is **spectrally filtered**: compute the power spectrum via FFT and reject sequences whose spectral power exceeds the Parseval budget at any frequency. Then attempt to **pair** Z and W whose combined spectral power stays within budget.

At n >= 28, no Z/W pairs survive the spectral pair filter -- this is the Phase B wall.

### Phase C: X/Y completion

Given a valid (Z,W) pair, find X and Y. Three approaches:

- **SAT X/Y** (default hybrid): Encode X/Y constraints as CNF with totalizer cardinality encoding, solve with radical.
- **SAT X/Y/W** (`--z-sat`): Skip W from Phase B. Generate only Z via DFS + spectral filtering, then SAT-solve X/Y/W jointly. Bypasses the spectral pairing bottleneck entirely.

### Full SAT (`--sat`)

Encode all four sequences as SAT variables with XNOR agree/disagree auxiliaries, totalizer counters for sum and autocorrelation cardinality constraints, and selector variables for the weighted (XY + 2*ZW) decomposition. Best for n <= 20.

### Stochastic (`--stochastic`)

Multi-threaded simulated annealing: random initialization, sum-preserving pair swaps, O(n) incremental defect updates, Luby restarts. Works up to TT(18). Independent of the Phase A/B/C pipeline.

## radical: pure Rust CDCL SAT solver

The `radical/` subcrate is a minimal CDCL (Conflict-Driven Clause Learning) SAT solver written from scratch in Rust, inspired by CaDiCaL. ~1600 lines, zero dependencies, 18 tests.

It ships as both a library (used by turyn) and a standalone binary that reads and solves DIMACS CNF files:

```bash
target/release/radical problem.cnf
# Output: s SATISFIABLE / s UNSATISFIABLE (exit 10/20)
```

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
| Quadratic PB (`sum(a*b) = k`) | ❌ | ✅ |
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
