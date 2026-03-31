# turyn

Searches for **Turyn-type sequences** TT(n) -- four {+1, -1} sequences (X, Y, Z, W) of lengths (n, n, n, n-1) whose combined aperiodic autocorrelations vanish at every nonzero shift. These are building blocks for constructing Hadamard matrices of order 4(3n-1) via the base-sequence → T-sequence → Goethals-Seidel pipeline.

The long-term goal is TT(56), which yields a **Hadamard matrix of order 668**.

## Current results

| n | Best time | Method | Hadamard |
|---|---|---|---|
| 4 | <1ms | full SAT | 44 |
| 6 | <1ms | full SAT | 68 |
| 8 | 1.4ms | full SAT | 92 |
| 10 | 106ms | full SAT | 116 |
| 12 | 792ms | full SAT | 140 |
| 14 | 310ms | full SAT | 164 |
| 16 | 3.9s | full SAT | 188 |
| 18 | 3.7s | full SAT | 212 |
| 20 | 49s | full SAT | 236 |
| 22 | 39s | hybrid | 260 |
| 24 | 3.1s | hybrid | 284 |

All solved with **radical**, a pure Rust CDCL SAT solver included as a subcrate. No external C/C++ dependencies.

Known solutions exist in the literature for all even n up to 44 (London-Kotsireas 2025). The current bottleneck for n >= 26 is SAT solver performance at scale.

## Quick start

```bash
cargo build --release

# Full SAT search (best for n <= 20)
target/release/turyn --n=14 --sat

# Hybrid: Phase B generates Z/W, SAT solves X/Y (best for n=22-24)
target/release/turyn --n=24 --sat-xy --theta=128 --max-z=200000 --max-w=200000 --max-pairs=5000 --k=0

# Z-SAT: DFS generates Z, SAT solves X/Y/W (bypasses spectral pairing)
target/release/turyn --n=14 --z-sat --theta=128 --max-z=50000

# Stochastic search via simulated annealing
target/release/turyn --n=16 --stochastic

# Exhaustive DFS search (original method, small n only)
target/release/turyn --n=8 --theta=64 --max-z=200000 --max-w=200000 --max-pairs=2000

# Benchmark mode (exhaustive or stochastic throughput)
target/release/turyn --n=16 --theta=20000 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=3
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

The `radical/` subcrate is a minimal CDCL (Conflict-Driven Clause Learning) SAT solver written from scratch in Rust, inspired by CaDiCaL. Features:

- Two-watched-literal (2WL) unit propagation
- 1-UIP conflict analysis with clause learning
- Non-chronological backjumping
- VSIDS variable activity heuristic with binary heap
- Phase saving
- Luby restart schedule
- LBD-based learnt clause deletion
- Flat clause storage for fast cloning
- ~600 lines, zero dependencies, 18 tests

## Docs

- `docs/OPTIMIZATION_LOG.md` -- benchmark protocol and change-by-change performance history
- `docs/PROFILING.md` -- how to profile in this environment
- `IDEAS.md` -- experiment log with per-idea measurements (Grok/Gemini contributions credited)

## References

- Kharaghani & Tayfeh-Rezaie (2005). A Hadamard matrix of order 428. *J. Combin. Des.* 13(6), 435-440.
- Best, Djokovic, Kharaghani, Ramp (2013). Turyn-Type Sequences: Classification, Enumeration and Construction. [arXiv:1206.4107](https://arxiv.org/abs/1206.4107)
- London & Kotsireas (2025). New Turyn-type sequences. *Cryptogr. Commun.*
