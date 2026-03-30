# turyn

Searches for **Turyn-type sequences** TT(n) -- four {+1, -1} sequences (X, Y, Z, W) of lengths (n, n, n, n-1) whose combined aperiodic autocorrelations vanish at every nonzero shift. These are building blocks for constructing Hadamard matrices of order 2(2n-1).

The long-term goal is TT(56), which yields a **Hadamard matrix of order 668**.

## Quick start

```bash
cargo build --release

# Exhaustive search (small n)
target/release/turyn --n=8 --theta=64 --max-z=200000 --max-w=200000 --max-pairs=2000

# Stochastic search via simulated annealing (larger n)
target/release/turyn --n=14 --stochastic

# Benchmark mode
target/release/turyn --n=16 --theta=256 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=5
```

## Search modes

**Exhaustive** (default): enumerate sum-tuples, generate Z/W candidates with spectral filtering, backtrack for X/Y. Works well up to ~n=16.

**Stochastic** (`--stochastic`): multi-threaded simulated annealing with O(n) incremental defect updates. Finds solutions much faster for moderate n (TT(14) in ~175ms). Needed for scaling toward n=56.

## Docs

- `docs/OPTIMIZATION_LOG.md` -- benchmark protocol and change-by-change performance history
- `docs/PROFILING.md` -- how to profile in this environment
- `IDEAS.md` -- experiment log with per-idea measurements (Grok contributions credited)
