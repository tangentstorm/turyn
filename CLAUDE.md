# CLAUDE.md

## Project overview

Turyn-type sequence search engine. Finds TT(n) — four {+1,-1} sequences whose combined aperiodic autocorrelations vanish — for constructing Hadamard matrices.

## Build & run

```bash
cargo build --release
target/release/turyn --n=26          # default hybrid search (needs table)
target/release/turyn --n=26 --no-table  # without table (slower)
```

## Startup: generate XY boundary table

On first run (or if `xy-table-k7.bin` is missing), generate the table:

```bash
cargo build --release --bin gen_table && target/release/gen_table 7 xy-table-k7.bin
```

This takes a few minutes and produces the k=7 boundary table used by the hybrid solver. The table is a pure function of k, not n, so it works for all n >= 14.

## Benchmarking

Primary benchmark (Phase B throughput):
```bash
target/release/turyn --n=16 --theta=20000 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=3
```

For n=24 optimization work:
```bash
time target/release/turyn --n=24
```

## Key architecture

- `src/main.rs`: Three-phase pipeline (A: tuple enum, B: Z/W gen+spectral, C: SAT X/Y)
- `radical/src/lib.rs`: Custom CDCL SAT solver with quadratic pseudo-boolean constraints
- Phase C (SAT) dominates runtime at n >= 22 (90%+)

## Docs

- `docs/OPTIMIZATION_LOG.md`: Measured before/after for every optimization
- `IDEAS.md`: Tried and untried optimization ideas with results
