# CLAUDE.md

## Project overview

Turyn-type sequence search engine. Finds TT(n) — four {+1,-1} sequences whose combined aperiodic autocorrelations vanish — for constructing Hadamard matrices.

## Build & run

```bash
cargo build --release
target/release/turyn --n=26          # default hybrid search (uses table for n>=14)
target/release/turyn --n=26 --no-table  # without table (slower)
target/release/turyn --n=8            # auto-skips table for n<14 (table requires n>=2k)
```

### MDD pipeline (recommended for n >= 18)

```bash
# Generate k=10 MDD (one-time, ~2 min, 262 MB)
cargo build --release --bin gen_mdd && target/release/gen_mdd 10

# Search using MDD pipeline
target/release/turyn --n=56 --mdd --mdd-k=10
target/release/turyn --n=26 --mdd --mdd-k=7
target/release/turyn --n=18 --mdd --mdd-k=5
```

The MDD pipeline uses a pull-based 4-stage priority queue:
1. **Boundary** (stage 0): MDD path navigation → sum feasibility check
2. **SolveW** (stage 1): SAT or brute-force W middle generation with spectral filtering
3. **SolveZ** (stage 2): SAT Z with per-frequency spectral constraint + pair check
4. **SolveXY** (stage 3): SAT X/Y solve with boundary config

Workers pull from a dual queue (gold queue for ranked XY items, work queue for stages 0-2). The monitor navigates MDD paths on demand (nanosecond per path, no upfront enumeration).

## Startup: generate XY boundary table

On first run (or if `xy-table-k7.bin` is missing), generate the table:

```bash
cargo build --release --bin gen_table && target/release/gen_table 7 xy-table-k7.bin
```

This takes a few minutes and produces the k=7 boundary table used by the hybrid solver. The table is a pure function of k, not n, so it works for all n >= 14.

## Benchmarking

### MDD pipeline throughput (n=56)
```bash
target/release/turyn --n=56 --mdd --mdd-k=10 --sat-secs=30
```
Current: ~680 xy/s average (high variance 200-1100 due to LCG path ordering).

### MDD pipeline correctness (n=18, should find solution)
```bash
target/release/turyn --n=18 --mdd --mdd-k=5 --sat-secs=10
```
Should find TT(18) in <1s.

### Legacy benchmark (Phase B throughput)
```bash
target/release/turyn --n=16 --theta=20000 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=3
```

### Override thread count
```bash
TURYN_THREADS=8 target/release/turyn --n=56 --mdd --mdd-k=10 --sat-secs=30
```

## Key architecture

- `src/main.rs`: MDD pipeline (4-stage priority queue) + legacy three-phase pipeline
- `radical/src/lib.rs`: Custom CDCL SAT solver with quadratic pseudo-boolean constraints and native spectral constraint
- `src/mdd_zw_first.rs`: ZW-first MDD builder, `build_extension` for runtime boundary extension
- `src/sat_z_middle.rs`: LagTemplate for Z/W SAT solver construction with checkpoint/restore

### MDD pipeline stages
- Monitor thread: navigates MDD paths via LCG permutation, feeds Boundary items on demand
- Workers: pull highest-priority item from dual queue (gold XY items first, then work queue)
- Spectral pair check filters bad (Z,W) pairs before they reach XY SAT
- Brute-force W for small middles (≤20 positions), SAT W for large middles

## Docs

- `docs/OPTIMIZATION_LOG.md`: Measured before/after for every optimization
- `docs/MDD-OPTIMIZATION-LOG.md`: MDD generation optimizations
- `IDEAS.md`: Tried and untried optimization ideas with results
- `toc-ideas.md`: Theory of Constraints analysis of the MDD pipeline
