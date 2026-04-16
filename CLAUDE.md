# CLAUDE.md

## Project overview

Turyn-type sequence search engine. Finds TT(n) — four {+1,-1} sequences whose combined aperiodic autocorrelations vanish — for constructing Hadamard matrices.

## Build & run

```bash
cargo build --release
target/release/turyn --n=26               # default (--wz=cross)
target/release/turyn --n=18 --mdd-k=5     # shorthand for --wz=apart --mdd-k=5
```

### Producer modes (`--wz`)

All three modes load the same `mdd-<k>.bin` for XY boundary enumeration
and feed the same `SolveXyPerCandidate` XY SAT fast path. They differ
only in how they generate the `(Z, W)` candidate pairs:

```bash
target/release/turyn --n=26 --wz=cross                 # default: brute-force Z × W, SpectralIndex match
target/release/turyn --n=26 --wz=apart    --mdd-k=7    # MDD walker + SolveW → SolveZ
target/release/turyn --n=26 --wz=together --mdd-k=7    # MDD walker + combined W+Z SAT
```

The `--wz=apart|together` modes use a pull-based 4-stage priority queue:
1. **Boundary** (stage 0): MDD path navigation → sum feasibility check
2. **SolveW** (stage 1): SAT or brute-force W middle generation with spectral filtering
3. **SolveZ** (stage 2): SAT Z with per-frequency spectral constraint + pair check
4. **SolveXY** (stage 3): XY SAT solve via `SolveXyPerCandidate::try_candidate`

Workers pull from a dual queue (gold queue for ranked XY items, work queue for stages 0-2). The monitor navigates MDD paths on demand (nanosecond per path, no upfront enumeration).

## Startup: generate the MDD

On first run (or if `mdd-<k>.bin` is missing), generate the MDD:

```bash
cargo build --release --bin gen_mdd && target/release/gen_mdd 7    # for --wz=cross (hardcoded k=7)
target/release/gen_mdd 10                                          # for --wz=apart|together at larger n
```

`mdd-<k>.bin` is the only on-disk artifact the search needs. `gen_mdd 7` is ~1 MB and <1 min; `gen_mdd 10` is ~262 MB and ~2 min.

## Benchmarking

### `--wz=apart|together` throughput (n=56)
```bash
target/release/turyn --n=56 --wz=apart --mdd-k=10 --sat-secs=30
```
Current: ~680 xy/s average (high variance 200-1100 due to LCG path ordering).

### Correctness smoke test (n=18, should find solution)
```bash
target/release/turyn --n=18 --wz=apart --mdd-k=5 --sat-secs=10
```
Should find TT(18) in <1s.

### Override thread count
```bash
TURYN_THREADS=8 target/release/turyn --n=56 --wz=apart --mdd-k=10 --sat-secs=30
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
- `docs/CANONICAL.md`: Turyn symmetry group (T1..T4) and BDKR 2012 canonicalization rules (i..vi). Summarizes what the code currently enforces (rule i) and TODO encodings for rules (ii..vi).
- `IDEAS.md`: Tried and untried optimization ideas with results
- `toc-ideas.md`: Theory of Constraints analysis of the MDD pipeline
