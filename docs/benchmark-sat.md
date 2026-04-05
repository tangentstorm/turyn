# SAT Solver Benchmark (n=56 focused)

## Why n=56 is different

At n=56, the search space is so massive that the hybrid approach (Phase B → Phase C)
fails: we can enumerate many Z or many W candidates individually, but we **never find
any spectrally-compatible Z/W pairs**. The spectral pair filter kills everything.

This means hybrid mode is useless at n=56. The only viable approach is `--sat` (or
`--z-sat`/`--w-sat`) which encodes the entire problem into SAT and lets the solver
do the heavy lifting. The SAT solver IS the search at this scale.

## Table setup (required)

Generate the k=7 XY boundary table (one-time, ~few minutes):
```bash
cargo build --release --bin gen_table && target/release/gen_table 7 xy-table-k7.bin
```

This produces a ~1.9GB table with 224K signatures and 67M XY entries.
When `--sat` detects this table, it automatically uses **k=7 cubing** (14 boundary
positions fixed per sequence) instead of k=6 (12). This means:
- Z/W search space: 2^14 = 16384 configs each (vs 4096 at k=6)
- Middle variables per SAT instance: 4 × (56-14) = 168 (vs 176 at k=6)
- XY boundary configs come from the pre-filtered table (O(1) lookup)

## Primary benchmark (n=56 SAT)

```bash
target/release/turyn --n=56 --sat --tuple=8,14,6,1 --sat-secs=120 --conflict-limit=50000
```

**What it measures:** SAT solver performance on genuinely hard Turyn instances.
Each instance encodes all four sequences with 168 middle variables. The
`--conflict-limit=50000` caps individual solves to prevent threads from getting
stuck indefinitely on a single hard instance.

**Baseline (2026-04-05, k=7 table):**
- 48 trivially UNSAT instances (immediate contradiction from boundary constraints)
- 4 threads then stuck on hard instances for remainder of 120s
- All UNSAT so far (no solutions found)

**Key metrics:**
- `SAT solves` — how many instances completed
- `Avg conflicts` — instance difficulty
- `Total conflicts` — raw solver throughput
- Whether any instance is SAT (i.e., a solution exists!)

**Note on conflict limit:** Without `--conflict-limit`, threads get stuck on single
instances for minutes+. The limit ensures progress through the search space. Set it
high enough that a solvable instance would be found (50K+ conflicts) but low enough
to avoid burning all time on one hopeless instance.

## Instance difficulty at n=56

The SAT instances at n=56 are in a fundamentally different regime than n=26:

| | n=26 (k=6) | n=56 (k=7) |
|---|---|---|
| Middle vars per instance | 56 | 168 |
| Avg conflicts (UNSAT) | ~14 | 10K-50K+ |
| Solves/sec | ~160-200 | <1 |
| Z/W configs | 4096 | 16384 |
| XY matches per Z/W | ~90 | ~12 |

At n=26, instances are trivial (14 conflicts). At n=56, each instance is a
genuine hard combinatorial problem where SAT solver optimizations make a real
difference (GJ elimination, clause learning quality, restart strategy, etc).

## Alternative modes

- `--z-sat`: enumerate W, solve Z+X+Y via SAT (3 sequences in SAT)
- `--w-sat`: enumerate Z, solve W+X+Y via SAT
- `--sat`: solve all four sequences via SAT (hardest per instance, most cubing benefit)

All modes benefit from the k=7 table when available.

## n=26 for quick smoke tests

```bash
target/release/turyn --n=26 --sat --tuple=8,8,2,3 --sat-secs=30
```

Useful for verifying correctness and quick regression checks (instances are trivial).
**Not representative of n=56 performance.** An optimization that helps at n=26
may hurt at n=56 and vice versa.

## Tuples for n=56

```
TT(56): 12 tuples (x,y,z,w) satisfying x²+y²+2z²+2w²=334
  (0,18,2,1)  (8,14,6,1)  (2,16,6,1)  (10,12,6,3)
  (8,10,2,9)  (4,14,6,5)  (8,10,6,7)  (4,10,10,3)
  (6,8,6,9)   (0,10,6,9)  (2,4,6,11)  (0,6,10,7)
```

Default benchmark tuple: `8,14,6,1` (small z,w sums → more feasible boundary configs).

## Workflow

1. Always use `--conflict-limit` at n=56 to avoid stuck threads
2. Measure total conflicts processed and instances completed
3. Profile with callgrind on 10-30s runs
4. An optimization that lets the solver prove UNSAT faster or find SAT on a hard
   instance is far more valuable than throughput on trivial instances
