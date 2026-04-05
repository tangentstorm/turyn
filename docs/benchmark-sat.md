# SAT Solver Benchmark

## Primary benchmark (fast iteration)

```bash
target/release/turyn --n=26 --sat --tuple=8,8,2,3 --sat-secs=30
```

**What it measures:** Pure SAT solver throughput on Turyn-type instances.
Encodes all four sequences (X,Y,Z,W) into a single SAT problem per cube,
with k=6 boundary cubing (12 positions fixed, 14 middle variables per sequence = 56 total SAT variables).

**Baseline (2026-04-05, ac7b5cf):**
- Rate: ~163-178 solves/s
- Total conflicts: ~70K in 30s
- Avg conflicts per solve: ~14
- SAT solves: ~4900 (all UNSAT)
- XY matches: ~5000-7000

**Key metrics:**
- `Rate` (solves/s) — primary metric, higher is better
- `Total conflicts` — secondary, measures raw conflict processing speed
- `Avg conflicts` — instance difficulty indicator

**Why n=26:** At n=56, individual SAT instances are too hard (~seconds each)
for fast benchmarking iteration. n=26 gives ~160+ solves/s with enough
conflict depth to exercise CDCL machinery (restarts, learning, propagation).

## Heavyweight benchmark (n=56)

```bash
target/release/turyn --n=56 --sat --tuple=8,14,6,1 --sat-secs=60 --conflict-limit=5000
```

**What it measures:** SAT solver performance on hard instances (176 middle variables).
Each solve runs up to 5000 conflicts before giving up.

**Baseline (2026-04-05):**
- Rate: ~0.7 solves/s
- Avg conflicts: ~2000
- Very slow — use for validation only, not iteration

## Hybrid benchmark (n=56, table-based)

```bash
target/release/turyn --n=56 --tuple=8,14,6,1 --theta=50 --max-spectral=200 --max-z=50000 --max-w=50000 --benchmark=3
```

**What it measures:** Phase C (SAT X/Y solving) with k=7 table lookup.
Requires `xy-table-k7.bin` (generate with `gen_table 7 xy-table-k7.bin`).
Only encodes X/Y middle variables (~42 each = 84 total), much faster per instance.

**Baseline (2026-04-05):**
- mean=35688ms, median=35499ms
- 229 SAT instances per run
- ~7-11 items/s

## Workflow

1. Run primary benchmark before and after each change
2. Accept only clear, decisive improvements (>3% sustained)
3. If primary benchmark becomes too easy (<5s), increase --sat-secs or switch to n=30
4. Use heavyweight benchmark for final validation of accepted changes
