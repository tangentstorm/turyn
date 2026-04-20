# turyn

Searches for **Turyn-type sequences** TT(n) — four {+1, -1} sequences
(X, Y, Z, W) of lengths (n, n, n, n-1) whose combined aperiodic
autocorrelations vanish at every nonzero shift. These are building blocks
for constructing Hadamard matrices of order 4(3n-1) via the
base-sequence → T-sequence → Goethals-Seidel pipeline.

The long-term goal is **TT(56)**, which yields a Hadamard matrix of order 668.

## Quick start

```bash
cargo build --release

# One-time: generate the MDD boundary tables the default mode needs.
# k=5 is small (~10 KB, <1s); k=7 is ~220 KB (<1s); k=10 is ~260 MB (~2 min).
target/release/gen_mdd 5
target/release/gen_mdd 7
target/release/gen_mdd 10

# Default: --wz=together with auto-selected mdd-k, parallel across all cores.
target/release/turyn --n=26

# Other producers for the same XY SAT fast path:
target/release/turyn --n=26 --wz=cross                 # brute-force Z × W
target/release/turyn --n=26 --wz=apart --mdd-k=7       # MDD walker, SolveW → SolveZ
target/release/turyn --n=26 --wz=together --mdd-k=7    # MDD walker, combined W+Z SAT
target/release/turyn --n=56 --wz=apart --mdd-k=10 --sat-secs=60

# Unified 4-sequence walker — no MDD file needed:
target/release/turyn --n=18 --wz=sync --sat-secs=30

# Stochastic local search (simulated annealing), works up to TT(18):
target/release/turyn --n=16 --stochastic
```

Run `target/release/turyn -h` for the full flag list (problem parameters,
tuning knobs, debugging helpers).

## Search architecture

The core constraint: find X, Y (length n), Z (length n), W (length n-1)
with `N_X(k) + N_Y(k) + 2·N_Z(k) + 2·N_W(k) = 0` for all k = 1..n-1.

### Phase A — sum-tuple enumeration

Enumerate integer 4-tuples `(x, y, z, w)` satisfying
`x² + y² + 2z² + 2w² = 6n − 2`, where x, y, z are even and w is odd. These
fix the required sum of each sequence. Typically ~100-300 tuples per n.

### Producer modes (`--wz`)

All four modes feed into the same XY SAT fast path
(`SolveXyPerCandidate::try_candidate`); they differ only in how the
(Z, W) candidate pairs are generated.

- **`--wz=cross`** — brute-force full Z × full W with spectral filtering
  on each side, cross-matched via a `SpectralIndex`. No MDD needed.
- **`--wz=apart`** — MDD boundary walker + two-stage SAT (SolveW → SolveZ).
  Loads `mdd-<k>.bin`. Recommended for large n.
- **`--wz=together`** — MDD boundary walker + a single combined W+Z SAT
  call (one solve produces both middles). Default when an MDD file exists.
- **`--wz=sync`** — unified 4-sequence heuristic walker with a persistent
  CDCL SAT solver. No MDD file needed. Builds a bouncing-order walker
  on the fly, enforces BDKR rules (i)–(vi), and scores candidates by
  autocorrelation pressure. See `docs/PIPELINE.md#wzsync` and
  `docs/TELEMETRY.md`.

The `apart|together` modes use a 4-stage pull-based priority queue:

1. **Boundary** (stage 0) — MDD path navigation + sum feasibility check.
2. **SolveW** (stage 1) — SAT or brute-force W middle generation,
   spectrally filtered.
3. **SolveZ** (stage 2) — SAT Z with per-frequency spectral pair
   constraint.
4. **SolveXY** (stage 3) — XY SAT via `SolveXyPerCandidate`.

### radical — pure Rust CDCL SAT solver

The `radical/` subcrate is a custom CDCL SAT solver with three extensions
that matter to the Turyn pipeline:

- **Quadratic PB constraints** (`sum(x_i · x_j) = k`) — directly encodes
  the agree-count form of autocorrelation without XNOR auxiliary variables.
- **Native spectral constraint** — per-frequency Parseval budget
  `|Z(ω)|² ≤ pair_bound − |W(ω)|²`, enforced during CDCL propagation.
- **Assumptions API with persistent learnt clauses** across candidates.

Zero C dependencies, ~3500 lines, standalone DIMACS binary
(`target/release/radical problem.cnf`). Compile with
`--features cadical` to swap in CaDiCaL for the standalone `--sat`
encoding; the live pipeline still uses radical because CaDiCaL cannot
express the quadratic PB / spectral / MDD propagators.

## Benchmarking

### Correctness smoke test (finds TT(18) in <1 s)

```bash
target/release/turyn --n=18 --wz=apart --mdd-k=5 --sat-secs=10
```

### Time-to-cover throughput (n=56, primary optimisation metric)

```bash
target/release/turyn --n=56 --wz=apart --mdd-k=10 --sat-secs=30
```

The "Time to cover" (TTC) line is the headline metric —
`(live_zw_paths − eff) / (eff/elapsed)`, i.e. the wall-clock time a run
would need to fully cover the search space at the observed rate. See
`IDEAS.md` for the TTC denominator/rate/shortfall decomposition used to
evaluate optimisations, and `docs/OPTIMIZATION_LOG.md` for the
measured before/after of every accepted change.

### Divan harness (reproduces the TTC-by-n table)

```bash
cargo bench --bench turyn_bench                 # TT(4)..TT(24)
cargo bench --bench turyn_bench -- tt26         # standalone TT(26)
```

The harness auto-builds release binaries and generates every `mdd-{1..5}.bin`
table it needs. It parses the `Time to cover` line from each run and
prints a cross-size TTC summary after divan's wall-clock table.

### Override thread count

```bash
TURYN_THREADS=8 target/release/turyn --n=56 --wz=apart --mdd-k=10 --sat-secs=30
```

## Docs

- `docs/PIPELINE.md` — overview of all four `--wz` modes and shared building blocks.
- `docs/TELEMETRY.md` — reader's guide to `--wz=sync` output.
- `docs/OPTIMIZATION_LOG.md` — measured before/after for every accepted optimisation.
- `docs/MDD-OPTIMIZATION-LOG.md` — MDD generation optimisations.
- `docs/CANONICAL.md` — Turyn symmetry group (T1..T4) and BDKR canonical form.
- `docs/PROFILING.md` — how to profile in this environment.
- `IDEAS.md` — experiment log with per-idea TTC measurements.
- `docs/TTC.md` — per-`--wz` TTC formulas and the uniform TTC contract.

## References

- Kharaghani & Tayfeh-Rezaie (2005). A Hadamard matrix of order 428.
  *J. Combin. Des.* 13(6), 435-440.
- Best, Djokovic, Kharaghani, Ramp (2013). Turyn-Type Sequences:
  Classification, Enumeration and Construction.
  [arXiv:1206.4107](https://arxiv.org/abs/1206.4107)
- London (2013). *Constructing New Turyn Type Sequences, T-Sequences and
  Hadamard Matrices*. PhD thesis, UIC.
- London & Kotsireas (2025). New Turyn-type sequences. *Cryptogr. Commun.*
