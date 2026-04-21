# radical

A pure-Rust CDCL SAT solver inspired by CaDiCaL, with first-class support
for the non-clausal constraints the Turyn sequence search needs.

`radical` started as a drop-in replacement for the `cadical` crate and
grew native propagators for the constraint families that show up in the
combinatorial-design pipeline upstairs in `turyn`. It is a library first
(`use radical::Solver`) and a CLI second (`radical file.cnf`).

## What's in the box

Standard CDCL core:

- Two-watched-literal unit propagation (with a separate binary fast path)
- 1-UIP conflict analysis with learnt-clause minimization
- Non-chronological backjumping (and optional chronological BT for shallow conflicts)
- VSIDS with a binary-heap decision queue and exponential decay
- Luby restarts by default, optional glucose-style EMA restarts
- LBD-based clause database cleanup (`reduce_db`)
- Phase saving, optional rephasing, optional "lucky phase" trial
- Optional failed-literal probing and clause vivification
- DIMACS parser and `dump_dimacs` for round-tripping

Native constraint propagators (all participate in BCP and conflict
analysis):

| Kind       | What it says                                                |
|------------|-------------------------------------------------------------|
| `Clause`   | ordinary CNF                                                |
| `Pb`       | `Σ cᵢ·ℓᵢ ≥ bound`  (pseudo-boolean at-least)                |
| `QuadPb`   | `Σ cᵢ·ℓᵢ·ℓ'ᵢ ∈ [lo, hi]`  (quadratic PB, two-sided slack)   |
| `PbSetEq`  | `#{i : ℓᵢ true} ∈ V`  for a finite set `V`                  |
| `Xor`      | GF(2) parity: `v₁ ⊕ … ⊕ vₖ = parity`                        |
| `Mdd`      | path feasibility in a multi-valued decision diagram         |
| `Spectral` | `|DFT(sequence)|² ≤ bound` at sampled frequencies           |

The `Spectral` and `Mdd` propagators are what make `radical` useful to
`turyn`: they let the solver rule out partial {+1, −1} assignments whose
DFT magnitudes would exceed an autocorrelation budget, or whose boundary
variables don't correspond to any surviving MDD path, without expanding
those constraints into exponentially many clauses.

Per-propagator statistics are available via
`Solver::propagations_by_kind(PropKind::…)`, which is how the `--wz=sync`
telemetry attributes forcings to each constraint family (see
`docs/TELEMETRY.md` in the parent crate).

## Using it as a library

```rust
use radical::Solver;

let mut s = Solver::new();
s.add_clause([1, 2, -3]);
s.add_clause([-1, 3]);
match s.solve() {
    Some(true)  => println!("SAT, x1 = {:?}", s.value(1)),
    Some(false) => println!("UNSAT"),
    None        => println!("UNKNOWN (conflict budget hit)"),
}
```

Literals are `i32` in DIMACS convention (variables 1-indexed, negation =
negated integer). Beyond `add_clause`, the constraint builders are:

- `add_pb_atleast(lits, coeffs, bound)`
- `add_pb_eq(lits, coeffs, target)`
- `add_pb_set_eq(lits, values)`
- `add_quad_pb_eq(lits_a, lits_b, coeffs, target)`
- `add_quad_pb_range(lits_a, lits_b, coeffs, lo, hi)`
- `add_xor(vars, parity)`
- `add_mdd_constraint(…)`

Spectral constraints are attached directly to the `Solver`'s
`SpectralConstraint` field after construction; see `src/sat_z_middle.rs`
in the parent crate for a worked example.

Incremental use is supported via assumption frames
(`push_assume_frame` / `pop_assume_frame`), `set_conflict_limit`, and
`take_last_learnt_clause` for extracting the final nogood on UNSAT.

### Configuration

`SolverConfig` toggles the optional features. Defaults are conservative
(only XOR propagation is on); the other flags exist because the right
setting depends on the workload — e.g. `bin_watch_fastpath` is a win for
`--wz=sync` but a loss for the per-candidate-clone flows in
`--wz=apart`. See the field docs on `SolverConfig` in `src/lib.rs` for
the measured trade-offs.

## Using it as a CLI

```bash
cargo build --release -p radical
target/release/radical path/to/formula.cnf
```

Output follows the DIMACS competition convention (`s SATISFIABLE` / `s
UNSATISFIABLE` / `s UNKNOWN`, with a `v` line on SAT) and the exit code
is 10 / 20 / 0. Run `radical --help` for the flag list; the flags mirror
`SolverConfig`.

## Layout

```
radical/
├── Cargo.toml
└── src/
    ├── lib.rs    # the solver (core CDCL + all propagators)
    └── main.rs   # DIMACS CLI front-end
```

## Relationship to `turyn`

This crate lives inside the `turyn` workspace and is the SAT backend for
every `--wz` pipeline mode that runs a solver. It does not depend on
anything in `turyn` itself, so it can be pulled into other projects that
need a SAT solver with PB / XOR / MDD / spectral reasoning built in.
