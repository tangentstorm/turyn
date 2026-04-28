# Carrier-Refactor Blockers

This document tracks the state of the function-typed carrier refactor
described in `~/.claude/plans/abundant-toasting-kitten.md`. The branch
is `carrier-refactor-fin-fn`.

## Goal recap

Eliminate `Turyn/GSArrayBridge.lean` by changing all sequence carriers
(`PmSeq n`, `SignSeq n`, `TSequence m`) from list-based to function-typed
`Fin n → Int`. After the refactor, the same carrier shape runs end-to-end
through the GS pipeline.

## Status

| Phase | File | Status | Build |
|---|---|---|---|
| 1 | `Turyn/Defs.lean` | DONE — incl. `lookupNat_of_lt/_of_ge/_eq_apply` simp lemmas | green |
| 2 | `Turyn/TurynType.lean` | DONE (with `toList`/`ofList` shims) | green |
| 3 | `Turyn/BaseSequence.lean` | DONE | green |
| 3+ | `Turyn/BaseSequence.lean` (Phase-4 building blocks) | DONE — see "Phase-4 foundations" below | green |
| 4 | `Turyn/Equivalence.lean` | NOT STARTED — proof rewrites only (foundations are in `BaseSequence.lean`) |
| 5 | `Turyn/XY.lean` | NOT STARTED — 564 lines, mostly mechanical |
| 6 | `Turyn/TSequence.lean` | NOT STARTED — 535 lines, redefine `TSequence`, `step2*` |
| 7 | `Turyn/GSArrayBridge.lean` | NOT STARTED — to be deleted |
| 8 | `Turyn/GoethalsSeidel.lean` | NOT STARTED — absorb survivors |
| 9 | `Turyn/Hadamard.lean` | NOT STARTED — should compose if 6+8 are right |
| 10 | `Turyn/Examples.lean` | NOT STARTED — `native_decide` regression risk |
| 11 | `Turyn/Energy.lean` | NOT STARTED — sums become `Finset.univ : Finset (Fin n)` |

Approximate proof-script work remaining: **~1200 lines** (Phase 4 step
proofs are the bulk; Phase 6 redefinition is next-largest).

## Phase-4 foundations (now in `Turyn/BaseSequence.lean`)

All the building blocks the eventual `Turyn.Equivalence` rewrite needs
to consume are pre-landed in `BaseSequence.lean`:

- **Function-typed primitives:** `negSeqFn`, `appendFn`, `Turyn.altSeqFn`, `reverseFn`
- **`AllPmOne` preservation:** `negSeqFn_AllPmOne`, `AllPmOne_appendFn`, `AllPmOne_altSeqFn`, `AllPmOne_reverseFn`
- **Autocorrelation invariance kernel:** `aperiodicAutocorr_negSeqFn`, `aperiodicAutocorr_altSeqFn`, `aperiodicAutocorr_reverseFn`
- **Vanishing preservation (10 lemmas):** `Turyn.vanishing_negX/Y/Z/W`, `vanishing_revX/Y/Z/W`, `vanishing_altAll`, `vanishing_swapXY`
- **`PmSeq` operation wrappers:** `PmSeq.neg/.reverse/.alt` + `PmSeq.neg_data/.reverse_data/.alt_data` (simp)
- **Elementary-move constructors (10):** `TurynType.doNegX/Y/Z/W`, `doRevX/Y/Z/W`, `doAltAll`, `doSwap`
- **Equivalence machinery:** `Turyn.Elementary` inductive, `Turyn.Equivalent`, `Elementary.toEquivalent`, `equivalent_trans`

Plus utility simp lemmas in `Turyn/Defs.lean`:
- `lookupNat_of_lt`, `lookupNat_of_ge`, `lookupNat_eq_apply`

## What was done this session

### Phase 1: `Turyn/Defs.lean` (commit `de36bd1`)

- `AllPmOne {n : Nat} (a : Fin n → Int)` predicate replaces list-based version.
- `AllSignOne` likewise.
- `aperiodicAutocorr {n : Nat} (a : Fin n → Int) (s : Nat) : Int` —
  uses a new helper `lookupNat : (Fin n → Int) → Nat → Int` that returns
  `0` for out-of-range `i`. The sum body is
  `∑ i ∈ range (n - s), lookupNat a i * lookupNat a (i + s)`.
- `combinedAutocorr {n m : Nat} (x y z : Fin n → Int) (w : Fin m → Int) (s : Nat)`
  takes two distinct lengths because `W` has length `n - 1`.
- `PmSeq n := { data : Fin n → Int, pm : AllPmOne data }` — `len` field removed
  (the `Fin n` carrier knows its own length).
- `SignSeq n := { data : Fin n → Int, sign : AllSignOne data }`.
- `xAt/yAt/zAt/wAt` use `lookupNat S.X.data (i - 1)`.
- All `Canonical1..6/Canonical` predicates unchanged.

### Phase 2: `Turyn/TurynType.lean` (commit `de36bd1`, then refined)

- Renamed list-based predicates to `AllPmOneList` / `AllSignOneList` and
  kept their decidability/Boolean machinery for parsing input strings.
- Added `PmSeq.ofList` / `SignSeq.ofList` constructors that take a list of
  the right length and produce a function-typed `PmSeq` / `SignSeq` via a
  helper `listToFin`. Used downstream to build `pm! "..."` literals.
- Added `PmSeq.toList` / `SignSeq.toList` (`List.ofFn s.data`) for
  backwards compatibility with downstream proofs that still want a list,
  plus simp-friendly bridging lemmas:
  `PmSeq.toList_length`, `PmSeq.toList_getD` (bridges to `lookupNat`),
  `PmSeq.toList_AllPmOne`. Same for `SignSeq`.
- `seqSum` is now over `Fin n` (`∑ i : Fin n, a i`); `seqSumList` retains
  the list form.
- `IsTurynType`, `isTurynTypeBool`, `IsTurynType.toTyped`,
  `IsTurynType.vanishing`, `PmSeq.toSign`, the `pm!` parser — all migrated.

### Phase 3: `Turyn/BaseSequence.lean` (draft on branch, not yet green)

Drafted (see file in branch). Defines:
- `negSeqFn : (Fin n → Int) → (Fin n → Int)` — pointwise negation
- `appendFn : (Fin n → Int) → (Fin m → Int) → (Fin (n+m) → Int)` —
  function-level concat (dispatch on `i.1 < n`)
- `pointwise_cancel_fn` — pointwise version of the existing list lemma
- `concat_neg_autocorr_sum_fn` — direct port of the list-based proof,
  with `lookupNat` replacing `List.getD`. The inner case-analysis follows
  the same shape (range filtering on `i + s < nz` etc.).
- A length identity `2 * n - 1 = n + (n - 1)` (`two_n_sub_one_eq`).
- `step1_pmSeq f h` — wraps a function on `Fin (n + (n - 1))` into a
  `PmSeq (2 * n - 1)` by relabeling the underlying `Nat` index.
- `aperiodicAutocorr_step1_pmSeq` — proves the autocorrelation is unchanged
  by the relabeling.
- `step1` — the final Step 1 interface.

## Known issues

### BaseSequence.lean (in-progress)

Several iterations needed because:
1. `recast` from `Fin (n + (n - 1))` to `Fin (2 * n - 1)` initially used
   `rw [length_eq]` inside the `Fin` proof, which fails motive-type-correct.
   **Fixed:** use `omega` directly with `i.2` and `two_n_sub_one_eq` as hypotheses.
2. The unused-simp-arg linter is promoted to an error in this Lean toolchain
   (4.28.0). Several `simp [hi, his, hbi]` calls don't actually need every
   arg. **Workaround:** added `set_option linter.unusedSimpArgs false` at
   the file top; long-term, prune the unused args.
3. The dependent-if (`dite`) reductions in `pointwise_cancel_fn` need
   explicit `simp only [...]` pre-passes to expose `i - nz < nw` and
   `i + s - nz < nw` so `ring` can close the resulting algebraic goals.
   **Last known issue: line 116-118**, where after `simp only [hi, his, ↓reduceIte]`
   the dependent-if branches with `(if h : i - nz < nw then w ⟨...⟩ else 0)`
   are not yet simplified. Fix in progress: add `have hwi : i - nz < nw := by omega; simp only [hwi, ↓reduceDIte]` before `ring`.

The proof structure is correct and parallels the existing list-based proof.
With 2-3 more iterations on the dite-reduction patterns, Phase 3 should be
green.

## What's left (phase-by-phase)

### Phase 4 — `Turyn/Equivalence.lean` (1419 lines, largest rewrite)

The kernel proofs are:
- `aperiodicAutocorr_neg/rev/alt` invariance lemmas — re-prove using
  `Finset.sum_nbij` on `Finset.range (n - s)`. The underlying index set is
  the same; only `lookupNat (negSeqFn a) i = -(lookupNat a i)`,
  `lookupNat a.reverse i = lookupNat a (n - 1 - i)`, and
  `lookupNat (Turyn.altSeq a) i = sign(i) * lookupNat a i` change.
- `vanishing_neg/rev/alt/swap` — follow immediately from invariance lemmas.
- `PmSeq.neg`, `PmSeq.reverse`, `PmSeq.alt` — function-typed versions.
  Reversal needs `i ↦ ⟨n - 1 - i, _⟩` proof.
- `Elementary` inductive, `Equivalent` definition — unchanged.
- `step1_condition1`..`step6_condition6` — proof rewrites where
  `S.X.data.length` becomes a known `n`, and `S.X.data.getD i 0` becomes
  `lookupNat S.X.data i` (which the existing `xAt` already wraps).
- `lemma1_endpoint_constraint` etc. — algebraic content unchanged.

### Phase 5 — `Turyn/XY.lean` (564 lines)

Mostly mechanical: every `S.X.data.getD i 0` becomes `S.X.data ⟨i, _⟩` (with
`_` discharged by `omega` from a `1 ≤ i ≤ n` hypothesis), or use
`PmSeq.toList_getD` to keep list-style proofs working. The
`aperiodicAutocorr_X_via_xAt` lemma needs to be re-stated using the new
`lookupNat`-based primitive.

### Phase 6 — `Turyn/TSequence.lean` (535 lines)

- Replace `seqSumHalf` / `seqDiffHalf` / `zeroSeq` / list-based
  `periodicAutocorr` with function-typed analogues.
- Redefine `TSequence m` to carry `a b c d : IntVec m` (= `Fin m → Int`).
- Redefine `step2a..step2d` as direct `Fin (3n-1) → Int` functions
  (no list concatenation). E.g.
  ```
  def step2a {n : Nat} (T : TurynType n) : Fin (3 * n - 1) → Int :=
    fun i => if h : i.1 < n then T.Z.data ⟨i.1, h⟩ else 0
  ```
- Rewrite `step2_support` (currently 91 lines of list-append case analysis)
  as ~40 lines of `Fin.val` case analysis on three regions:
  `[0, n)`, `[n, 2n-1)`, `[2n-1, 3n-1)`.
- Rewrite `step2_periodic` against `Turyn.periodicAutocorr` from
  `Turyn/MatUtils.lean`.

### Phase 7 — `Turyn/GSArrayBridge.lean`

DELETE. Survivors:
- `tseqCombine1..4` — produce `IntVec m` directly from a function-typed
  `TSequence m`. Move into `GoethalsSeidel.lean`.
- `gsDataOfTSequence`, `typedGsMatrixOfTSequence`, `typedGsMatrix_isHadamard` —
  move into `GoethalsSeidel.lean`.
- `listToIntVec` and `typed_periodicAutocorr_eq_list` — DELETE; no longer
  needed since both sides are function-typed.

### Phase 8 — `Turyn/GoethalsSeidel.lean`

Absorb the chain entry points described above. Likely <50 lines added.

### Phase 9 — `Turyn/Hadamard.lean`

Should compose without changes if Phases 6+7+8 are right. Update
the import from `Turyn.GSArrayBridge` to `Turyn.GoethalsSeidel`.

### Phase 10 — `Turyn/Examples.lean`

The risk: `native_decide` on `tt6_valid` and `kharaghani_2005_tt36`.
The native compiler may evaluate `Fin n → Int` differently from
`List Int`, possibly slower. Mitigation in `TurynType.lean`:
`PmSeq.ofList` is implemented so that the underlying `Fin n → Int`
calls `List.getD` on the source list, which should preserve native-decide
performance. **Untested.**

The `pm! "..."` literal builds a `List Int`, then `PmSeq.ofList` wraps it
with a `Fin n → Int` accessor. So `S.data ⟨i, h⟩` reduces to
`(pm! "...").getD i 0`, which native_decide can evaluate efficiently.

### Phase 11 — `Turyn/Energy.lean` (~80 lines rewrite)

`sum_sq_eq_finset` and the chain become sums over `Fin n` rather than
`List.range a.length`. The structure is parallel; needs careful
`Fin.sum_univ_eq_sum_range`-style rewrites.

## Recommended next steps

1. **Phase 4 proper (Equivalence.lean rewrite):** All foundations are
   in place. The remaining work is:
   - Add accessor identity lemmas (`xAt_doNegX`, `xAt_doRevX_at`, etc.)
     — ~30-40 short lemmas, mostly `unfold + rfl` style for unchanged
     fields and `simp [PmSeq.neg_data, negSeqFn]` for changed ones.
   - Add per-condition preservation (`canonical1_doRevX`, etc.)
   - Rewrite `step1_condition1` through `step6_condition6` —
     ~600+ lines of step-by-step normalization using the do* family.
     The original list-based code in `Turyn.Equivalence` is the template;
     each `S.A.data.length = n` becomes type-level (the field is
     `S.X : PmSeq n`), `S.A.getD i 0` becomes `lookupNat S.X.data i`
     (or `xAt S i` after the i is appropriately offset).
   - Cap with `canonical_representative_exists` and the namespace re-exports.

2. **Phase 6 (TSequence):** Redefine `TSequence m` and `step2*` as direct
   `Fin (3n-1) → Int` functions (no list concatenation). Rewrite
   `step2_support` and `step2_periodic` against `Turyn.periodicAutocorr`
   from `Turyn/MatUtils.lean`.

3. **Phase 5 (XY):** Mechanical `S.X.data.getD i 0 → lookupNat S.X.data i`
   substitution; many proofs already use `xAt S i` accessor which is
   unchanged in interface.

4. **Phases 7-11:** Mostly mechanical once foundations are in place.

## Strategic suggestion: split the refactor

The user's plan estimates 3-5 days. Even with an autonomous worker that
does not pause, this is bounded by:
- Each `lake build` of a Turyn module takes 4-15 minutes on a cold cache.
- ~1500-2000 lines of Lean proof scripts must be touched, of which several
  hundred have non-trivial `simp`/`omega` interactions that need verification.
- Cascading errors mean each proof needs fixing in isolation before the
  next one's diagnostics become readable.

A more incremental path would be:

**Sub-PR 1:** Phases 1-3 (carrier change in `Defs`, `TurynType`,
`BaseSequence`). End state: only `Turyn.Defs`, `Turyn.TurynType`, and
`Turyn.BaseSequence` build; the rest is broken. *(Roughly: this session.)*

**Sub-PR 2:** Phase 4 (`Equivalence.lean`). Adds `aperiodicAutocorr_neg/rev/alt`
re-proofs and the `step*_condition*` family. *(One session.)*

**Sub-PR 3:** Phase 5 (`XY.lean`). Mechanical rewrite. *(One session.)*

**Sub-PR 4:** Phases 6-9 (TSequence, GSArrayBridge deletion,
GoethalsSeidel absorption, Hadamard). Cleanly closes out the GS chain.
*(One session.)*

**Sub-PR 5:** Phases 10-11 (Examples, Energy). Validates `native_decide`
performance and the energy identity. *(One session.)*

This sequencing keeps each sub-PR reviewable in isolation. The user can
reject or revise any sub-PR without losing prior work.

## Suggested simplifying utilities to add

- `lookupNat_eq_apply` simp lemma: `lookupNat a i.1 = a i` for `i : Fin n`.
- `Fin.append`-like notation for `appendFn`.
- A `simp` extension that rewrites `T.X.data ⟨i, h⟩` directly when `i` and
  `h` are obvious from context — there are many such uses in the proof scripts.
