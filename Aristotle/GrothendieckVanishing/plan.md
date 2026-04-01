# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-01T23:30Z

## Status Summary
- **CI**: Push to `wip/grothendieck-vanishing` (commit `a901094`)
- **Heartbeat overrides**: 0
- **Sorry count**: 2 in IrreducibleStep.lean (both are confirmed Mathlib API gaps)
- **Files**: 15 files under `main/`, ~5000 lines

## Remaining Sorry's (2)

Both are genuine Mathlib API gaps, not proof regressions:

### 1. `exists_good_section` (line ~616)
**Step 4 core construction**: Find V' ≤ V, V' ≠ ⊥, and section s ∈ R(V') such that
`sHom s : zeroOutsideInt V' ⟶ R` is a stalk-isomorphism on V'.

**Strategy**:
1. Find x₀ ∈ V with nonzero stalk via `exists_nonzero_stalk_in_V` (proved)
2. Identify cyclic subgroup generator via `ulift_int_subgroup_cyclic` (proved)
3. Lift generator to section s via `stalk_zeroOutsideInt_eq_zsmul_generator` (proved)
4. Shrink V' for stalk bijectivity using Noetherian + irreducible properties

**Dependencies**: All sub-lemmas proved. Core difficulty is the Noetherian shrinking argument.

### 2. `cohomology_vanishing_of_finitelyGenerated_vanishing` (line ~774)
**Hartshorne 2.9**: If H^m = 0 for all finitely generated subsheaves, then H^m(K) = 0.

**Strategy**: K = colim K_α (filtered colimit of finitely generated subsheaves),
H^m(K) = colim H^m(K_α) = colim 0 = 0. Requires:
- Ext commutes with filtered colimits (AB5 / Grothendieck abelian)
- K expressed as filtered colimit of `finsetGeneratedSheaf S`

## Recently Completed (this session)

Closed 19 sorry's in IrreducibleStep.lean (21 → 2):
- Tier 1-2 stalk lemmas (8 proofs)
- ClosedImmersionSES pattern proofs (4 proofs)
- Finset infrastructure (5 proofs)
- Germ algebra (2 proofs)

Key API patterns established:
- `stalkFunctor_map_iso_toSheafify` for IsIso instances
- `Sheaf.forget ⋙ stalkFunctor` for PreservesMonomorphisms
- `ConcreteCategory.mono_iff_injective_of_preservesPullback` for injectivity
- `AddCommGrpCat.subsingleton_of_isZero` for zero object elements

## Backlog

- **Docs deployment**: Fix 404 on blueprint pages
- **File sizes**: ZeroOutside.lean (733), FlasqueVanishing.lean (616) over guideline
- **Plan/docs**: Keep sorry counts accurate
