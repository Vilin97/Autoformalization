# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-02T02:30Z

## Status Summary
- **CI**: PR #5 open with auto-merge, CI pending
- **Heartbeat overrides**: 0
- **Sorry count**: 1 in IrreducibleStep.lean
- **Files**: 15 files under `main/`, ~6500 lines

## Remaining Sorry (1)

### `cohomology_vanishing_of_finitelyGenerated_vanishing` (line ~1222)
**Hartshorne 2.9**: If H^m = 0 for all finitely generated subsheaves of K, then H^m(K) = 0.

**Mathematical content**: K is the filtered colimit of its finitely generated subsheaves K_S.
Then H^m(K) = colim H^m(K_S) = colim 0 = 0.

**Mathlib status**: 
- `Sheaf.instIsGrothendieckAbelian` exists (sheaf category is Grothendieck abelian)
- `IsGrothendieckAbelian.hasFilteredColimitsOfSize` exists
- "Ext commutes with filtered colimits" is NOT in Mathlib (as of v4.28.0)

**Possible approaches**:
1. **AB5 + Ext**: Show Ext preserves filtered colimits using the Grothendieck abelian structure. Requires proving the colimit formula for Ext.
2. **Direct Noetherian argument**: Show any element of H^m(K) factors through a finitely generated subsheaf. Uses: on a Noetherian space, every section of K lives in some finsetGeneratedSheaf(S), and Ext classes can be represented by extensions that factor through f.g. subsheaves.
3. **Accept as axiom**: This is a standard theorem in homological algebra. If proving it from scratch is too costly, it could be stated as an axiom pending Mathlib development.

## Completed This Session

Closed 22+ sorry's total, reducing from 23 to 1:
- All stalk lemmas, ClosedImmersionSES proofs, finset infrastructure
- exists_good_section (via Nat.find minimality for exists_section_generating_stalks)
- IsFlasqueSheaf(zeroOutsideInt ⊤) (via presheaf NatIso + sheafification)
- zsmul_generator_injective, sHom_stalk_bijective_at, and many more helpers
