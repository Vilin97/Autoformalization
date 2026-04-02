# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-02T08:30Z

## Status Summary
- **CI**: GREEN (PRs auto-merging)
- **Heartbeat overrides**: 0
- **Sorry count**: 2 in IrreducibleStep.lean (decomposed from 1)
- **Files**: 15 files under `main/`, ~6500 lines

## Remaining Sorry's (2)

### 1. `ext_comm_filtered_colimit_mono` (line ~1227)
**Pure categorical Mathlib gap**: In a Grothendieck abelian category, Ext^n(Z,-) preserves
filtered colimits of monomorphism diagrams.

### 2. `cohomology_vanishing_of_finitelyGenerated_vanishing` (line ~1241)
**Hartshorne 2.9**: If H^m = 0 for all finitely generated subsheaves of K, then H^m(K) = 0.
Applies (1) to the specific sheaf case.

**Mathematical content**: K is the filtered colimit of its finitely generated subsheaves K_S.
Then H^m(K) = colim H^m(K_S) = colim 0 = 0.

**Mathlib status**:
- `Sheaf.instIsGrothendieckAbelian` exists (sheaf category is Grothendieck abelian)
- `IsGrothendieckAbelian.hasFilteredColimitsOfSize` exists
- `Sheaf.ab5ofSize` exists (filtered colimits are exact)
- `preservesColimit_coyoneda_obj_of_mono` exists — Hom(X,-) preserves colimits of
  mono diagrams in Grothendieck abelian categories. Gives the n=0 (Hom) case.
- "Ext^n commutes with filtered colimits" is NOT in Mathlib (as of v4.28.0).
  The dimension-shifting step (Hom → Ext^n) requires additional infrastructure.

**Possible approaches**:
1. **Coyoneda + dimension shifting**: Use `preservesColimit_coyoneda_obj_of_mono` for
   n=0, then prove Ext^n preserves filtered colimits by induction on n using injective
   presentations + LES. Obstacle: quotient system {I/K_S} has epi (not mono) transitions.
2. **Direct Noetherian argument**: Show any element of H^m(K) factors through a f.g.
   subsheaf. Requires Čech cohomology or Godement resolution (not in Mathlib).
3. **Accept as axiom**: Standard theorem in homological algebra. State as axiom pending
   Mathlib development.

## Completed This Session

Closed 22+ sorry's total, reducing from 23 to 1:
- All stalk lemmas, ClosedImmersionSES proofs, finset infrastructure
- exists_good_section (via Nat.find minimality for exists_section_generating_stalks)
- IsFlasqueSheaf(zeroOutsideInt ⊤) (via presheaf NatIso + sheafification)
- zsmul_generator_injective, sHom_stalk_bijective_at, and many more helpers
