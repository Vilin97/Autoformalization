# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-02T12:00Z

## Status Summary
- **CI**: GREEN (PRs auto-merging)
- **Heartbeat overrides**: 0
- **Sorry count**: 1 in IrreducibleStep.lean
- **Files**: 15 files under `main/`, ~6600 lines

## Remaining Sorry (1)

### `ext_comm_filtered_colimit_mono` (line ~1227)
**Pure categorical Mathlib gap**: In a Grothendieck abelian category, Ext^n(Z,-) preserves
filtered colimits of monomorphism diagrams.

Mathlib has `preservesColimit_coyoneda_obj_of_mono` which gives the n=0 (Hom) case.
The general case (Ext^n for n > 0) requires dimension shifting via injective presentations,
which is NOT in Mathlib v4.28.0.

## Recently Closed

### `cohomology_vanishing_of_finitelyGenerated_vanishing` (was sorry, now proved)
**Hartshorne 2.9**: If H^m = 0 for all finitely generated subsheaves of K, then H^m(K) = 0.
Now proved via the filtered diagram of finitely generated subsheaves:
- Built `finsetGenFunctor : Finset(SectionIndex K) ⥤ Sheaf(X)` sending S ↦ finsetGeneratedSheaf S
- Built `finsetGenCocone` with vertex K (maps are image.ι)
- Proved `finsetGenCocone_isColimit`: the canonical map colim → K is mono (AB5) and epi
  (allSectionMap K factors through it), hence iso
- Applied `ext_comm_filtered_colimit_mono` to close the sorry

## Completed This Session

Closed 23+ sorry's total, reducing from 23 to 1:
- All stalk lemmas, ClosedImmersionSES proofs, finset infrastructure
- exists_good_section (via Nat.find minimality for exists_section_generating_stalks)
- IsFlasqueSheaf(zeroOutsideInt ⊤) (via presheaf NatIso + sheafification)
- cohomology_vanishing_of_finitelyGenerated_vanishing (via filtered diagram construction)
- zsmul_generator_injective, sHom_stalk_bijective_at, and many more helpers
