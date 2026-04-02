# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-02T21:30Z

## Status Summary
- **CI**: GREEN
- **Heartbeat overrides**: 0
- **Sorry count**: 1 in FiniteGeneratorReduction.lean (n≥1 case of ext_comm_filtered_colimit_mono)
- **Files**: 16 files under `main/`, ~5100 lines

## Remaining Sorry (1)

### `ext_comm_filtered_colimit_mono` n≥1 case (line ~82)
**Genuine Mathlib API gap**: In a Grothendieck abelian category, `Ext^{n+1}(Z,-)` preserves
filtered colimits of monomorphism diagrams. The n=0 case (Hom) is FULLY PROVED.

The dimension shifting approach fails because the quotient diagram `{I/Y_j}` has
epi (not mono) transitions, and the IH requires mono transitions.

**Paths to closing (ordered by feasibility)**:
1. **Mathlib PR**: Submit the `CreatesColimitsOfShape` instance for `sheafToPresheaf` for
   filtered shapes. This would let `sheafToPresheaf` preserve filtered colimits, enabling
   the presheaf-level colimit argument.
2. **Build Čech cohomology**: ~500 lines. Define Čech complex, prove it commutes with
   filtered colimits (finite covers), prove Čech = derived on Noetherian spaces.
3. **Universal δ-functor theorem**: ~300 lines. Define effaceable δ-functors, prove
   universality, show filtered-colimit Ext is effaceable.
4. **Wait for Mathlib**: The infrastructure may be added as part of ongoing derived
   category development.

## Completed

- n=0 case of ext_comm_filtered_colimit_mono (PROVED)
- constantSheafAdj + addCommGrpCat helpers (PROVED)
- Direct section argument for hKsub (PROVED via sHom_app_generator)
- File split: IrreducibleStep → IrreducibleStep + FiniteGeneratorReduction
- Cascade theorems: sheafH_vanishing_succ + sheafH_vanishing_cascade (PROVED)
- All documentation headers updated
