# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-02T22:20Z

## Status Summary
- **CI**: GREEN
- **Heartbeat overrides**: 0
- **Sorry count**: 1 in FiniteGeneratorReduction.lean (Ext^n colimit transfer)
- **Files**: 16 files under `main/`, ~5100 lines

## Remaining Sorry (1)

### `Subsingleton (Ext Z ip.shortComplex.X₃ n)` (line ~94)
**Precise statement**: For the cokernel Q = I/c.pt of an injective embedding c.pt ↪ I,
show Ext^n(Z, Q) = 0 given that the original diagram Y has vanishing Ext^{n+1} on all
pieces (and the dimension shift reduces Ext^{n+1}(Z, c.pt) to Ext^n(Z, Q)).

**What's proved around the sorry**:
- The dimension shift via injective presentation (LES + Ext.eq_zero_of_injective)
- Every element of Ext^{n+1}(Z, c.pt) lifts to Ext^n(Z, Q) via the connecting map
- The n=0 case of the full theorem (Hom level) is PROVED via hHom + Ext.homEquiv₀

**Why it's hard**: Q = I/c.pt = colim(I/Y.obj j) by AB5, and Ext^n(Z, I/Y.obj j) = 0
by the per-j LES. But showing Ext^n(Z, colim) = 0 from per-piece vanishing requires
Ext^n to preserve the filtered colimit. The quotient diagram has epi (not mono) transitions,
blocking recursive application of the theorem.

**Paths to closing (ordered by feasibility)**:
1. **Universal δ-functor theorem** (~300 lines): Define effaceable δ-functors, prove
   universality, show Ext^n and colim-Ext^n agree at degree 0 hence at all degrees.
2. **Čech cohomology** (~500 lines): For Noetherian spaces, Čech cochains use finite
   products which commute with filtered colimits. Prove Čech = derived.
3. **Derived category colimit preservation** (~500 lines): Show the localization C → D(C)
   preserves filtered colimits and Z is compact in D(C).
4. **Mathlib PR**: Submit `PreservesFilteredColimits (extFunctorObj Z n)` upstream.
5. **Wait for Mathlib**: The infrastructure may be added as part of ongoing development.

## Completed

- n=0 case of ext_comm_filtered_colimit_mono (PROVED)
- Dimension shift decomposition for n≥1 (PROVED: reduces to Ext^n(Z,Q) = 0)
- constantSheafAdj + addCommGrpCat helpers (PROVED)
- Direct section argument for hKsub (PROVED via sHom_app_generator)
- File split: IrreducibleStep → IrreducibleStep + FiniteGeneratorReduction
- Cascade theorems: sheafH_vanishing_succ + sheafH_vanishing_cascade (PROVED)
- All documentation headers updated
