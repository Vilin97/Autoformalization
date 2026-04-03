# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-03T10:00Z

## Status Summary
- **CI**: In progress (prev 2 green)
- **Sorry count**: 3 (1 in SheafHom.lean, 2 in FiniteGeneratorReduction.lean)
- **Files**: ~17 files, 5200 lines

## This Cycle's Work Items

1. **[/prove] Close sorry #1 (isSheaf_filtered_colimit_of_sheaves)** (P0)
   Core AB5 gap in SheafHom.lean: filtered presheaf colimits of sheaves are sheaves
   on Noetherian spaces. Well-defined mathematical statement.

2. **[/prove] Decompose sorry #2 (hQprov)** (P0)
   Recursive provider for quotients-of-quotients in FiniteGeneratorReduction.lean.
   If cannot close directly, decompose into well-defined sub-lemmas.

3. **[/simplify] Split IrreducibleStep.lean** (P3)
   At 1263 lines, 26% over 1000-line guideline.

## Backlog
- P0: Build universal δ-functor theorem (~300 lines)
- P1: Fix docs/blueprint 404
- P3: Split IrreducibleStep.lean (1263 lines)
- P3: FlasqueVanishing.lean at 616 lines
