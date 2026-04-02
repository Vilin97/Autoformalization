# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-02T22:50Z

## Status Summary
- **CI**: In progress (prev 2 green)
- **Heartbeat overrides**: 0
- **Sorry count**: 1 (`ext_vanishing_of_colimit_pieces` at FiniteGeneratorReduction.lean:65)
- **Files**: 16 files under `main/`, 5183 lines

## This Cycle's Work Items

1. **[/simplify] Fix stale header in FiniteGeneratorReduction.lean** (P4, immediate)
   Line 6 references old sorry location. Update to match current `ext_vanishing_of_colimit_pieces`.

2. **[/prove] Attempt to close ext_vanishing_of_colimit_pieces** (P0)
   Try: decompose into sub-lemmas. For the n=0 case, the hHom hypothesis should suffice
   (transfer via Ext.homEquiv₀). For n≥1, extract the dimension-shift reduction as a
   proved sub-lemma and leave only the core colimit-transfer as sorry.

3. **[/simplify] Split IrreducibleStep.lean** (P3)
   Extract epi-image vanishing lemmas into `EpiImageVanishing.lean` to bring both files
   under ~700 lines. This addresses critique P3.

## Backlog
- P1: Build universal δ-functor theorem (~300 lines)
- P1: Fix docs/blueprint 404
- P2: Generalize to finite cohomological dimension
- P3: Extract Mathlib PR candidates
