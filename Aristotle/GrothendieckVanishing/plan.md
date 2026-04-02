# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-02T22:40Z

## Status Summary
- **CI**: Latest run in_progress (previous 2 green)
- **Heartbeat overrides**: 0
- **Sorry count**: 1 in FiniteGeneratorReduction.lean:95 (Ext^n colimit transfer)
- **Files**: 16 files under `main/`, 5183 lines

## Remaining Sorry (1)

### `Subsingleton (Ext Z ip.shortComplex.X₃ n)` (FiniteGeneratorReduction.lean:95)
Ext^n(Z, Q) = 0 where Q = cokernel of injective embedding c.pt ↪ I.
Dimension shift is PROVED — the sorry is isolated to this one subgoal.
Q = colim Q_j by AB5, each Ext^n(Z, Q_j) = 0 by per-j LES.
Needs: Ext^n preserves filtered colimit. Mathlib gap.

**Aristotle history**: Multiple attempts (b46c7418, d18d43d0, 58d52866) all returned
COMPLETE_WITH_ERRORS. The gap is genuine Mathlib infrastructure.

## This Cycle's Work Items

1. **[/simplify] Update GrothendieckVanishing.lean header** (P4)
   The header still says "n≥1 case" but the sorry is now precisely decomposed via
   dimension shift. Update to reflect the `Subsingleton (Ext Z Q n)` formulation.

2. **[/submit-aristotle] Resubmit ext colimit transfer** (P1)
   The file `aristotle-in/ext_filtered_colimit.lean` exists but was NOT_SUBMITTED.
   Check if it compiles, update if needed with the new dimension-shift decomposition,
   and submit.

3. **[/prove] Attempt direct proof of Ext^n colimit transfer** (P1)
   Even though previous attempts failed, the dimension-shift decomposition is new.
   Try: for the specific call site (sheaves on Noetherian space), prove the factoring
   property using `IsFinitelyPresentable.exists_hom_of_isColimit` or the adjunction.

4. **[/simplify] Split IrreducibleStep.lean** (P3, from critique)
   At 1263 lines, it's 26% over the 1000-line guideline. Extract epi-image vanishing
   lemmas (~400 lines) into a separate `EpiImageVanishing.lean`.

## Backlog

- **P1**: Build universal δ-functor theorem (~300 lines) — most feasible path to close sorry
- **P1**: Docs/blueprint 404 — needs CI/deployment fix
- **P2**: Generalize to finite cohomological dimension (drop NoetherianSpace)
- **P3**: Extract FlasqueVanishing as standalone Mathlib PR candidate
- **P3**: Extract subsingleton_ext_of_ses family as Mathlib PR candidate

## Completed (from previous plans)

- n=0 case of ext_comm_filtered_colimit_mono (PROVED)
- Dimension shift decomposition for n≥1 (PROVED: reduces to Ext^n(Z,Q) = 0)
- constantSheafAdj + addCommGrpCat helpers (PROVED)
- Direct section argument for hKsub (PROVED via sHom_app_generator)
- Cascade theorems: sheafH_vanishing_succ + sheafH_vanishing_cascade (PROVED)
