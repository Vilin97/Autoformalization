# Work Plan — Grothendieck Vanishing

**Updated**: 2026-04-05T00:17Z

## Status Summary

- **Sorry count**: 0 — FULLY PROVED
- **Axioms**: 0 (verified by `lean_verify`)
- **Files**: 16 `.lean` in `main/`, ~5844 total lines
- **CI**: Last runs green, but uncommitted changes need push
- **Key breakthrough**: Gabriel's theorem bypassed by proving "filtered colimits of flasque sheaves are flasque" (`isFlasque_filtered_colimit`). Since injective ⟹ flasque, this gives H^n(colim I_j) = 0 without needing Injective(colim I_j).

## This Cycle's Work Items

### 1. Commit and push (`/commit`) — P0
6 modified files with the sorry elimination. Must commit and push to trigger CI.

### 2. Clean up stale Aristotle files (`/cleanup`) — P3
- Delete `aristotle-in/gabriel_injective.lean` (Gabriel's theorem no longer needed)
- Delete `aristotle-in/sheafH_colim_v2.lean` (superseded)
- Update `aristotle-jobs.json` to reflect all jobs are expired/superseded

### 3. Cancel Aristotle job (`/check-aristotle`) — P3
- Job `2507e172` for Gabriel's theorem is still IN_PROGRESS but no longer needed

## Backlog

- **P1**: Blueprint deployment — returns 404. No deployment workflow exists.
- **P4**: Generalize coefficient category from `AddCommGrpCat` to arbitrary Grothendieck abelian.
- **P4**: Upstream `isFlasque_filtered_colimit`, `PresheafFilteredColimit`, `FlasqueVanishing`, `ConstantSheafFlasque` to Mathlib.
