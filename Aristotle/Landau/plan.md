# Plan — Cycle 102

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 9,550 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Replace manual `schwartz_pointwise_decay` expansions in CoulombFluxDiff.lean (`/simplify`)
- **What**: Issue 6d. Lines 60-62 and 64-67 manually expand `schwartz_pointwise_decay` instead of calling it. Replace with direct calls. Also check for similar cleanup in the `h_per_term` block (lines 162, 170).
- **Why**: Reduces `coulomb_flux_deriv_schwartz_decay` by ~6 lines (197→~191). Consistent with pattern used in CoulombPSD and CoulombFluxBound.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6d | 4 proofs over 150 lines | Low — all under 200 |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | 5 candidates ready |
| 8j | lean-lsp build desync | Persistent tooling issue |
