# Plan — Cycle 101

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 9,563 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Extract duplicated `h_poly_int` block from CoulombPSD.lean (`/simplify`)
- **What**: Issue 6d. The block proving `Integrable (fun v => (1+‖v‖)^{2*Kg} * f v)` from Schwartz decay appears identically (~14 lines each) in both `psd_outer_integrable_coulomb` (lines 78-91) and `fubini_double_integrable_coulomb` (lines 251-264). Extract to a standalone lemma.
- **Why**: Deduplicates ~14 lines, shortens `fubini_double_integrable_coulomb` from 197 to ~183 and `psd_outer_integrable_coulomb` from 88 to ~74 lines.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6d | 5 proofs over 150 lines | Low — all under 200 |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | 5 candidates ready |
| 8j | lean-lsp build desync | Persistent tooling issue |
