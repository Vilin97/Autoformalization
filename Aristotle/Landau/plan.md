# Plan — Cycle 104

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 9,537 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Extract `current_density_of_gaussian` from Theorem42.lean (`/simplify`)
- **What**: Issue 6d. The `hJ_from_maxwellian` block (lines 275-304, ~30 lines) proves that if `f = exp(a₀ + b·v + c₀|v|²)`, then `∫ vᵢ f = (∫ f) * (-1/(2c₀)) * bᵢ`. Extract as a standalone lemma in GaussianHelpers.lean. Saves ~22 lines, bringing `Theorem42` from ~200 to ~178 lines.
- **Why**: Reduces the longest remaining proof and makes the Gaussian identity reusable.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6d | 2 proofs over 150 lines | Low — both under 200 |
| 8c | Generalize beyond T^3 | Hard |
| 8d | Mathlib PR for helper lemmas | 5 candidates ready |
| 8j | lean-lsp build desync | Persistent tooling issue |
