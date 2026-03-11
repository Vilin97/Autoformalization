# Plan — Cycle 80

## Status summary

- **Sorry count**: 0
- **Files**: 22 files, ~8,927 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Continue semicolon cleanup — remaining files (`/simplify`)
- **What**: Break lines with 2+ plain semicolons in the remaining files not yet cleaned: Defs (8), NewtonianPotential (7), CoulombFluxDiff (6), Section2 (8), CoulombFlux (4), Section4 (1), Section5 (5), others.
- **Why**: 64 lines with 2+ plain semicolons remain. Previous cycles cleaned Section3Helpers, TorusInstance, CoulombPSD. Now clean the rest.
- **Approach**: For each file, break multi-semicolon lines at `;` boundaries. Skip idiomatic short pairs. Verify build.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 7 files over 600 lines | Code quality — ongoing |
| 6c | 183 lines > 100 chars | Code style — future cycles |
| 8b | Weaken C^∞ → C^2 | Epistemic — hard |
| 8c | Generalize beyond T^3 | Epistemic — hard |
| 8d | Mathlib PR for helper lemmas | Community |
| 8e | Split Defs.lean | Code quality |
| 8f | Split Section3Helpers.lean (1027 lines) | Code quality — needs dependency analysis |
