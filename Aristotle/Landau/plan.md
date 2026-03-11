# Plan — Cycle 71

## Status summary

- **Sorry count**: 0
- **Files**: 22 files, ~8,300 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## Active multi-cycle strategies

### Code quality reduction (cycles 70–71+)
7 files over 600 lines. Target: continue extracting helpers and splitting large files.

## This cycle's work items

### 1. Extract remaining derivative helpers from CoulombConcreteTheorem42.lean (`/simplify`)
- **What**: Move `norm_iteratedFDeriv_proj_sq_le`, `contDiff_negNormSq_div`, and `quadratic_iteratedFDeriv_bound` (~80 lines) to Section3Helpers.lean
- **Why**: Reduces CoulombConcreteTheorem42.lean from 742 to ~660 lines
- Fixes critique issue 8a, reduces 6b

### 2. Split Maxwellian section from Defs.lean (`/simplify`)
- **What**: Extract `IsMaxwellian`, `equilibriumMaxwellian`, and related lemmas (~150 lines) to a new `MaxwellianDefs.lean`
- **Why**: Reduces Defs.lean from 788 to ~640 lines
- Fixes critique issue 8e

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 7 files over 600 lines | Code quality — ongoing reduction |
| 8b | Weaken C^∞ → C^2 | Epistemic — hard |
| 8c | Generalize beyond T³ | Epistemic — hard |
| 8d | Mathlib PR for helper lemmas | Community |
