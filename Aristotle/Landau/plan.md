# Plan — Cycle 70

## Status summary

- **Sorry count**: 0
- **Files**: 22 files, ~8,300 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## Active multi-cycle strategies

### Code quality reduction (cycle 70+)
With 0 sorry's, focus shifts to code quality. 7 files over 600 lines. Target: reduce the largest files by extracting reusable helpers.

## This cycle's work items

### 1. Fix long-line warnings in Defs.lean (`/simplify`)
- **File**: `Defs.lean` lines 324, 363, 424
- **What**: Wrap lines exceeding 100 characters
- Fixes critique issue 6c

### 2. Extract iterated derivative helpers from CoulombConcreteTheorem42.lean (`/simplify`)
- **What**: Move `iteratedFDeriv_clm_zero`, `norm_iteratedFDeriv_one_clm`, `norm_iteratedFDeriv_proj_sq_le`, `quadratic_iteratedFDeriv_bound` to Section3Helpers.lean
- **Why**: Reduces CoulombConcreteTheorem42.lean from 762 to ~680 lines, makes helpers reusable
- Fixes critique issues 6b (partially) and 8a

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 7 files over 600 lines | Code quality — ongoing reduction |
| 8b | Weaken C^∞ → C^2 | Epistemic — requires threading finite regularity |
| 8c | Generalize beyond T³ | Epistemic — hard, needs Mathlib manifold infra |
| 8d | Mathlib PR for helper lemmas | Community — iteratedFDeriv_clm_zero, norm_iteratedFDeriv_one_clm |
| 8e | Split Defs.lean | Code quality — extract Maxwellian section |
