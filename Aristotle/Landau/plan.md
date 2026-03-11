# Plan — Cycle 73

## Status summary

- **Sorry count**: 0
- **Files**: 22 files, 8,297 lines
- **Build**: Passes with cached .olean only. **Fresh build FAILS** (Section3Helpers.lean + TorusDefs.lean Mathlib API drift).
- **Critique verdict**: REVISE
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Fix Mathlib API drift in Section3Helpers.lean (P0, `/simplify`)
- **What**: Fix 14 compilation errors caused by renamed/removed Mathlib identifiers
- **Key renames to find**: `integral_gaussian`, `integral_fintype_prod_eq_prod`, `integrable_rpow_mul_exp_neg_mul_sq`, `ContDiffAt.isSymmSndFDerivAt`, `norm_iteratedFDeriv_mul_le`, `iteratedFDeriv_sum` parameter name change
- **Why**: Fresh builds fail. This blocks everything.

### 2. Fix Mathlib API drift in TorusDefs.lean (P0, `/simplify`)
- **What**: Fix 14 compilation errors — `MeasureSpace Torus3` synthesis failures and `isSymmSndFDerivAt` rename
- **Why**: Same as above — cascade failure breaks CoulombConcreteTheorem42.

### 3. Verify full rebuild after fixes (P0, `/commit`)
- **What**: After fixing both files, delete .olean cache for affected files and verify they compile from source.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 6 files over 600 lines | Code quality — ongoing |
| 6c | ~45 lint warnings in Section3Helpers | Code quality |
| 8b | Weaken C^∞ → C^2 | Epistemic — hard |
| 8c | Generalize beyond T^3 | Epistemic — hard |
| 8d | Mathlib PR for helper lemmas | Community |
| 8e | Split Defs.lean | Code quality |
