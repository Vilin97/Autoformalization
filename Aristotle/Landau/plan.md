# Plan — Cycle 84

## Status summary

- **Sorry count**: 0
- **Files**: 23 files, ~9,396 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Split Defs.lean (805 lines) (`/simplify`)
- **What**: Defs.lean is the second-largest file at 805 lines and contains multiple logical groups: core VML definitions, VelocityDecayConditions, VMLSteadyState, FlatTorus3 typeclass, and simp lemmas. Split into 2 files along natural boundaries.
- **Why**: Issue 8e from critique. Reduces the count of files over 600 lines from 8 to 7.

### 2. Add docstring to hGradBound explaining Coulomb-specificity (`/strengthen`)
- **What**: Issue 8i. Add a docstring or comment to the `hGradBound` field in `VelocityDecayConditions` explaining it is a Coulomb-specific regularity condition not needed for bounded kernels.
- **Why**: Low-effort improvement to mathematical documentation accuracy.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 8 files over 600 lines | Code quality — ongoing |
| 6c | ~333 plain semicolons | Code style — diminishing returns |
| 8b | Weaken C^∞ → C^2 | Epistemic — hard |
| 8c | Generalize beyond T^3 | Epistemic — hard |
| 8d | Mathlib PR for helper lemmas | Community — `iteratedFDeriv_clm_zero`, `norm_iteratedFDeriv_one_clm` ready |
| ~~8e~~ | ~~Split Defs.lean~~ | Planned this cycle |
| ~~8f~~ | ~~Split Section3Helpers.lean~~ | Done cycle 83 |
| 8g | UniformSchwartzDecay stronger than needed | Epistemic — medium |
| 8h | hExpDecay could be weakened | Epistemic — minor |
| 8i | hGradBound Coulomb-specific documentation | Documentation — minor |
