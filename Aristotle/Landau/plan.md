# Plan -- Cycle 119 (updated)

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 10,203 lines
- **Build**: Local build passing
- **Critique verdict**: CONDITIONAL ACCEPT (cycle 119)
- **Condition for ACCEPT**: Fix 11 linter warnings in Section3Helpers.lean
- **maxHeartbeats overrides**: 2 (NewtonianPotential.lean:85 at 800000, TorusIntegration.lean:87 at 400000)
- **Aristotle jobs**: 0 pending
- **Open issues**: 1 Medium (Section3Helpers warnings), rest Low

## This cycle's completed work

### 1. ContDiff ℝ ⊤ → ContDiff ℝ 3 (`/strengthen`) — DONE
- Weakened velocity smoothness from C∞ to C³ across 13 Coulomb files
- Internal helpers in CoulombFluxConv lowered to ContDiff ℝ 2 where fderiv drops one order

### 2. Linter fixes across 5 files (`/simplify`) — DONE
- Section4, Section7, CoulombSpatialTransport, CoulombFlux, VMLInputDerive

## Next cycle's work items

### 1. Fix linter warnings in Section3Helpers.lean (`/simplify`)
- **What**: Critique issue 6d. 11 warnings: 8 unused simp args, 2 unused variables.
- **Files**: `Section3Helpers.lean`
- **Approach**: Remove unused simp args, prefix unused vars with `_`.
- **Risk**: Low. Cosmetic changes only.
- **START IMMEDIATELY.**

### 2. Fix long line in Section3Helpers.lean (`/simplify`)
- **What**: Critique issue 6c. 1 line over 100 chars.
- **Files**: `Section3Helpers.lean`
- **Approach**: Break at natural point.
- **Risk**: None.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 2 maxHeartbeats overrides (800000 + 400000) | Code quality | Critique 6a. |
| Section3Helpers.lean 615 lines | Code quality | Just over guideline. |
| Spatial smoothness C∞ audit | Strengthen | Critique 8f. |
| Gaussian integral lemmas not generalized | Strengthen | Critique 8c. |
| Maxwell molecules kernel instance | Feature | Easy win ~100 lines. |
| Mathlib PR candidates (4 lemmas) | Upstream | |
