# Plan -- Cycle 118 (updated)

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 10,202 lines
- **Build**: Local build passing; CI re-run in progress (elan infra issue)
- **Critique verdict**: CONDITIONAL ACCEPT (cycle 118)
- **Condition for ACCEPT**: Fix 12 linter warnings in CoulombPSD.lean
- **maxHeartbeats overrides**: 2 (NewtonianPotential.lean:85 at 800000, TorusIntegration.lean:87 at 400000)
- **Aristotle jobs**: 0 pending
- **Open issues**: 1 Medium (CoulombPSD warnings), rest Low

## This cycle's work items

### 1. Fix linter warnings in CoulombPSD.lean (`/simplify`)
- **What**: Critique issue 6d. 12 warnings: 7 unused simp args, 2 unused variables, 3 multi-goal tactics.
- **Files**: `CoulombPSD.lean`
- **Approach**: Remove unused simp args, prefix unused vars with `_`, fix multi-goal scoping.
- **Risk**: Low. Cosmetic changes only.
- **START IMMEDIATELY.**

### 2. Fix long line in Section3Helpers.lean (`/simplify`)
- **What**: Critique issue 6c. 1 line over 100 chars.
- **Files**: `Section3Helpers.lean`
- **Approach**: Break at natural point.
- **Risk**: None.

### 3. Weaken ContDiff ℝ ⊤ → ContDiff ℝ 3 (`/strengthen`)
- **What**: Critique issue 8a. The abstract theorem only needs C³ but the concrete uses C∞.
- **Files**: `CoulombConcreteTheorem42.lean` + 12 Coulomb files
- **Approach**: Change hypothesis 4, update `.of_le le_top` → `.of_le (by norm_num)`. Medium effort.
- **Risk**: Medium. Touches many files but the change is mechanical.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 2 maxHeartbeats overrides (800000 + 400000) | Code quality | Critique 6a. |
| Section3Helpers.lean 613 lines | Code quality | Just over guideline. |
| Gaussian integral lemmas not generalized | Strengthen | Critique 8c. |
| Maxwell molecules kernel instance | Feature | Easy win ~100 lines. |
| Mathlib PR candidates (4 lemmas) | Upstream | |
