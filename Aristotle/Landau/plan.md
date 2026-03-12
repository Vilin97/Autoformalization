# Plan -- Cycle 117 (updated)

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 10,188 lines
- **Build**: CI passing locally; commit f43e39c CI in progress
- **Critique verdict**: CONDITIONAL ACCEPT (cycle 117)
- **Condition for ACCEPT**: Fix ~45 linter warnings across 6 files
- **maxHeartbeats overrides**: 2 (NewtonianPotential.lean:86 at 800000, TorusIntegration.lean:85 at 400000)
- **Aristotle jobs**: 0 pending, all done/failed/abandoned
- **Open issues**: 1 Medium (linter warnings), rest Low

## This cycle's work items

### 1. Fix linter warnings in NewtonianPotential.lean (`/simplify`)
- **What**: Critique issue 6d. ~20+ warnings: unused simp args, unused variables (`hf_smooth`), multi-goal tactics, `ring_nf` suggestions.
- **Files**: `NewtonianPotential.lean`
- **Approach**: Address each warning type systematically. Remove unused simp args, fix multi-goal tactics, replace `ring` with `ring_nf` where suggested.
- **Risk**: Low. Cosmetic changes only.
- **START IMMEDIATELY.**

### 2. Fix linter warnings in TorusIntegration.lean (`/simplify`)
- **What**: Critique issues 6d + 6e. ~8 warnings including 3 deprecated `integral_mul_left` → `integral_const_mul`, unused simp args, multi-goal tactics.
- **Files**: `TorusIntegration.lean`
- **Approach**: Replace deprecated API, remove unused simp args.
- **Risk**: Low.

### 3. Fix linter warnings in CoulombPSDHelpers.lean, CoulombFluxBound.lean (`/simplify`)
- **What**: Critique issue 6d. ~11 warnings: `show` → `change`, unused simp args, long lines.
- **Files**: `CoulombPSDHelpers.lean`, `CoulombFluxBound.lean`
- **Approach**: Replace `show` with `change`, remove unused simp args, fix 2 long lines.
- **Risk**: Low.

### 4. Fix CoulombFluxDiff line count in MEMORY.md (`/simplify`)
- **What**: Critique issue 7a. MEMORY.md says ~250, actual is 320.
- **Files**: MEMORY.md
- **Approach**: Update the line count.
- **Risk**: None.

### 5. Strengthen roundtrip with uniqueness (`/strengthen`)
- **What**: Critique issue 8e. `CoulombConcreteTheorem42_roundtrip` doesn't include T_eq uniqueness. `_unique_T` already proves this separately.
- **Files**: `CoulombNonvacuous.lean`
- **Approach**: Add uniqueness assertion to roundtrip conclusion, using `_unique_T` or `equilibriumMaxwellian_T_unique`.
- **Risk**: Low. ~5 lines.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 2 maxHeartbeats overrides (800000 + 400000) | Code quality | Critique 6a. Investigate for simplification. |
| Section3Helpers.lean 613 lines | Code quality | Just over 500-line guideline; tightly coupled. |
| Weaken ContDiff ℝ ⊤ → ContDiff ℝ 3 | Strengthen | Critique 8a. Touches all 12 Coulomb files. |
| Gaussian integral lemmas not generalized | Strengthen | Critique 8c. Could extract to reusable module. |
| Maxwell molecules kernel instance | Feature | Easy win ~100 lines. |
| Dimension generalization (Fin n) | Feature | Hard; 3D-specific throughout. |
| Mathlib PR candidates (4 lemmas) | Upstream | inverse_poly_integrable, schwartz_pointwise_decay, etc. |
| CoulombFluxConv unused variable `hM` | Code quality | Line 27; pre-existing. |
| Section3Helpers `ring_nf` suggestions | Code quality | ~4 info-level suggestions. |
