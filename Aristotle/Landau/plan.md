# Plan -- Cycle 116 (updated)

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 10,147 lines
- **Build**: CI passing (lean-action succeeded on commit 230054f)
- **Critique verdict**: CONDITIONAL ACCEPT (cycle 116)
- **Condition for ACCEPT**: Fix ~20 unused simp warnings, 1 deprecated API, 14 long lines
- **maxHeartbeats overrides**: 2 (NewtonianPotential.lean:86 at 800000, TorusIntegration.lean:85 at 400000)
- **Aristotle jobs**: 0 pending, all done/failed/abandoned
- **Open issues**: All Low severity (cosmetic cleanup)

## This cycle's work items

### 1. Clean up unused simp warnings in CoulombNonvacuous.lean (`/simplify`)
- **What**: Critique issue 6d. ~20 linter warnings for unused simp arguments (`fderiv_const`, `Function.comp`, `ContinuousLinearMap.sum_apply`, etc.). These were introduced during the Mathlib v4.24.0 fix — the agent's rewrites left stale simp arguments.
- **Files**: `CoulombNonvacuous.lean`
- **Approach**: Remove unused arguments from simp calls. Verify each change doesn't break the proof.
- **Risk**: Low. Removing unused simp args cannot change proof semantics.
- **START IMMEDIATELY.**

### 2. Fix deprecated API usage (`/simplify`)
- **What**: Critique issue 6e. `Matrix.mulVec_smul_assoc` at CoulombNonvacuous.lean:447 is deprecated → use `Matrix.mulVec_smul`.
- **Files**: `CoulombNonvacuous.lean`
- **Approach**: Replace `mulVec_smul_assoc` with `mulVec_smul`. The types differ slightly — verify with lean_goal.
- **Risk**: Low. Mathlib provides the replacement.

### 3. Fix long lines in CoulombFluxConv.lean (`/simplify`)
- **What**: Critique issue 6c. 10 lines over 100 chars in CoulombFluxConv.lean, introduced during Mathlib v4.24.0 fix.
- **Files**: `CoulombFluxConv.lean`
- **Approach**: Break long lines at natural points (after commas, before `→`, etc.).
- **Risk**: None. Formatting only.

### 4. Update MEMORY.md line counts (`/simplify`)
- **What**: Critique issue 7b. CoulombNonvacuous listed as ~351 lines (actual: 498), CoulombFluxConv as ~373 (actual: 540).
- **Files**: MEMORY.md
- **Approach**: Update line counts for the 2 stale entries.
- **Risk**: None.

### 5. Weaken hypothesis 4 from ContDiff ℝ ⊤ to ContDiff ℝ 3 (`/strengthen`)
- **What**: Critique issue 8a. The abstract theorem only needs C³. The concrete theorem uses C∞ and downcasts. Tightening this makes the theorem statement more honest.
- **Files**: `CoulombConcreteTheorem42.lean` (line 72)
- **Approach**: Change `ContDiff ℝ ⊤` to `ContDiff ℝ 3` in hypothesis 4. Verify the proof still works (it uses `.of_le le_top` to downcast, which would become `.of_le (by norm_num)`).
- **Risk**: Low-Medium. Need to verify all 19 VelocityDecayConditions fields still compile. The Schwartz decay implies C∞ anyway so all integrability arguments go through.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| CoulombNonvacuous should apply main theorem | Strengthen | Critique 8b. Proves hypotheses satisfiable but doesn't produce equilibrium conclusion. |
| 2 maxHeartbeats overrides (800000 + 400000) | Code quality | Critique 6a. Investigate for simplification. |
| Section3Helpers.lean 613 lines | Code quality | Just over 500-line guideline; tightly coupled. |
| Gaussian integral lemmas not generalized | Strengthen | Critique 8c. Could extract to reusable module. |
| Dimension generalization (Fin n) | Feature | Hard; 3D-specific throughout. |
| Maxwell molecules kernel instance | Feature | Easy win ~100 lines. |
| Mathlib PR candidates (4 lemmas) | Upstream | inverse_poly_integrable, schwartz_pointwise_decay, etc. |
