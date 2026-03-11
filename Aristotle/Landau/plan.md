# Plan -- Cycle 116

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 9,599 lines
- **Build**: Clean (`lake env lean` on all 32 files: 0 errors, 0 warnings)
- **Critique verdict**: CONDITIONAL ACCEPT (cycle 115)
- **Condition for ACCEPT**: Add CoulombNonvacuous to default build target
- **maxHeartbeats overrides**: 1 (TorusIntegration.lean:85, 400000)
- **`simp +decide` / `aesop` / `decide`**: 0
- **Working tree**: 4 modified files (CoulombFlux, CoulombFluxDiff, CoulombPSD, LandauMatrixDerivBound), state.md untracked
- **Open issues**: 1 medium (build target), 3 low (dead parameter, stale docstring, maxHeartbeats)

## This cycle's work items

### 1. Add CoulombNonvacuous to default build target (`/simplify`)
- **What**: Critique issue 0 (Medium). `CoulombNonvacuous.lean` compiles cleanly but is not imported by `Aristotle.lean`, so `lake build` never verifies it. This is the sole condition for upgrading the critique verdict from CONDITIONAL ACCEPT to ACCEPT.
- **File**: `/home/vilin/aristotle/Aristotle.lean`
- **Approach**: Add `import Aristotle.Landau.main.CoulombNonvacuous` as a second line. Verify with `lake build`.
- **Risk**: None. One-line addition.
- **Resolves**: Critique issue 0 (Medium). Satisfies the ACCEPT condition.
- **START IMMEDIATELY.**

### 2. Remove dead parameter from `torus_hSpatialVelocityFubini` (`/simplify`)
- **What**: Critique issue 9b. The concrete helper `torus_hSpatialVelocityFubini` (TorusDefs.lean:258) takes `(hF : forall x, Integrable (F x))` but the proof body (line 262) only uses `hF_joint`. The abstract `hSpatialVelocityFubini` in Defs.lean:481 already does NOT have this parameter -- the dead parameter is only in the concrete helper.
- **File**: `/home/vilin/aristotle/Aristotle/Landau/main/TorusDefs.lean` (line 258-262)
- **Approach**:
  1. Remove the `(hF : forall x, Integrable (F x))` argument from `torus_hSpatialVelocityFubini`.
  2. Check callers: `TorusInstance.lean` passes this helper to the `hSpatialVelocityFubini` field. Since the abstract field already lacks this parameter, the instance proof may use `fun F hF_joint => torus_hSpatialVelocityFubini F hF_joint` -- removing the dead parameter should simplify the instance proof, not break it.
  3. Verify with `lake env lean` on TorusDefs.lean and TorusInstance.lean.
- **Risk**: Low. The abstract interface is unchanged; only the concrete helper loses an unused argument.
- **Resolves**: Critique issue 9b.

### 3. Fix stale docstring in Defs.lean (`/simplify`)
- **What**: Critique issue 8a. Defs.lean:378 says "hSpatialVelocityFubini is stated without explicit integrability hypothesis at the abstract level" -- this is false. The actual definition (lines 481-484) takes `Integrable (Function.uncurry F)` as an explicit hypothesis.
- **File**: `/home/vilin/aristotle/Aristotle/Landau/main/Defs.lean` (line 378-379)
- **Approach**: Rewrite the sentence to accurately describe the current state: hSpatialVelocityFubini takes joint integrability of `uncurry F` as its hypothesis.
- **Risk**: None. Pure documentation fix.
- **Resolves**: Critique issue 8a.

### 4. Attempt to eliminate maxHeartbeats 400000 in TorusIntegration.lean (`/simplify`)
- **What**: Critique issue 7a. The sole remaining `maxHeartbeats` override is on `integral_derivative_periodic_zero` (TorusIntegration.lean:85). This is a Fubini-based FTC argument over the 3D box. The critique notes this "may be hard to eliminate."
- **File**: `/home/vilin/aristotle/Aristotle/Landau/main/TorusIntegration.lean` (line 85)
- **Approach**:
  1. Profile the proof with `/profile` to find the expensive tactic.
  2. Try targeted strategies: replace `simp` with explicit rewrites, add type annotations to reduce unification, break out intermediate `have` steps.
  3. If the heartbeats drop below 200000, remove the override. If not, leave it and note in backlog.
- **Risk**: Medium. The override is 2x default (400000 vs 200000). The proof involves nested Fubini decomposition over `Fin 3 -> R` which is inherently expensive for the elaborator.
- **Resolves**: Critique issue 7a (if successful).

### 5. Update MEMORY.md project statistics (`/simplify`)
- **What**: Critique issue 8c. MEMORY.md says "22 files, ~8,700 lines" but actual is 32 files, 9,599 lines. The Coulomb file inventory lists 7 files but there are 12. Individual line counts are stale (reflecting the pre-split structure).
- **File**: `/home/vilin/.claude/projects/-home-vilin-aristotle/memory/MEMORY.md`
- **Approach**: Update all file counts, line counts, and the Coulomb file inventory to match current `wc -l` output. Update sorry status to say "32 files, ~9,600 lines".
- **Risk**: None. Pure documentation.
- **Resolves**: Critique issue 8c.

### 6. Run critique cycle 116
- **What**: After completing items 1-5, run `/critique` to verify all issues are resolved. The target is ACCEPT with 0 conditions.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| Weaken hypothesis 4 from `ContDiff R top` to `ContDiff R 3` | Strengthen | Critique 9a. Low priority: does not affect soundness, and `hSchwartz` implies C-infinity anyway. |
| CoulombNonvacuous should import main theorem and apply it | Strengthen | Critique 9d. Currently proves hypotheses satisfiable but doesn't produce the equilibrium conclusion. |
| Section3Helpers.lean 613 lines | Code quality | Just over 500-line guideline; contents are tightly coupled, splitting would be artificial. |
| 12 long lines across 5 files | Code quality | Critique 7d. Trivial formatting. |
| Dimension generalization (Fin n) | Feature | Hard; 3D is hard-coded everywhere (cross product, Killing equation, Coulomb kernel). |
| Multi-species | Feature | Hard; requires coupling multiple distribution functions and cross-species entropy estimates. |
| Mathlib PR candidates (5 lemmas) | Upstream | `inverse_poly_integrable`, `schwartz_pointwise_decay`, `schwartz_fderiv_component_decay`, `norm_fderiv_eq_iteratedFDeriv_one`, `poly_mul_gaussian_le`. |
| IsMaxwellian API | Mathematical | Add `IsMaxwellian.unique` or `IsMaxwellian.integrable`. Nice-to-have. |
