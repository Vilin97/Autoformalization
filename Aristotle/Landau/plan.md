# Plan — Cycle 115

## Status summary

- **Sorry count**: 0
- **Files**: 32 files, 9,598 lines
- **Build**: Clean, 0 errors, 0 warnings
- **Critique verdict**: ACCEPT (cycle 114, no conditions)
- **maxHeartbeats overrides**: 0
- **`simp +decide`**: 0
- **`aesop`**: 0
- **Aristotle jobs**: 0 pending (all resolved or abandoned)
- **Working tree**: clean (only critique.md modified, state.md untracked)
- **Open issues**: all low severity (MEMORY.md staleness, hypothesis tightening, 1 long line)

## This cycle's work items

### 1. Update MEMORY.md project statistics (`/simplify`)
- **What**: Critique issues 8a, 8b, 8c (persisting since cycle 112). MEMORY.md says "22 files, ~8,700 lines" but actual is 32 files, 9,598 lines. The Coulomb file inventory lists 7 files but there are 12. Individual line counts are 3-4x off from reality (reflecting the pre-split structure).
- **File**: `/home/vilin/.claude/projects/-home-vilin-aristotle/memory/MEMORY.md`
- **Approach**:
  1. Replace "22 files, ~8,700 lines" with "32 files, ~9,600 lines" in all occurrences.
  2. Replace the 7-file Coulomb list with the full 12-file list and current `wc -l` counts:
     - `CoulombKernel.lean` (117), `CoulombSpatialTransport.lean` (414), `CoulombForceTransport.lean` (332), `NewtonianPotential.lean` (436), `CoulombFlux.lean` (186), `CoulombFluxBound.lean` (465), `CoulombFluxConv.lean` (373), `CoulombFluxDiff.lean` (250), `CoulombPSD.lean` (298), `CoulombPSDHelpers.lean` (428), `CoulombConcreteTheorem42.lean` (241), `CoulombNonvacuous.lean` (351)
  3. Update other stale line counts (SchwartzDecayDefs 213, VelocityDecayInstance 71, etc.)
  4. Update sorry status section to say "32 files, ~9,600 lines"
- **Resolves**: Critique issues 8a, 8b, 8c.
- **Can start immediately**: yes, pure documentation edit.

### 2. Weaken hypothesis 4 from `ContDiff R top` to `ContDiff R 3` (`/strengthen`)
- **What**: Critique issue 9a. The concrete theorem `CoulombConcreteTheorem42` requires `ContDiff R top (f x)` for velocity smoothness but the abstract chain (`VMLStructures`, `Theorem42`) only needs `ContDiff R 3`. The coercion happens at line 205 via `.of_le le_top`. Weakening the hypothesis makes the theorem statement tighter: it asserts that C3 velocity regularity suffices.
- **Files**: `CoulombConcreteTheorem42.lean` lines 72 and 215 (both theorem statements)
- **Approach**:
  1. Change `ContDiff ℝ ⊤ (f x)` to `ContDiff ℝ 3 (f x)` in both `CoulombConcreteTheorem42` (line 72) and `CoulombConcreteTheorem42_unique_T` (line 215).
  2. At line 205, the `.of_le le_top` coercion becomes unnecessary — replace with direct pass-through.
  3. Check if any Coulomb-specific file (CoulombFlux, CoulombPSD, etc.) uses `hf_smooth_v` directly. If they do, verify they only need C3 or less. Based on critique analysis, they derive regularity from `hSchwartz` instead.
  4. Verify with `lake env lean Aristotle/Landau/main/CoulombConcreteTheorem42.lean`.
  5. Update the docstring (lines 52-58) to note that C3 suffices.
- **Risk**: Low. The critique confirms the coercion is the only use site. If a Coulomb file does need C-infinity from `hf_smooth_v` (unlikely), revert.
- **Resolves**: Critique issue 9a.

### 3. Remove unused first argument from `hSpatialVelocityFubini` (`/strengthen`)
- **What**: Critique issue 9b. The `hSpatialVelocityFubini` field in `FlatTorus3` takes `(forall x, Integrable (F x))` as its first argument after `F`, but the concrete instance (TorusInstance line 439) discards it, and the single call site (Section4 line 298) must supply it anyway. Removing it makes the abstract axiom strictly weaker.
- **Files**: `Defs.lean` (line 480-484), `Section4.lean` (line 298), `TorusInstance.lean` (line 439), `TorusDefs.lean` (line 256-258)
- **Approach**:
  1. In `Defs.lean` line 480-484, remove the `(forall x, MeasureTheory.Integrable (F x)) ->` argument.
  2. In `Section4.lean` line 298, remove the `hSpatialTransport_int` argument from the call.
  3. In `TorusInstance.lean` line 439, update the instance proof (likely just remove `intro _`).
  4. In `TorusDefs.lean`, update `torus_hSpatialVelocityFubini` signature to match.
  5. Verify with `lake env lean` on all four files.
- **Risk**: Low-medium. Need to verify that removing the argument doesn't break the concrete Fubini proof in `TorusInstance`. The concrete proof uses `MeasureTheory.integral_integral_swap` which requires joint integrability (still provided) but may also need per-section integrability internally. If so, derive it from joint integrability inside the proof.
- **Resolves**: Critique issue 9b.

### 4. Fix Defs.lean line length violation (`/simplify`)
- **What**: Critique issue 7f. Line 98 of Defs.lean exceeds the 100-character soft limit.
- **File**: `Defs.lean`, line 98
- **Approach**: Break the `have h0` line into two lines. Trivial formatting fix.
- **Resolves**: Critique issue 7f.

### 5. Run critique cycle 115
- **What**: After completing items 1-4, run `/critique` to verify all issues are resolved and update the summary table.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| Section3Helpers.lean 613 lines | Code quality | Just over 600-line limit; contents are tightly coupled, splitting would be artificial. Leave as-is. |
| Dimension generalization (Fin n) | Feature | Hard; 3D is hard-coded everywhere (cross product, Killing equation, Coulomb kernel). |
| Multi-species | Feature | Hard; requires coupling multiple distribution functions and cross-species entropy estimates. |
| Mathlib PR candidates | Upstream | 5 lemmas: `inverse_poly_integrable`, `schwartz_pointwise_decay`, `schwartz_fderiv_component_decay`, `second_deriv_nonpos_at_local_max'`, `norm_fderiv_eq_iteratedFDeriv_one`. |
| IsMaxwellian API | Mathematical | Add `IsMaxwellian.unique` or `IsMaxwellian.integrable`. Nice-to-have, no urgency. |
