# Plan — Cycle 89

## Status summary

- **Sorry count**: 0
- **Files**: 27 files, ~9,492 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Split CoulombSpatialTransport.lean (676 lines) (`/simplify`)
- **What**: CoulombSpatialTransport.lean is now the largest file. Split at line ~337: extract the first part (torusGradX_aestronglyMeasurable, spatial_transport_integrable, force_fderiv_log_component_integrable, force_transport_integrable_coulomb, force_ibp_f_dg_integrable_coulomb, force_ibp_fg_integrable_coulomb) into CoulombForceTransport.lean. Keep the second part (gradX_stronglyMeasurable_v, spatial_transport_joint_integrable, spatial_transport_continuous) in CoulombSpatialTransport.lean.
- **Why**: Issue 6b. Reduces files over 600 lines from 5 to 4.

### 2. Implement UniformC2Decay weakening (`/strengthen`)
- **What**: Issue 8g. Replace `UniformSchwartzDecay` (all k) with `UniformC2Decay` (k ≤ 2) based on the analysis from cycle 88. This is a mechanical change touching ~10 files.
- **Why**: Makes the formalization applicable to a strictly larger class of distributions (C² with rapid decay, not just Schwartz class).

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 5 files over 600 lines | Code quality — ongoing, splitting 1 per cycle |
| 8b | Weaken C^∞ → C^2 | Epistemic — hard, deferred |
| 8c | Generalize beyond T^3 | Epistemic — hard |
| 8d | Mathlib PR for helper lemmas | Community — `iteratedFDeriv_clm_zero`, `norm_iteratedFDeriv_one_clm` ready |
| 8g | UniformSchwartzDecay → UniformC2Decay | Epistemic — analyzed, implementing this cycle |
