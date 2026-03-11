# Plan — Cycle 90

## Status summary

- **Sorry count**: 0
- **Files**: 28 files, ~9,505 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Split CoulombFluxDiff.lean (637 lines) (`/simplify`)
- **What**: CoulombFluxDiff.lean is the second largest file. Split at line ~354: extract the first part (schwartz_fderiv_component_schwartz, coulomb_entry_schwartz_integrable, coulomb_entry_conv_hasFDerivAt_aux, coulomb_entry_conv_differentiable, coulomb_entry_conv_deriv_bounded, coulomb_flux_differentiable, coulomb_flux_eq_decomposed) into CoulombFluxConv.lean. Keep the second part (coulomb_flux_deriv_schwartz_decay, coulomb_ibp_df_g_integrable) in CoulombFluxDiff.lean.
- **Why**: Issue 6b. Reduces files over 600 lines from 4 to 3.

### 2. Weaken ContDiff hypothesis — scope analysis (`/strengthen`)
- **What**: Issue 8b. The concrete theorem uses `ContDiff ℝ ⊤` (C^∞) for f, E, B. The proof only needs finite regularity. Audit exactly which `ContDiff` orders are used and document the minimum required.
- **Why**: Understanding the minimum regularity is the prerequisite for any future weakening.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 4 files over 600 lines | Code quality — ongoing, splitting 1 per cycle |
| 8b | Weaken C^∞ → C^2 | Epistemic — hard, analyzing this cycle |
| 8c | Generalize beyond T^3 | Epistemic — hard |
| 8d | Mathlib PR for helper lemmas | Community — ready |
