# Plan — Cycle 66

## Status summary

- **Sorry count**: 6 (all in `CoulombConcreteTheorem42_nonvacuous`, goals 7-12)
- **Files**: 22 files, 7,921 lines
- **Heartbeat overrides**: 1 (`synthInstance.maxHeartbeats 160000`)
- **Build**: Clean, 0 errors
- **Critique verdict**: CONDITIONAL ACCEPT — close ≥2 more sorry's, prioritize (8) and (9)

## Active multi-cycle strategies

### Non-vacuousness theorem (cycles 64-66)
6 remaining sorry goals. Updated difficulty after cycle 65 analysis:

| Goal | What to prove | Difficulty | Approach |
|------|---------------|------------|----------|
| (9) | `|∂eM/∂vᵢ| ≤ (1/T)(1+‖v‖) * eM` | **Medium** | Compute fderiv of Gaussian: `∂eM/∂vᵢ = -(vᵢ/T)*eM`, then `|vᵢ| ≤ 1+‖v‖` |
| (8) | `exp(-C(1+‖v‖)^K) ≤ eM` | **Medium** | Use `normSq v ≤ 3‖v‖²`, choose C = 3/(2T) - log(prefix), K = 2 |
| (11) | `∫ vᵢ * eM dv = 0` | **Medium** | Odd function × even Gaussian integrand → 0 (needs symmetry argument) |
| (12) | `∫ eM dv = ρ_ion` | **Hard** | Gaussian integral `∫ exp(-|v|²/(2T)) = (2πT)^(3/2)` |
| (7) | `UniformSchwartzDecay eM` | **Hard** | Iterated fderiv of Gaussian is polynomial × Gaussian |
| (10) | `0 = ν * LandauOperator eM` | **Hard** | Maxwellian in nullspace of Landau operator |

### Spatial smoothness (deferred)
Design documented in `experiments/spatial_smoothness_design.md`. ~95 call-site refactor. Low priority.

## This cycle's work items

### 1. Close sorry (9) — gradient bound (`/prove`)
- **Why**: Critique acceptance condition. Most tractable of the remaining 6.
- **File**: `CoulombConcreteTheorem42.lean`
- **Approach**:
  1. Compute `fderiv ℝ normSq v (Pi.single i 1) = 2 * v i` (bilinear form derivative)
  2. Chain rule: `fderiv ℝ eM v (eᵢ) = eM(v) * (-v_i / T)`
  3. Bound: `|v_i| / T ≤ (1 + ‖v‖) / T`
  4. Choose `Cg = 1/T, Kg = 1`
- **Key Mathlib lemmas**: `HasFDerivAt.exp`, `fderiv_inner_apply` or manual bilinear, `norm_le_pi_norm`

### 2. Close sorry (8) — exponential decay bound (`/prove`)
- **Why**: Algebraic, no integrals needed.
- **Approach**:
  1. Helper: `normSq v ≤ 3 * ‖v‖ ^ 2` (sup norm on Fin 3 → ℝ)
  2. Helper: `∃ C, exp(-C) ≤ ρ_ion / (2πT)^(3/2)` (via `Real.exp_log`)
  3. Choose `C₀ = 3/(2T) + max 0 (-Real.log prefix)`, K = 2
  4. Show: `exp(-C₀(1+‖v‖)²) ≤ prefix * exp(-normSq(v)/(2T))`

### 3. Attempt sorry (11) — Ampere (odd integral vanishes) (`/prove`)
- **Why**: If time allows after (8) and (9). Uses symmetry, no hard analysis.
- **Approach**: Show `fun v => v i * eM v` is odd in vᵢ; use `MeasureTheory.integral_comp_neg` or manual symmetry.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| #6: 5 files over 600 lines | Code quality | TorusInstance 816, Defs 785, CoulombPSD 703 |
| #18: long lines | Cosmetic | Low priority |
| #21: C^∞ spatial smoothness | Epistemic | Deferred |
| Sorry's (7)(10)(12) | Epistemic | Hard — Schwartz, Landau nullspace, Gaussian integral |
