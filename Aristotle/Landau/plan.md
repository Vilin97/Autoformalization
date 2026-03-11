# Plan — Cycle 67

## Status summary

- **Sorry count**: 3 (all in `CoulombConcreteTheorem42_nonvacuous`, goals 7, 10, 12)
- **Files**: 22 files, 7,984 lines
- **Heartbeat overrides**: 1 (`synthInstance.maxHeartbeats 160000`)
- **Build**: Clean, 0 errors
- **Critique verdict**: CONDITIONAL ACCEPT — fix MEMORY.md, no new sorry's
- **Aristotle jobs**: 0 pending

## Active multi-cycle strategies

### Non-vacuousness theorem (cycles 64–67)
3 remaining sorry goals after cycle 66 closed (8), (9), (11):

| Goal | What to prove | Difficulty | Approach |
|------|---------------|------------|----------|
| (12) | `∫ eM dv = ρ_ion` | **Medium-Hard** | Gaussian integral `∫ exp(-|v|²/(2T)) = (2πT)^{3/2}` cancels prefactor |
| (7) | `UniformSchwartzDecay eM` | **Hard** | Iterated fderiv of Gaussian is polynomial × Gaussian → decay |
| (10) | `0 = ν * LandauOperator eM` | **Hardest** | Maxwellian in nullspace of Landau operator |

### Spatial smoothness (deferred)
Design documented in `experiments/spatial_smoothness_design.md`. ~95 call-site refactor. Low priority.

## This cycle's work items

### 1. Fix MEMORY.md — stale documentation (`/simplify`)
- **Why**: Critique flagged sorry count (says 6, actual 3), line counts wrong.
- **Immediate**: Update sorry count, file line counts, CoulombConcreteTheorem42 line count.

### 2. Prove sorry (12) — Gaussian integral normalization (`/prove`)
- **Why**: Most tractable of the 3 remaining. Pure computation.
- **File**: `CoulombConcreteTheorem42.lean` line ~452
- **Goal**: `∀ x, torusDivX (fun _ => (0 : Fin 3 → ℝ)) x = (∫ v, eM v) - ρ_ion`
- **Approach**: LHS simplifies to `0 = ∫ eM dv - ρ_ion`, so need `∫ eM dv = ρ_ion`. The prefactor `ρ/(2πT)^{3/2}` is chosen exactly so this holds. Need:
  1. `∫ exp(-normSq(v)/(2T)) dv = (2πT)^{3/2}` — product of 3 Gaussian integrals
  2. Pull out constant prefactor: `∫ eM = ρ/(2πT)^{3/2} * (2πT)^{3/2} = ρ`
  3. With `ρ = ρ_ion`, done.
- **Key Mathlib**: `MeasureTheory.integral_gaussian` or `integral_exp_neg_sq` for 1D Gaussian, then Fubini for product.

### 3. Attempt sorry (7) — UniformSchwartzDecay for Gaussian (`/prove`)
- **Why**: If (12) is closed quickly, attempt decomposition of (7).
- **Approach**: Decompose into sub-lemmas:
  1. `iteratedFDeriv ℝ k (equilibriumMaxwellian ρ T) v = P_k(v) * eM(v)` where P_k is polynomial of degree k
  2. `‖P_k(v) * eM(v)‖ * (1+‖v‖)^N ≤ C` — polynomial × Gaussian decays
  3. Combine for UniformSchwartzDecay
- Even if the full proof isn't possible, decomposition into well-typed sub-lemmas is progress.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| #6: 5 files over 600 lines | Code quality | TorusInstance 816, Defs 785, CoulombPSD 703 |
| Sorry (10): Landau nullspace | Epistemic | Hardest — needs collision operator analysis |
| #21: C^∞ spatial smoothness | Epistemic | Deferred |
