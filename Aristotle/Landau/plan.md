# Plan — Cycle 65

## Status summary

- **Sorry count**: 10 (all in `CoulombConcreteTheorem42_nonvacuous`, non-critical)
- **Files**: 22 files, 7,888 lines
- **Heartbeat overrides**: 1 (`synthInstance.maxHeartbeats 160000` in CoulombSpatialTransport.lean)
- **Build**: Clean, 0 errors
- **Critique verdict**: CONDITIONAL ACCEPT — close ≥2 non-vacuousness sorry's or make progress on file splitting

## Active multi-cycle strategies

### Non-vacuousness theorem (started cycle 64)
10 sorry goals for hypotheses (4)-(13) of `CoulombConcreteTheorem42_nonvacuous`. Difficulty assessment:

| Goal | Hypothesis | What to prove | Difficulty |
|------|-----------|---------------|------------|
| (13) | hDivB | `torusDivX (fun _ => 0) = 0` | **Trivial** — fderiv of constant = 0 |
| (6)  | hB_smooth | `periodicLift (fun _ => 0) is C^∞` | **Easy** — constant function |
| (5)  | hf_smooth_x | `periodicLift (fun _ => eM ρ T v) is C^∞` | **Easy** — constant function (same as 6) |
| (4)  | hf_smooth_v | `eM ρ T is C^∞` | **Medium** — composition: const, normSq, exp, div |
| (8)  | hExpDecay | `exp(-C(1+‖v‖)^K) ≤ eM` | **Medium** — algebraic + (1+‖v‖)² ≥ normSq |
| (12) | hGauss | `∫ eM dv = ρ_ion` | **Hard** — Gaussian integral normalization |
| (11) | hAmpere | `∫ vᵢ eM dv = 0` | **Hard** — odd integral vanishes |
| (9)  | hGradBound | `|∂eM/∂vᵢ| ≤ poly * eM` | **Hard** — fderiv of Gaussian |
| (7)  | hSchwartz | Gaussian is UniformSchwartzDecay | **Hard** — iterated fderiv decay |
| (10) | hVlasov | `0 = ν * Q(eM)` | **Hard** — Landau operator nullspace |

### C^∞ → C^k weakening (velocity done, spatial deferred)
Velocity smoothness weakened to C³ in cycle 63. Spatial smoothness still C^∞, blocked by `hDiff_grad` typeclass design. Deferred.

## This cycle's work items

### 1. Close sorry's (13), (6), (5) — three easiest goals (`/prove`)
- **Why**: Critique #8 acceptance condition. These three are clearly provable right now.
- **File**: `CoulombConcreteTheorem42.lean`
- **Approach**: Replace `all_goals sorry` with individual tactic blocks:
  - (13): unfold `torusDivX`, show fderiv of constant = 0, sum of zeros = 0
  - (6): unfold `periodicLift`, `(0 : Fin 3 → ℝ) i = 0`, `contDiff_const`
  - (5): same as (6) — `equilibriumMaxwellian ρ_ion T v` doesn't depend on x

### 2. Attempt sorry (4) — Maxwellian is C^∞ (`/prove`)
- **Why**: Should be doable with Mathlib's `ContDiff` API.
- **Approach**: `contDiff_const.div contDiff_const ≠ 0` for prefix, `ContDiff.exp` for the exponential, `ContDiff.neg`, `contDiff_normSq` or manual proof.

### 3. Attempt sorry (8) — exponential decay bound (`/prove`)
- **Why**: Algebraic, no Gaussian integral needed.
- **Approach**: Choose `C = 1/(2T), K = 2`. Show `exp(-(1/(2T))(1+‖v‖)²) ≤ eM(v)` by comparing exponents and using positivity of the prefactor `ρ/(2πT)^(3/2)`.

### 4. Fix MEMORY.md line count drift (`/simplify`)
- **Why**: Critique #7. Says ~8,300 lines, actual 7,888.
- **Approach**: Update the number.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| #6: 6 files over 600 lines | Code quality | TorusInstance 816, Defs 785, CoulombPSD 703 |
| #18: multiGoal violations, long lines | Cosmetic | Low priority |
| #21: C^∞ spatial smoothness overkill | Epistemic | Blocked by typeclass design |
| Sorry's (7)(9)(10)(11)(12) | Epistemic | Hard, need Gaussian integrals / Landau nullspace |
