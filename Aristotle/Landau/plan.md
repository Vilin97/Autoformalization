# Plan — Cycle 88

## Status summary

- **Sorry count**: 0
- **Files**: 26 files, ~9,476 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: ACCEPT
- **Aristotle jobs**: 0 pending

## This cycle's work items

### 1. Split CoulombPSD.lean (826 lines) (`/simplify`)
- **What**: CoulombPSD.lean is the largest file. Look for a natural split point — it contains PSD continuity, pointwise bounds, inner/outer integrability, and Fubini lemmas. Extract the inner/outer integrability or Fubini portion into a separate file.
- **Why**: Issue 6b. Reduces files over 600 lines from 6 to 5.

### 2. Experiment: weaken UniformSchwartzDecay (`/strengthen`)
- **What**: Issue 8g. UniformSchwartzDecay requires ALL derivatives decay faster than ANY polynomial. The proof only needs specific integrals to converge. Prototype a weaker decay condition in `experiments/` and check if VelocityDecayConditions can still be verified.
- **Why**: Makes the formalization applicable to a strictly larger class of distributions.

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| 6b | 6 files over 600 lines | Code quality — ongoing, splitting 1 per cycle |
| 8b | Weaken C^∞ → C^2 | Epistemic — hard, deferred |
| 8c | Generalize beyond T^3 | Epistemic — hard |
| 8d | Mathlib PR for helper lemmas | Community — `iteratedFDeriv_clm_zero`, `norm_iteratedFDeriv_one_clm` ready |
| 8g | UniformSchwartzDecay stronger than needed | Epistemic — medium, experimenting this cycle |
