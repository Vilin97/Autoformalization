# Plan — Cycle 68

## Status summary

- **Sorry count**: 2 (both in `CoulombConcreteTheorem42_nonvacuous`)
- **Files**: 22 files, ~8,000 lines
- **Build**: Clean, 0 errors
- **Critique verdict**: CONDITIONAL ACCEPT — close (7) hDecay
- **Aristotle jobs**: 0 pending

## Active multi-cycle strategies

### Non-vacuousness theorem (cycles 64–68)
2 remaining sorry goals:

| Goal | What to prove | Difficulty | Approach |
|------|---------------|------------|----------|
| (7) hDecay | `‖iteratedFDeriv ℝ k eM v‖ * (1+‖v‖)^N ≤ C` | **Medium-Hard** | `norm_iteratedFDeriv_comp_le` + polynomial×Gaussian bound |
| (10) hVlasov | `0 = ν * LandauOperator coulombKernel eM` | **Hardest** | Maxwellian in nullspace of Landau operator |

## This cycle's work items

### 1. Prove sorry (7) hDecay — polynomial×Gaussian bound (`/prove`)
- **Why**: Critique acceptance condition. Identified sub-lemmas in cycle 67.
- **File**: `CoulombConcreteTheorem42.lean` line ~429
- **Strategy (two sub-lemmas)**:

  **Sub-lemma A**: `poly_mul_exp_bounded` — `∀ M a > 0, ∃ C, ∀ u ≥ 0, (1+u)^M * exp(-a*u²) ≤ C`
  - Split: u ≤ 1 → bound by 2^M; u > 1 → use u² ≥ u, then `(2u)^M * exp(-a*u) → 0`
  - Use `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero` for the limit
  - Extract bound from the limit via `Metric.tendsto_atTop` or `Filter.Tendsto.eventually`

  **Sub-lemma B**: iterated derivative bound via `norm_iteratedFDeriv_comp_le`
  - `eM = const * (exp ∘ q)` where `q(v) = -normSq(v)/(2T)`
  - `‖iteratedFDeriv ℝ i exp (q v)‖ = |exp(q v)|` for all i (exp is its own derivative)
  - `‖iteratedFDeriv ℝ i q v‖ ≤ D^i` where D ≈ c*(1+‖v‖) (q is quadratic: zero for i ≥ 3)
  - Result: `‖iteratedFDeriv ℝ n eM v‖ ≤ n! * |eM v| * (c(1+‖v‖))^n`

  **Combine**: `n! * |eM v| * c^n * (1+‖v‖)^n * (1+‖v‖)^N ≤ n! * c^n * C_{n+N}` via sub-lemma A

## Backlog

| Issue | Category | Notes |
|-------|----------|-------|
| #6: 5 files over 600 lines | Code quality | TorusInstance 816, Defs 785, CoulombPSD 703 |
| Sorry (10): Landau nullspace | Epistemic | Hardest — needs collision operator analysis |
