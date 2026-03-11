# ContDiff Regularity Analysis (Cycle 90)

## Question
Can we weaken `ContDiff ℝ ⊤` (C^∞) to finite regularity (e.g., C^2) in the main theorem?

## Analysis

### Three regularity tiers in the project

| Tier | Regularity | Where used | Why |
|------|-----------|------------|-----|
| Torus geometry | ContDiff ℝ 1–2 | TorusInstance, torus helpers | Smooth manifold structure, gradients |
| Abstract VML | ContDiff ℝ 3 | Section2–Section8, VMLInputDerive | Score bound via `fderiv.log`, chain rule needs C^3 |
| Coulomb concrete | ContDiff ℝ ⊤ | CoulombFluxDiff, CoulombConcreteTheorem42 | Singular kernel convolutions |

### Why ContDiff ⊤ is necessary for Coulomb

The Coulomb kernel `K(z) = z / ‖z‖³` has singularity `‖z‖⁻²`. Key lemmas:

1. **`schwartz_fderiv_component_schwartz`** — needs `iteratedFDeriv ℝ (k+1) (f x)` for `k ≤ 1`, so needs C^2 in velocity.
2. **`coulomb_entry_conv_hasFDerivAt_aux`** — uses `hasFDerivAt_integral_of_dominated_of_fderiv_le`, which requires differentiability of the integrand w.r.t. parameter. This needs C^1 of the convolution, which requires C^2 of f (one derivative "absorbed" by the convolution).
3. **`coulomb_flux_deriv_schwartz_decay`** — the Schwartz decay of the flux derivative uses arbitrary polynomial decay of f, which requires C^∞.

The critical bottleneck is item 3: the proof of `coulomb_flux_deriv_schwartz_decay` establishes `‖fderiv(flux_i)(v)‖ * (1+‖v‖)^N ≤ C` for **all** N. This Schwartz-class decay is essential for the IBP integrability argument. The bound comes from:
- The flux derivative being a convolution of `‖z‖⁻¹` (locally integrable) with derivatives of Schwartz functions
- Schwartz decay requires all seminorms bounded, which needs all derivatives of f to exist

### Could we weaken to C^k for finite k?

In principle, if we only need decay `(1+‖v‖)^N` for specific N values, we could get away with C^(N+3) or similar. However:
- The abstract VML framework (`Section3.lean`) uses `UniformSchwartzDecay` which quantifies over all N
- Changing this would require reworking the entire abstract framework, not just the Coulomb instantiation
- The mathematical literature (Villani, Alexandre–Villani) also assumes C^∞ for the Landau equation

### Conclusion

**ContDiff ℝ ⊤ cannot be meaningfully weakened for the Coulomb case** without a major restructuring of the abstract framework. The C^∞ requirement is mathematically natural for Schwartz-class solutions of the Landau equation.

## Status: COMPLETE — issue 8b documented as inherent limitation
