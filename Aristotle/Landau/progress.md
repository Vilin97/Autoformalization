# Formalization Progress: Global Steady State of the VML System

**Files**: `Aristotle/Landau/main/*.lean` (split across 11 files)
**Blueprint**: `Aristotle/Landau/H-theorem-formal.tex` (Sections 1--10)
**Status**: 0 errors, 2 sorry's

## Summary

The formalization proves Theorem 42 (= Theorem 12 in the blueprint):
any smooth steady state (f, E, B) of the Vlasov--Maxwell--Landau system
on T^3 x R^3 with collision frequency nu > 0 must satisfy:

  (i)   f is a spatially uniform, zero-drift Maxwellian
  (ii)  E = 0
  (iii) B = const
  (iv)  T > 0 uniquely determined by conservation laws

The proof is complete modulo 2 sorry's: velocity-space IBP (`velocity_ibp`)
and Landau operator IBP (`landau_ibp`), both requiring velocity-space
analysis beyond current Mathlib.

---

## File Structure

- `Defs.lean` — FlatTorus3 typeclass (extends MeasureSpace X), structures (VMLSteadyState, VMLEquilibrium, VMLInput), base definitions
- `Section2.lean` — Algebraic lemmas (Landau matrix properties, Lemmas 1-3)
- `Section3.lean` — H-theorem chain + analysis lemmas (~1130 lines, Lemmas 4-9)
- `Section4.lean` — Transport constraints (Lemmas 10-12, Corollary 2)
- `Section5.lean` — Polynomial matching (Lemmas 13-17)
- `Section6.lean` — Bulk velocity (Lemmas 18-19)
- `Section7.lean` — Maximum principle (Lemmas 20-21, Corollary 3)
- `Section8.lean` — Magnetic field (Lemmas 22-23)
- `Section9.lean` — Conservation laws (Lemmas 24-28)
- `VMLInputDerive.lean` — VMLInput.toSteadyState, main_steady_state, main_from_physics
- `Theorem42.lean` — Main theorem statement + proof

---

## Proved Lemmas (by blueprint section)

### Section 2: Algebraic Lemmas about the Landau Matrix

- **Lemma 1(a)** (A is symmetric): `landauMatrix_symmetric`
- **Lemma 1(b)** (A is even): `landauMatrix_even`
- **Lemma 2** (A is PSD): `landauMatrix_posSemidef`, `landauMatrix_quadForm_eq_zero_iff`
- **Lemma 3** (Projection annihilation): `landauMatrix_mulVec_self`, `vecMul_landauMatrix_self`

### Section 3: The H-Theorem and Nullspace

- **Lemma 4** (Symmetrized weak form): `entropy_score_form`
- **Lemma 5** (Entropy dissipation formula): `entropy_dissipation_formula`
- **Theorem 3** (H-theorem: D(f) <= 0): `H_theorem`
- **Lemma 6** (D=0 implies parallelism): `D_zero_implies_parallel`
- **Lemma 7** (Parallel implies affine): `functional_eq_affine`, `parallel_curl_free_affine`
- **Lemma 8** (Affine gradient implies quadratic): `log_f_quadratic`, `affine_gradient_antiderivative`
- **Theorem 4** (Nullspace necessity): `nullspace_necessity`
- **Theorem 5** (Nullspace sufficiency): `nullspace_sufficiency`
- **Corollary 1** (Complete characterization): `nullspace_iff`

### Section 4: Vlasov--Maxwell Transport Constraints

- **Lemma 10** (Lorentz force div = 0): `lorentz_force_div_zero`
- **Lemma 11** (Global entropy production vanishes): `transport_entropy_from_vlasov`
- **Lemma 12** (Pointwise D = 0): derived in Theorem42

### Section 5: Polynomial Matching

- **Lemma 13** (Polynomial identity): `polynomial_identity_velocity`
- **Lemma 14** (Temperature constant): `temperature_constant`, `cubic_coeff_zero`
- **Lemma 15** (Bulk velocity constant): `bulk_velocity_constant`, `killing_constant_torus`
- **Lemma 16** (Force balance): `force_balance`, `force_balance_from_polynomial`
- **Lemma 17** (Zeroth-order term): `E_dot_u_zero`

### Section 6: Nullification of Bulk Velocity

- **Lemma 18** (Ampere at steady state): `ampere_steady_state`
- **Lemma 19** (u = 0): `bulk_velocity_zero`

### Section 7: Spatial Uniformity via Maximum Principle

- **Lemma 20** (Poisson--Boltzmann): `poisson_boltzmann_density`, `poisson_boltzmann_from_vlasov`
- **Lemma 21** (Density constant): `density_constant_max_principle`, `poisson_boltzmann_max_principle`
- **Corollary 3** (E = 0): `electric_field_zero`

### Section 8: Uniformity of the Magnetic Field

- **Lemma 22** (B constant): `magnetic_field_constant`
- **Lemma 23** (Compatibility): `B_compatible_maxwellian`

### Section 9: Conservation Laws

- **Lemma 24** (B mean conserved): `B_mean_conserved`
- **Lemma 25** (Energy conserved): `energy_conserved`
- **Lemma 26** (B_infty determined): `B_infty_determination`
- **Lemma 27** (T_infty determined): `T_infty_determination`
- **Lemma 28** (T > 0): `T_positive`

### Main Theorem Assembly

- `main_steady_state`: VMLSteadyState -> conclusion. **Fully proved.**
- `main_from_physics`: VMLInput -> conclusion. **Fully proved.**
- **Fubini symmetrization** (proved by Aristotle): `fubini_symmetrization_logf`
- `Theorem42`: Clean statement with physical hypotheses. **Proved modulo 2 sorry's.**

---

## Remaining Sorry's (2)

Both sorry's are in `Defs.lean` and concern velocity-space integration by parts:

1. **`velocity_ibp`** (Defs.lean:140) — General IBP on ℝ³:
   ∫ (∇·F)(v) · g(v) dv = -∫ F(v) · (∇g)(v) dv.
   Requires Fubini + 1D IBP in each coordinate direction.

2. **`landau_ibp`** (Defs.lean:175) — IBP for the Landau operator:
   ∫ Q(g,g)(v) log g(v) dv = -∫∫ ⟨∇ log g(v), A(v-w) · flux⟩ dw dv.
   Follows from `velocity_ibp` + `dotProduct_integral_comm`, but verifying
   the smoothness/integrability hypotheses requires differentiation under ∫.

Both now include decay hypotheses (h_decay / h_decay) ensuring boundary terms
vanish at velocity-space infinity. Earlier versions without decay were correctly
negated by Aristotle (counterexample: F=(1,0,0), g=arctan(v₀)·exp(-v₁²-v₂²)).

Submitted to Aristotle with decay hypotheses (projects 14f30222, 1ecdcc05).

---

## Architecture

The `FlatTorus3` typeclass extends `MeasureSpace X` and bundles spatial domain axioms
(gradX, divX, curlX, Stokes, harmonic→constant, Killing→harmonic, Laplacian sign at
extrema, etc.). Spatial integration uses Mathlib's `∫ x, ...` via the inherited measure.

The proof flows through three layers:

1. **Theorem42** (user-facing): Takes physical + decay hypotheses over `[FlatTorus3 X]`.
   Derives mathematical consequences. Constructs VMLInput.

2. **VMLInput → main_from_physics**: Physical hypotheses + analytical interface.
   Derives VMLSteadyState.

3. **VMLSteadyState → main_steady_state** (algebraic core): All analytical work done.
   Proves u = 0, E = 0, B = const, T > 0.

---

## FlatTorus3 Axioms (15)

The typeclass has 15 axioms, all justified for a flat 3-torus:

**Operator properties (5):** hDivLinear, hGradConst, hGradAdd, hGradScalarMul, hGradChainExp

**Closed manifold integration (2):** hCurlIntZero, hIBP_spatial

**Compact manifold analysis (4):** hHarmonic_const, hLaplacianMaxNonpos, hSpatialPos, hSpatialNonnegZero

**Flat geometry (2):** hKillingToHarmonic, hCurlZeroDivZeroHarmonic

**Abstract measure (2):** hSpatialVelocityFubini, hSpatialAdd

**Removed axioms:**
- hStokes (∫ div F = 0): removed — never used, derivable from hIBP_spatial + hSpatialAdd + hGradConst

**Derived lemmas (proved from axioms):**
- hGradChainLog (from hGradChainExp via exp(log g) = g)
- hGradIntZero (from hIBP_spatial + hGradConst + hSpatialAdd)
- hLaplacianMinNonneg (from hLaplacianMaxNonpos + hGradScalarMul + hDivLinear)
- hSpatialMul (from Mathlib's integral_mul_right)

---

## Theorem42 Hypotheses

**Physical** (14): f > 0, f smooth, f integrable, ν > 0, ρ_ion > 0, Ψ > 0,
Ψ continuous, ρ = ∫f, J = ∫vf, ρ continuous, Vlasov equation, Maxwell equations.

**Domain** (via `[FlatTorus3 X]`): 15 axioms for spatial operators and torus topology.

**Velocity-space decay** (9): PSD integrand integrability (inner, outer),
Fubini integrability for symmetrized weak form (double, inner, outer),
transport integrability (spatial transport, force transport),
Landau flux decay (boundary terms for landau_ibp),
force transport decay (boundary terms for velocity_ibp in entropy estimate).
