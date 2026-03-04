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

The proof is complete modulo 2 sorry's: velocity-space IBP
for the Landau operator, and the global entropy production identity
(both require velocity-space analysis beyond current Mathlib).

---

## File Structure

- `Defs.lean` — FlatTorus3 typeclass, structures (VMLSteadyState, VMLEquilibrium, VMLInput), base definitions
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

- **Lemma 11** (Global entropy production vanishes): `global_entropy_production_zero`
- **Lemma 12** (Pointwise D = 0): `pointwise_entropy_dissipation_zero`
- **Corollary 2** (Local Maxwellian): `steady_state_is_local_maxwellian`

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

### Category 1: Velocity-space IBP (1 sorry in Theorem42.lean)

1. **`hIBP`** — IBP for the Landau operator:
   ∫ Q(f,f)(v) log f(v) dv = -∫∫ ⟨∇ log f(v), A(v-w) · flux⟩ dw dv.
   Requires integration by parts in velocity space with Schwartz-class decay.

### Category 2: Global entropy identity (1 sorry in Section4.lean)

2. **`transport_entropy_from_vlasov`** (Section4.lean) — ∫_X D(f)(x) dx = 0.
   Multiply Vlasov by log f, integrate over v and X. Spatial transport vanishes
   by Stokes on T³, Lorentz force term vanishes by velocity-space IBP and
   div_v(E + v×B) = 0.

Both sorry's trace to the same root: **vector IBP on ℝ³** with Schwartz-class decay,
which is beyond current Mathlib.

---

## Architecture

The `FlatTorus3` typeclass bundles all spatial domain axioms (gradX, divX, curlX,
spatialIntegral, Stokes, harmonic->constant, Killing->harmonic, Laplacian sign at extrema, etc.).

The proof flows through three layers:

1. **Theorem42** (user-facing): Takes physical + decay hypotheses over `[FlatTorus3 X]`.
   Derives mathematical consequences via sorry'd lemmas. Constructs VMLInput.

2. **VMLInput -> main_from_physics**: Physical hypotheses + analytical interface.
   Derives VMLSteadyState.

3. **VMLSteadyState -> main_steady_state** (algebraic core): All analytical work done.
   Proves u = 0, E = 0, B = const, T > 0.

---

## Theorem42 Hypotheses

**Physical** (14): f > 0, f smooth, f integrable, nu > 0, rho_ion > 0, Psi > 0,
Psi continuous, rho = integral f, J = integral vf, rho continuous, Vlasov equation, Maxwell equations.

**Domain** (via `[FlatTorus3 X]`): Stokes theorem, harmonic->constant, Killing->harmonic,
gradient/divergence/curl properties, Laplacian sign at extrema, spatial integral properties.

**Velocity-space decay** (5): PSD integrand integrability (inner and outer),
Fubini integrability for symmetrized weak form (double, inner, outer).
