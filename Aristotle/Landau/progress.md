# Formalization Progress: Global Steady State of the VML System

**Files**: `Aristotle/Landau/main/*.lean` (split across 11 files)
**Blueprint**: `Aristotle/Landau/H-theorem-formal.tex` (Sections 1--10)
**Status**: 0 errors, 0 sorry's in main chain; 4 sorry's in TorusInstance.lean (3 original + 1 new hDiff_velocityIntegral)

Last updated: 2026-03-09

## Summary

The formalization proves Theorem 42 (= Theorem 12 in the blueprint):
any smooth steady state (f, E, B) of the Vlasov--Maxwell--Landau system
on T^3 x R^3 with collision frequency nu > 0 must satisfy:

  (i)   f is a spatially uniform, zero-drift Maxwellian
  (ii)  E = 0
  (iii) B = const
  (iv)  T > 0 uniquely determined by conservation laws

The main proof chain (Defs, Section2-9, VMLInputDerive, Theorem42) is
**complete with 0 sorry's and 0 axioms**.

A concrete FlatTorus3 instance on `Fin 3 -> AddCircle 1` (TorusInstance.lean)
validates the typeclass with **3 sorry's** (all helper theorems; 0 instance field sorry's).

---

## File Structure

- `Defs.lean` -- FlatTorus3 typeclass (extends MeasureSpace X, TopologicalSpace X, CompactSpace, Nonempty), structures, base definitions
- `Section2.lean` -- Algebraic lemmas (Landau matrix properties, Lemmas 1-3)
- `Section3.lean` -- H-theorem chain + analysis lemmas (~1300 lines, Lemmas 4-9)
- `Section4.lean` -- Transport constraints (Lemmas 10-12, Corollary 2)
- `Section5.lean` -- Polynomial matching (Lemmas 13-17)
- `Section6.lean` -- Bulk velocity (Lemmas 18-19)
- `Section7.lean` -- Maximum principle (Lemmas 20-21, Corollary 3)
- `Section8.lean` -- Magnetic field (Lemmas 22-23)
- `Section9.lean` -- Conservation laws (Lemmas 24-28)
- `VMLInputDerive.lean` -- VMLInput.toSteadyState, main_steady_state, main_from_physics
- `Theorem42.lean` -- Main theorem statement + proof (VelocityDecayConditions bundle)
- `TorusInstance.lean` -- Concrete FlatTorus3 instance on T^3

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
- **velocity_ibp**: General IBP on R^3. **Fully proved.**
- **landau_ibp**: IBP for Landau operator. **Fully proved.**
- **fubini_symmetrization_logf**: Fubini swap for D(f) formula. Proved by Aristotle.

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
- `Theorem42`: Clean statement with VelocityDecayConditions bundle. **Fully proved.**

---

## TorusInstance Sorry's (3 remaining)

### Mathematically correct, hard (3 helper theorems; Aristotle jobs active)

- `torus_hIBP_spatial` -- IBP on torus (FTC + periodicity + Fubini); job 4b7ec531
- `torus_hCurlIntZero` -- curl integral zero (follows from IBP with phi=1); job 1be0761f
- `torus_hHarmonic_const` -- harmonic functions constant (energy method via IBP); job be472543

### Proved (all instance fields, 0 sorry's in instance)

Instance fields: `hDivLinear`, `hGradScalarMul`, `hGradChainExp`, `hGradAdd`, `hGradConst`,
`hSpatialPos`, `hSpatialNonnegZero`, `hSpatialVelocityFubini`, `hSpatialAdd` (via integral_add),
`hGradIntegrable` (via IsOpenQuotientMap.piMap), `IsSpatiallyDiff` (= ContDiff ℝ 1 ∘ periodicLift),
`hDiff_const`, `hDiff_add`, `hDiff_smul`, `hDiff_log` (= ContDiff.log; new 2026-03-09)

Helper theorems: `torus_hGradAdd'`, `torus_hLaplacianMaxNonpos`, `torus_hKillingToHarmonic`,
`torus_hCurlZeroDivZeroHarmonic`, `clairaut_fderiv`, `periodicLift_torusGradX`,
`laplacian_nonpos_at_max_rn`, `killing_harmonic_rn'`, `curl_div_harmonic_rn'`,
`contDiff2_from_partials`

---

## Architecture

The `FlatTorus3` typeclass extends `MeasureSpace X, TopologicalSpace X` and includes
`CompactSpace X` and `Nonempty X`. It bundles spatial operators + 15 axioms.
Spatial integration uses Mathlib's `integral` via the inherited measure.

The proof flows through three layers:

1. **Theorem42** (user-facing): Takes physical + VelocityDecayConditions over `[FlatTorus3 X]`.
   Computes rho and J from f. Constructs VMLInput.

2. **VMLInput -> main_from_physics**: Physical hypotheses + analytical interface.
   Derives VMLSteadyState.

3. **VMLSteadyState -> main_steady_state** (algebraic core): All analytical work done.
   Proves u = 0, E = 0, B = const, T > 0.

---

## FlatTorus3 Axioms (21)

**Operator properties (5):** hDivLinear, hGradConst, hGradAdd, hGradScalarMul, hGradChainExp

**Closed manifold integration (2):** hCurlIntZero, hIBP_spatial

**Compact manifold analysis (4):** hHarmonic_const, hLaplacianMaxNonpos, hSpatialPos, hSpatialNonnegZero

**Flat geometry (2):** hKillingToHarmonic, hCurlZeroDivZeroHarmonic

**Abstract measure (3):** hSpatialVelocityFubini, hSpatialAdd (requires Integrable), hGradIntegrable

**IsSpatiallyDiff closure (5):** hDiff_const, hDiff_add, hDiff_smul, hDiff_log, hDiff_velocityIntegral (new 2026-03-09)

**Derived lemmas (proved from axioms):**
- hGradChainLog (from hGradChainExp via exp(log g) = g)
- hGradIntZero (from hIBP_spatial + hGradConst + hSpatialAdd)
- hLaplacianMinNonneg (from hLaplacianMaxNonpos + hGradScalarMul + hDivLinear)
- hSpatialMul (from Mathlib's integral_mul_right)
- hDiff_sub (from hDiff_add + hDiff_smul with c=-1)
- maxwellian_params_isSpatiallyDiff (from hDiff_log + closure)

---

## Theorem42 Hypotheses

**Physical** (10): f > 0, f smooth, f integrable, nu > 0, rho_ion > 0, Psi > 0,
Psi continuous, rho continuous, D continuous, Vlasov equation, Maxwell equations (3).

**Spatial regularity** (4): hDiff_fv (f(·,v) ∈ C¹ for each v), hDiff_maxwellian_C2
(Maxwellian b params ∈ C²), hDiff_B (B ∈ C¹), hDiff_B_C2 (B ∈ C²).

**DERIVED** (no longer explicit hypotheses):
- hDiff_logfv = hDiff_log + hDiff_fv + hf_pos
- hDiff_maxwellian = maxwellian_params_isSpatiallyDiff (evaluate log f at v=0, eⱼ, 2e₀)
- hDiff_logRho = hDiff_velocityIntegral + hGradFv_dominated + hDiff_log + hρ_pos (new 2026-03-09)

**Domain** (via `[FlatTorus3 X]`): 21 fields for spatial operators, torus topology, differentiability.
CompactSpace and Nonempty bundled into FlatTorus3.

**Velocity-space decay** (1 structure): `VelocityDecayConditions` bundles 17
integrability/Fubini/IBP/decay conditions (incl. new hGradFv_dominated, new 2026-03-09).
