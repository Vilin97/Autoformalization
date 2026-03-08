# Formalization Progress: Global Steady State of the VML System

**Files**: `Aristotle/Landau/main/*.lean` (split across 12 files)
**Blueprint**: `Aristotle/Landau/H-theorem-formal.tex` (Sections 1--10)
**Status**: 0 errors, 0 sorry's in main chain + TorusInstance; 1 sorry in VelocityDecayInstance (Schwartz construction)

Last updated: 2026-03-07

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
validates the typeclass with **0 sorry's** (all 21 instance fields proved).

A concrete VelocityDecayConditions instance (VelocityDecayInstance.lean) for the
spatially uniform Maxwellian `f(x,v) = exp(a + c|v|²)` with E = 0, B = 0 validates
all 15 velocity-decay conditions with **0 sorry's**.

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
- `VelocityDecayInstance.lean` -- Concrete VelocityDecayConditions for uniform Maxwellian

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

## TorusInstance (0 sorry's)

### All instance fields proved:

`hDiff_velocityIntegral` was removed from `FlatTorus3` (2026-03-10): it was mathematically false
as stated (first-order bounds don't give C^∞). The need for `IsSpatiallyDiff ρ` was eliminated by
deriving `IsSpatiallyDiff (log ∘ ρ)` directly from the Maxwellian form: since f(x,v) = exp(a(x) + c₀|v|²),
we have log ρ(x) = a(x) + const, so `IsSpatiallyDiff (log ∘ ρ)` follows from `IsSpatiallyDiff a`.

Instance fields (21/21 proved): `hDivLinear`, `hGradScalarMul`, `hGradChainExp`, `hGradAdd`, `hGradConst`,
`hSpatialPos`, `hSpatialNonnegZero`, `hSpatialVelocityFubini`, `hSpatialAdd` (via integral_add),
`hGradIntegrable` (via IsOpenQuotientMap.piMap), `IsSpatiallyDiff` (= ContDiff ℝ ⊤ ∘ periodicLift),
`hDiff_const`, `hDiff_add`, `hDiff_smul`, `hDiff_log` (= ContDiff.log),
`hDiff_grad` (= ContDiff.fderiv_right + clm_apply),
`hCurlIntZero`, `hHarmonic_const`, `hIBP_spatial`, `hLaplacianMaxNonpos`,
`hKillingToHarmonic`, `hCurlZeroDivZeroHarmonic`

Helper theorems (all proved): `torus_hIBP_spatial` (1D FTC + Fubini + periodicity),
`torus_hCurlIntZero` (from IBP), `torus_hHarmonic_const` (energy method via IBP),
`torus_hGradAdd'`, `torus_hLaplacianMaxNonpos`, `torus_hKillingToHarmonic`,
`torus_hCurlZeroDivZeroHarmonic`, `clairaut_fderiv`, `periodicLift_torusGradX`,
`laplacian_nonpos_at_max_rn`, `killing_harmonic_rn'`, `curl_div_harmonic_rn'`,
`contDiff2_from_partials`

---

## VelocityDecayInstance

### uniformMaxwellianDecay (0 sorry's)

Constructs a concrete `VelocityDecayConditions` for the spatially
uniform isotropic Maxwellian `f(x,v) = exp(a + c|v|²)` with `c < 0`, `E = 0`, `B = 0`.
All 15 fields proved by showing each integrand is identically 0, then applying `integrable_zero`.
**Note:** This instance is circular (the Maxwellian is the theorem's conclusion).

### schwartzDecayConditions (1 sorry, 14 proved)

**Non-circular** construction: proves VelocityDecayConditions for Schwartz-class distributions
`φ(v) > 0` with `‖v‖^k * |φ(v)|` integrable for all k, C¹ bounded Ψ, gradient/log bounds.
For `E = B = 0`, this shows the hypothesis set is satisfiable by genuine non-Maxwellians
(e.g., `φ(v) = exp(-|v|⁴)`).

**Hypotheses** (added to unblock flux differentiability):
- `hΨ_diff : ContDiff ℝ 1 Ψ` — Ψ is C¹
- `hΨ'_bound : ∃ CΨ', ∀ r, |deriv Ψ r| ≤ CΨ'` — Ψ' bounded
- `hφ_deriv2_bound` — pointwise second derivative bound: `‖∂²φ/∂vⱼ∂vₖ‖ ≤ C₂(1+‖v‖)^K₂ φ(v)`

**Status:** 14/15 conditions proved:
- 5 transport/force conditions (trivially 0 since E=B=0, gradX=0)
- `hLandauFluxInt` — flux integrability (pointwise bound + Schwartz domination)
- `hLandauIBP_fg` — flux × log integrability (flux integral bound + log bound)
- `hLandauIBP_f_dg` — flux × d(log) integrability (flux bound + gradient/value bound)
- `hPSD_inner_int` — PSD inner integrability (psd_integrand_bound + integrable_of_schwartz_bound)
- `hPSD_outer_int` — PSD outer integrability (integrable_integral_schwartz + psd_integrand_bound)
- `hFubini_double` — Fubini double integrability (integrable_prod_schwartz_bound)
- `hFubini_inner` — Fubini inner integrability (flux projection + dotProduct decomposition)
- `hFubini_outer` — Fubini outer integrability (integrable_integral_schwartz)
- `hLandauFluxDiff` — flux differentiability (**proved** modulo `landau_flux_component_diff_with_bound`)
- `hLandauIBP_df_g` — derivative-of-flux × log (**proved** modulo `landau_flux_component_diff_with_bound`)

1 condition remains (reduced from `landau_flux_component_diff_with_bound`):
- This single helper lemma bundles: (1) flux integrand differentiability in v,
  (2) product-form derivative bound, (3) derivative integrability,
  (4) flux integral derivative Schwartz bound.
- **Part (1) is PROVED**: uses `landauMatrix_entry_differentiable` (proved by Aristotle, job 648b5b5b)
  + `Fin.sum_univ_three` + `DifferentiableAt.add`/`.mul` for the finite sum decomposition.
- Parts (2)-(4) combined into 1 sorry (was 3 separate sorry's).
  Key finding: the linear derivative bound ‖D A_{ij}(z)‖ ≤ C(1+‖z‖) is **FALSE**
  (Aristotle proved negation, job 207db299). Correct bound is quadratic: C(1+‖z‖)².
  Submitted corrected quadratic bound (job 0f6845b7) and full flux bound (job 68c58a76).

Key infrastructure lemmas (proved):
- `psd_integrand_bound` — |PSD(v,w)| ≤ 108CΨCg²(1+‖v‖)^(2K+2)|φv|(1+‖w‖)^(2K+2)|φw|
- `psd_integrand_continuous_joint` — joint continuity of PSD integrand in (v,w)
- `fubini_integrand_bound` — |⟨∇logφ(v), flux(v,w)⟩| ≤ C P(v) Q(w) (product Schwartz bound)
- `fubini_integrand_continuous` — joint continuity of Fubini integrand
- `differentiable_integral_of_schwartz_dominated` — differentiation under integral sign (v-uniform bound)
- `differentiable_integral_of_product_dominated` — differentiation under integral sign (product-form bound)
- `landau_flux_component_diff_with_bound` — **1 sorry** — flux integrand differentiability + bounds
- `landau_flux_pointwise_bound` — ‖A(v-w)(φ(w)∇φ(v)-φ(v)∇φ(w))‖ ≤ C(1+‖v‖)^M φ(v)(1+‖w‖)^M φ(w)
- `landau_flux_continuous_w` — continuity of flux integrand in w
- `landau_flux_continuous_joint` — joint continuity of flux integrand in (v,w)
- `landau_flux_integral_aestronglyMeasurable` — measurability of flux integral (via Fubini)
- Helper lemmas: `integrable_one_add_norm_pow_mul`, `integrable_of_schwartz_bound[_vec]`,
  `integrable_prod_schwartz_bound`, `integrable_integral_schwartz`, `norm_mulVec_le_of_entry_bound`,
  `landauMatrix_entry_le`, `vGrad_log_eq_div`, `vGrad_log_norm_le`, `normSq_le_three_mul_sq_norm`

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

**IsSpatiallyDiff closure (5):** hDiff_const, hDiff_add, hDiff_smul, hDiff_log, hDiff_grad

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

**Spatial regularity** (2): hDiff_fv (f(·,v) ∈ C^∞ for each v), hDiff_B (B ∈ C^∞).

**DERIVED regularity** (no longer explicit hypotheses, 2026-03-09):
- hDiff_B_C2 = hDiff_grad (FlatTorus3 closure) applied to B components
- hDiff_maxwellian_C2 = hDiff_grad applied to b_loc components

**DERIVED** (no longer explicit hypotheses):
- hDiff_logfv = hDiff_log + hDiff_fv + hf_pos
- hDiff_maxwellian = maxwellian_params_isSpatiallyDiff (evaluate log f at v=0, eⱼ, 2e₀)
- hDiff_logRho = derived from Maxwellian form: log ρ = a + const (2026-03-10, replaces hDiff_velocityIntegral)

**Domain** (via `[FlatTorus3 X]`): 21 fields for spatial operators, torus topology, differentiability.
CompactSpace and Nonempty bundled into FlatTorus3.

**Velocity-space decay** (1 structure): `VelocityDecayConditions` bundles 15
integrability/Fubini/IBP/decay conditions (hGradFv_dominated removed 2026-03-10).
