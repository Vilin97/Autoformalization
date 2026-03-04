# Formalization Progress: Global Steady State of the VML System

**File**: `Aristotle/Landau/landau-steady-state.lean`
**Blueprint**: `Aristotle/Landau/H-theorem-formal.tex` (Sections 1--10)
**Status**: 0 errors, 6 sorry's
**Lines**: ~2830

## Summary

The formalization proves Theorem 42 (= Theorem 12 in the blueprint):
any smooth steady state (f, E, B) of the Vlasov--Maxwell--Landau system
on T^3 x R^3 with collision frequency nu > 0 must satisfy:

  (i)   f is a spatially uniform, zero-drift Maxwellian
  (ii)  E = 0
  (iii) B = const
  (iv)  T > 0 uniquely determined by conservation laws

The proof is complete modulo 6 sorry's, all in velocity-space analysis
(integration by parts and Fubini symmetrization for the Landau operator,
Gaussian integral positivity, and three consequences of the Vlasov equation
that require chain rules for abstract spatial gradients).

---

## Proved Lemmas (by blueprint section)

### Section 2: Algebraic Lemmas about the Landau Matrix

All three algebraic lemmas from the blueprint are fully proved:

- **Lemma 1(a)** (A is symmetric): `landauMatrix_symmetric`
- **Lemma 1(b)** (A is even: A(-z) = A(z)): `landauMatrix_even`
- **Lemma 2** (A is positive semidefinite, with equality iff Y parallel to z): `landauMatrix_posSemidef`, `landauMatrix_quadForm_eq_zero_iff`
- **Lemma 3** (Projection annihilation: A(z) z = 0): `landauMatrix_mulVec_self`, `vecMul_landauMatrix_self`

### Section 3: The H-Theorem and Nullspace of the Landau Operator

The entire H-theorem chain is proved, but with two external inputs taken
as hypotheses: the symmetrized weak form (SWF) and PSD integrability.

- **Lemma 4** (Symmetrized weak form):
  int Q(f,f) phi dv = -(1/2) int int (grad phi(v) - grad phi(w))^T A(v-w) flux dv dw.
  Proved in `entropy_score_form` given the SWF identity as a hypothesis.
  The SWF identity itself requires IBP + Fubini (see "Remaining Sorry's").

- **Lemma 5** (Entropy dissipation formula):
  D(f) = -(1/2) int int f(v) f(w) (grad log f(v) - grad log f(w))^T A(v-w) (grad log f(v) - grad log f(w)) dv dw.
  Proved in `entropy_dissipation_formula` via flux factoring (`analysis_fluxFactor`) and scalar factor extraction (`analysis_scalarFactor`).

- **Theorem 3** (H-theorem: D(f) <= 0): `H_theorem`.
  Follows from Lemma 5 + Lemma 2 (PSD) + non-negativity of the PSD integrand (`PSDIntegrand_nonneg`).

- **Lemma 6** (D(f) = 0 implies parallelism): `D_zero_implies_parallel`.
  If D(f) = 0 then grad log f(v) - grad log f(w) is parallel to v - w for all v != w.
  Uses `analysis_nonneg_dbl_zero` (nonneg continuous double integral = 0 implies pointwise = 0).

- **Lemma 7** (Parallel + smooth implies affine): `functional_eq_affine`, `parallel_curl_free_affine`.
  If g(v) - g(w) = lambda(v,w)(v-w) for all v, w and g is smooth, then g(v) = b + 2 c_0 v.
  Proved by Aristotle via curl-free analysis and linear independence argument.

- **Lemma 8** (Affine gradient implies quadratic): `log_f_quadratic`, `affine_gradient_antiderivative`.
  If grad log f(v) = b + 2 c_0 v then log f(v) = a_0 + b . v + c_0 |v|^2.
  Proved by Aristotle via component-wise antidifferentiation.

- **Theorem 4** (Nullspace necessity): `nullspace_necessity`.
  Q(f,f) = 0 with f in L^1 implies f is Maxwellian. Chains Lemmas 6-8.

- **Theorem 5** (Nullspace sufficiency): `nullspace_sufficiency`.
  f Maxwellian implies Q(f,f) = 0 (because A(z) z = 0 by Lemma 3). Also `maxwellian_landau_flux_zero`.

- **Corollary 1** (Complete characterization): `nullspace_iff`.
  Q(f,f) = 0 iff f is Maxwellian.

### Section 4: Vlasov--Maxwell Transport Constraints

- **Lemma 11** (Global entropy production vanishes): `global_entropy_production_zero`.
  D(f)(x) <= 0 for all x and int_X D(f)(x) dx = 0 implies D(f)(x) = 0 for all x.
  Proved using the maximum principle for non-positive functions with zero integral.
  **Note**: The input int_X D(f) dx = 0 is a sorry'd lemma (`transport_entropy_from_vlasov`).

- **Lemma 12** (Pointwise D = 0): `pointwise_entropy_dissipation_zero`.

- **Corollary 2** (Local Maxwellian): `steady_state_is_local_maxwellian`.
  Chains D = 0 with the nullspace characterization.

### Section 5: Polynomial Matching -- From Local to Global Maxwellian

- **Lemma 13** (Polynomial identity in velocity): `polynomial_identity_algebraic`.
  The algebraic reformulation of the collisionless transport equation as a polynomial in v is proved.
  **Note**: Deriving the polynomial identity from the Vlasov equation requires chain rules for
  abstract spatial gradients; this is a sorry'd lemma (`polynomial_identity_from_vlasov`).

- **Lemma 14** (Temperature is constant): `temperature_constant`, `cubic_coeff_zero`.
  O(|v|^3) terms give (v . grad_x c) |v|^2 = 0 for all v, so grad_x c = 0.

- **Lemma 15** (Bulk velocity is constant): `bulk_velocity_constant`, `killing_constant_torus`.
  O(|v|^2) terms give Killing's equation on the flat torus. Killing fields on T^3 are constant.

- **Lemma 16** (Force balance): `force_balance`, `force_balance_from_polynomial`.
  grad_x(log n) = (1/T)(E + u x B).

- **Lemma 17** (Zeroth-order term): `E_dot_u_zero`.
  E(x) . u = 0 for all x.

### Section 6: Nullification of Bulk Velocity via Ampere's Law

- **Lemma 18** (Ampere at steady state): `ampere_steady_state`.
  curl B = J = n(x) u.

- **Lemma 19** (u = 0): `bulk_velocity_zero`.
  Take u . (curl B) = n |u|^2, integrate over T^3, use Stokes: |u|^2 int n = 0.
  Since int n > 0, we get u = 0.

### Section 7: Spatial Uniformity via the Maximum Principle

- **Lemma 20** (Poisson--Boltzmann): `poisson_boltzmann_density`.
  T Delta(log n) = n - rho_ion.
  **Note**: Deriving PB from the Vlasov equation is a sorry'd lemma (`poisson_boltzmann_from_vlasov`).

- **Lemma 21** (Density is constant): `density_constant_max_principle`, `poisson_boltzmann_max_principle`.
  T Delta(log n) = n - rho_ion on compact T^3 implies n = rho_ion by maximum principle.

- **Corollary 3** (E = 0): `electric_field_zero`.
  n constant + force balance + u = 0 gives grad log n = 0 = E/T, so E = 0.

### Section 8: Uniformity of the Magnetic Field

- **Lemma 22** (B is constant): `magnetic_field_constant`.
  curl B = 0 (from J = 0) and div B = 0 implies each B_i is harmonic on T^3, hence constant.

- **Lemma 23** (Compatibility): `B_compatible_maxwellian`.
  (v x B) . grad_v f = 0 for isotropic Maxwellian (since v x B is orthogonal to v).

### Section 9: Conservation Laws and Determination of Parameters

- **Lemma 24** (B mean conserved): `B_mean_conserved`.

- **Lemma 26** (B_infty determined): `B_infty_determination`.

- **Lemma 27** (T_infty determined): `T_infty_determination`.
  T = 2/(3 rho_ion |T^3|) (E_0 - |B_infty|^2 |T^3| / 2).

- **Lemma 28** (T > 0): `T_positive`.

### Main Theorem Assembly

- `main_steady_state`: VMLSteadyState -> exists T > 0 and B_0 such that f = equilibriumMaxwellian, E = 0, B = B_0. **Fully proved.**
- `main_from_physics`: VMLInput -> same conclusion. **Fully proved.**
- `Theorem42`: Clean statement with physical hypotheses. **Proved modulo 6 sorry's.**

### Auxiliary Results (proved by Aristotle)

- `vGrad_exp_quadratic`: grad_v exp(a + b.v + c|v|^2) = exp(...) (b + 2cv)
- `gaussian_normalization_maxwellian`: Gaussian integral normalization gives equilibriumMaxwellian
- `gaussian_first_moment`: int v_i exp(a+b.v+c|v|^2) dv = (-b_i/(2c)) int exp(...) dv
- `PSDIntegrand_nonneg`: the PSD integrand is non-negative (Cauchy--Schwarz + Psi > 0)
- `analysis_nonneg_dbl_zero`: nonneg continuous double integral = 0 implies pointwise = 0
- `analysis_gaussian_integrability`: f = exp(a+b.v+c|v|^2) integrable implies c < 0
- `parallel_curl_free_affine`: parallel + smooth implies affine (the functional equation)
- `affine_gradient_antiderivative`: affine gradient implies quadratic antiderivative
- `maxwellian_landau_flux_zero`: Landau flux vanishes for Maxwellians

---

## Remaining Sorry's

Six sorry's remain. They fall into two categories:

### Category 1: Velocity-space analysis for the SWF identity (2 sorry's in Theorem42)

These are the two steps composing the symmetrized weak form D(f) = -(1/2) int int PSD:

1. **IBP for the Landau operator** (`hIBP` in Theorem42, line ~2704):
   int Q(f,f)(v) log f(v) dv = - int int <grad log f(v), A(v-w) flux(v,w)> dw dv.
   This requires integration by parts in velocity space (moving div_v onto log f)
   and pulling the w-integral inside the dot product. Blueprint: first half of Lemma 4.

2. **Fubini symmetrization** (`hFubiniSym` in Theorem42, line ~2713):
   int int <Delta, A . flux> dv dw = 2 int int <grad log f(v), A . flux> dv dw
   where Delta = grad log f(v) - grad log f(w).
   This requires swapping v <-> w via Fubini, using A(-z) = A(z) and flux antisymmetry.
   Blueprint: second half of Lemma 4.

   **Aristotle status**: 5 submissions active (projects 10e4675e, cb17c256, e9c9cda6, f7669a6d, plus fubini_sym_with_swap). All IN_PROGRESS.

### Category 2: Consequences of the Vlasov equation (4 sorry'd lemmas)

These are mathematical truths derivable from the physical hypotheses (primarily
the Vlasov equation) that require velocity-space or abstract-operator analysis:

3. **Density positivity** (`density_positive_of_integral`, line ~2495):
   f(v) > 0 for all v and f integrable implies int f dv > 0.
   This is a basic measure theory fact (integral of a positive continuous integrable
   function on R^3 is positive). Should be provable from Mathlib.

4. **Transport entropy vanishes** (`transport_entropy_from_vlasov`, line ~2505):
   At steady state, int_X D(f)(x) dx = 0.
   Proof: multiply Vlasov by log f, integrate over v and X. The three transport
   terms vanish: (a) spatial transport by Stokes on T^3, (b) electric force by
   velocity IBP + E independent of v, (c) magnetic force by div_v(v x B) = 0.
   Blueprint: Lemmas 10--11.

5. **Polynomial identity from Vlasov** (`polynomial_identity_from_vlasov`, line ~2528):
   When f = exp(a + b.v + c|v|^2), the Vlasov equation at steady state (with Q=0
   by nullspace sufficiency) gives a polynomial identity in v involving the spatial
   gradients grad_X(a), grad_X(b), grad_X(c) and the fields E, B.
   Requires the chain rule for abstract spatial gradients applied to exponentials.
   Blueprint: Lemma 13.

6. **Poisson--Boltzmann from Vlasov** (`poisson_boltzmann_from_vlasov`, line ~2556):
   When f is locally Maxwellian with constant c_0, combining the force balance
   (from the polynomial identity) with Gauss's law gives T Delta(log rho) = rho - rho_ion.
   Requires connecting grad_X(log rho) to grad_X(a) via Gaussian integral identities.
   Blueprint: Lemma 20.

---

## Theorem42 Hypotheses

After converting mathematical truths to sorry'd lemmas, Theorem42 has the following
hypothesis groups:

**Physical** (14): f > 0, f smooth, f integrable, nu > 0, rho_ion > 0, Psi > 0,
Psi continuous, vol > 0, rho = int f, J = int v f, Vlasov equation, Maxwell equations
(Ampere, Gauss, div B = 0).

**T^3 domain structure** (14): Stokes theorem, harmonic implies constant,
Killing implies harmonic, gradient properties, extremizers for density (x_max, x_min),
Laplacian sign at extrema, curl-dot-constant vanishes, curl-free + div-free implies harmonic,
spatial integral properties (multiplicativity, positivity, nonneg-zero).

**Velocity-space decay** (2): PSD integrand integrability (inner and outer).
These cannot be derived from smoothness + integrability alone (Aristotle proved a
counterexample: f(v) = (1+|v|^2)^{-2} is smooth, positive, integrable, but the PSD
integrand is proportional to 1/|w|^2, not integrable in R^3).

---

## Architecture

The proof flows through three layers:

1. **Theorem42** (user-facing): Takes physical + T^3 + decay hypotheses.
   Derives mathematical consequences via sorry'd lemmas. Constructs VMLInput.

2. **VMLInput -> main_from_physics** (honest interface): Physical hypotheses +
   analytical interface (polynomial identity, PB, current, normalization).
   Derives VMLSteadyState via temperature_constant, bulk_velocity_constant,
   force_balance, density_constant_max_principle, etc.

3. **VMLSteadyState -> main_steady_state** (algebraic core): All analytical work
   is done. Proves u = 0 (Ampere + Stokes), E = 0 (force balance + density constant),
   B = const (curl-free + div-free + harmonic on T^3), T > 0 (Jensen).
