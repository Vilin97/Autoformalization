# Adversarial Critique of the VML Steady-State Formalization

An honest, adversarial analysis of the formalization's completeness. What would a
determined critic attack?

Last updated: 2026-03-10

---

## Current Status

| Component | Sorry's | Status |
|-----------|---------|--------|
| Abstract proof chain (Defs, Section2-9, VMLInputDerive, Theorem42) | **0** | Complete |
| FlatTorus3 instance (TorusInstance) | **0** | Complete |
| VelocityDecayInstance (3 instances) | **0** | Complete |
| ConcreteTheorem42 (shared defs) | **0** | Stub |
| CoulombConcreteTheorem42 | **6** | Incomplete (6 sorry's, all submitted to Aristotle) |

Abstract proof chain: **0 sorry's, 0 axioms, 0 admits** across 14 files.
`lean_verify` on `VML.Theorem42`: only `propext`, `Classical.choice`, `Quot.sound`.

---

## Issue 1: CoulombConcreteTheorem42 Has 6 Sorry's

**Severity: HIGH**

The Coulomb case (Psi(r) = r^{-3}) -- the entire physical motivation -- has **6 sorry's**
(0 helper + 6 main). All are in the proof body (deriving VelocityDecayConditions from
Schwartz + ExpDecay), not in the theorem statement.

| Sorry | File:Line | What's needed | Aristotle Job |
|-------|-----------|---------------|---------------|
| hIBP_f_dg | CoulombConcreteTheorem42:86 | flux_i * fderiv(log f) integrable | landau_ibp_f_dg |
| hPSD_inner_int | CoulombConcreteTheorem42:94 | PSD integrand integrable in w | psd_inner_integrable |
| hPSD_outer_int | CoulombConcreteTheorem42:95 | Iterated PSD integral integrable in v | psd_outer_integrable |
| hFubini_double | CoulombConcreteTheorem42:96 | Joint (v,w) integrability for Fubini | fubini_double_integrable |
| hLandauFluxDiff | CoulombConcreteTheorem42:126 | Flux differentiable (diff under integral) | coulomb_flux_diff |
| hLandauIBP_df_g | CoulombConcreteTheorem42:127 | d(flux_i) * log(f) integrable | landau_ibp_df_g |

**All 6 sorry's are submitted to Aristotle** (all IN_PROGRESS as of 2026-03-10).

### Mathematical assessment

**All 6 sorry'd statements are mathematically true.** They are analytical estimates that
follow from the Schwartz + stretched-exponential decay hypotheses combined with the key
Coulomb cancellation: the Landau matrix A(z) = |z|^{-3}(|z|^2 I - zz^T) has entries
bounded by |z|^{-1} (proved: `coulomb_landauMatrix_entry_le`), and the score difference
Delta = nabla log f(v) - nabla log f(w) provides an O(|v-w|) factor, making the PSD
integrand continuous despite the singularity (proved: `psd_continuous_coulomb`).

The **hardest cluster** (hPSD_inner_int, hPSD_outer_int, hFubini_double) requires showing
that f(v) * f(w) * |v-w|^{-1} * |Delta|^2 is integrable. Since |Delta| grows at most
polynomially (from the log bound lemma) and f is Schwartz, the integrand is bounded by
|v-w|^{-1} * polynomial * Schwartz^2. The key ingredient `inv_norm_schwartz_integrable`
(proved) gives integrability of |z|^{-1} * Schwartz, but composing this into the full
double-integral estimate requires careful multi-step bounds.

The **flux derivative cluster** (hLandauFluxDiff, hLandauIBP_df_g) requires differentiation
under the integral sign with the singular Coulomb kernel. The smooth kernel proof uses
`landau_flux_component_diff_with_bound` (needs `Continuous Psi`, `ContDiff 1 Psi`, bounded
Psi') -- none of which hold for Coulomb. A custom argument using local integrability of
`‖z‖⁻²` in 3D is needed. Note: the smooth kernel bound `‖fderiv(flux)‖ ≤ C*poly*f(v)`
does NOT carry over to Coulomb (|∂f|/f can grow exponentially); the correct bound is
Schwartz-class decay `‖fderiv(flux)‖ * (1+‖v‖)^N ≤ C` for any N.

**Critic's attack:** "The abstract Theorem42 is correct, but the Coulomb case --
the entire physical motivation -- has 6 unproved lemmas (down from 14). This is not a complete
formalization of the physically relevant result."

---

## Issue 2: VelocityDecayConditions is a Large Hypothesis Bundle

**Severity: HIGH (epistemic)**

The `VelocityDecayConditions` structure has **19 fields**:

1. hPSD_inner_int
2. hPSD_outer_int
3. hFubini_double
4. hFubini_inner
5. hFubini_outer
6. hSpatialTransport_int
7. hForceTransport_int
8. hLandauFluxDiff
9. hLandauIBP_df_g
10. hLandauIBP_f_dg
11. hLandauIBP_fg
12. hLandauFluxInt
13. hForceIBP_f_dg
14. hForceIBP_fg
15. hSpatialTransport_joint
16. hSpatTransComp
17. hf_velocity_dominated
18. hPSD_cont
19. hD_cont

Combined with 13 explicit hypotheses in Theorem42 and the 23 FlatTorus3 fields, the
theorem has roughly **55 total conditions**. The documentation claims "12 hypotheses"
for CoulombConcreteTheorem42, which counts only the explicit theorem parameters.

**Mitigating factor:** Three non-circular instances prove satisfiability (0 sorry's).
But none of those instances covers the Coulomb kernel (they require C^1 Psi with bounded
derivative, while Coulomb has Psi(r) = r^{-3}).

---

## Issue 3: No Non-Circular Instance Covers Coulomb

**Severity: MODERATE**

The three VelocityDecayConditions instances are:

1. **uniformMaxwellianDecay** (f = Maxwellian, E=B=0): **Circular** -- the Maxwellian is
   the theorem's conclusion.

2. **schwartzDecayConditions** (Schwartz f, E=B=0): Requires `ContDiff R 1 Psi` and
   bounded Psi'. Coulomb kernel is **excluded**.

3. **schwartzDecayConditionsEB** (Schwartz f, constant E, B): Same Psi requirements.
   Coulomb **excluded**.

This means there is **no formally verified instance demonstrating that the theorem's
hypotheses are satisfiable for the Coulomb kernel by a non-equilibrium distribution**.
The CoulombConcreteTheorem42 attempts to construct one but has 6 sorry's.

---

## Issue 4: FlatTorus3 Typeclass as Hidden Axioms

**Severity: LOW (well-addressed)**

The FlatTorus3 typeclass bundles 23 property fields including deep theorems:

- **hHarmonic_const**: Harmonic functions on compact manifolds are constant (Hodge theory)
- **hKillingToHarmonic**: Killing fields have harmonic components (flatness of metric)
- **hLaplacianMaxNonpos**: Second derivative test for the Laplacian
- **hIBP_spatial**: Integration by parts on the torus (Stokes' theorem)
- **hCurlZeroDivZeroHarmonic**: Irrotational solenoidal => harmonic (flatness + Hodge)

All 23 fields are proved for the concrete torus `Fin 3 -> AddCircle 1` with 0 sorry's
in TorusInstance.lean. The proofs use Mathlib's `fderiv`, periodicity, energy methods,
and Clairaut's theorem. They are correct but many are Aristotle-generated and hard to
audit manually.

**Design note:** `IsSpatiallyDiff` on the concrete torus is `ContDiff R top (periodicLift f)`
(C-infinity smooth periodic lift). This is stronger than "differentiable" but is necessary
for gradient closure (`hDiff_grad`). The name is somewhat misleading.

---

## Issue 5: Circularity

**Severity: LOW (no circularity in the abstract theorem)**

The proof chain `Theorem42 -> VMLInput -> VMLSteadyState -> main_steady_state` never
assumes the conclusion. The `uniformMaxwellianDecay` instance is circular but serves only
as a consistency check. The two Schwartz instances are genuinely non-circular.

**Subtle concern:** VelocityDecayConditions includes `hD_cont` and `hPSD_cont`, which are
properties of specific solutions rather than generic conditions. In principle, one could
worry that these silently exclude some solutions. But any smooth Schwartz-class solution
satisfies them, so the exclusion (if any) is of physically irrelevant pathologies.

---

## Issue 6: Physical Limitations

**Severity: MODERATE (inherent scope)**

- **Periodic domains only:** Excludes bounded domains, whole-space R^3, tokamak geometries.
  Standard in the literature (Desvillettes-Villani also use periodic domains).

- **Dimension 3 only:** Hard-coded to `Fin 3`. Cross product is dimension-specific.

- **Single species only:** Models one charged species against uniform ion background.
  Multi-species (electron-ion) systems not covered.

- **Steady state only:** No convergence-to-equilibrium results. The theorem says "IF a
  smooth steady state exists, THEN it is Maxwellian." Existence is not addressed.

- **f > 0 everywhere:** Physically, distribution functions can vanish (vacuum regions).
  Standard in H-theorem literature but worth noting.

- **IsSpatiallyDiff = C-infinity:** PDE regularity theory typically provides Sobolev
  regularity, not C-infinity. The theorem requires a strong regularity assumption that
  PDE solutions may not satisfy in general. The theorem is about characterization, not
  existence, so this is standard.

---

## Issue 7: Documentation Staleness

**Severity: MINOR**

- `MEMORY.md` says "6 sorry's" for CoulombConcreteTheorem42. Actual count: **6**. (Current)
- `progress.md` may have stale sorry counts.
- `progress.md` says "15 conditions" for VelocityDecayConditions. Actual count: **19**.
- The VelocityDecayConditions docstring says "18 fields." Actual count: **19** (hD_cont
  was added later).
- CoulombConcreteTheorem42 docstring says "Hypotheses (12 total)." This counts only
  explicit parameters, not the ~19 VelocityDecayConditions derived internally.

---

## Issue 8: Code Quality

**Severity: COSMETIC**

- **`set_option linter.all false`** in every file (all 21). This suppresses all quality
  warnings including unused variables, unused simp arguments, and style issues.

- **High heartbeat settings:** Several files use `maxHeartbeats 800000` to `3200000`
  (default 200000). The worst offenders:
  - `VelocityDecayInstance.lean:1002`: `maxHeartbeats 4000000`
  - `NewtonianPotential.lean:241`: `maxHeartbeats 3200000`
  - `CoulombFlux.lean:131`: `maxHeartbeats 3200000`
  These indicate fragile proofs that may break under Lean/Mathlib updates.

- **Large files:** VelocityDecayInstance.lean (2019 lines), Section3.lean (1308 lines),
  TorusInstance.lean (1223 lines). The VelocityDecayInstance could benefit from splitting.

- **Aristotle-generated proofs:** Machine-generated proofs (e.g., `gaussian_normalization_maxwellian`,
  `gaussian_first_moment`, `psd_continuous_coulomb`) are correct but dense and
  unmaintainable. Example: `gaussian_normalization_maxwellian` is a single tactic block
  with nested `simp_all +decide` and `erw` chains spanning 13 lines.

- **Trivial wrapper lemmas:** `lhs_entropy_vanishes` (Section4, line 21) literally returns
  its hypothesis `htransport`. `energy_conserved` (Section9) and `B_mean_conserved` are
  trivial wrappers. These match the blueprint's lemma numbering but add no content.

- **Faraday's law omitted:** The fourth Maxwell equation (curl E = -dB/dt, trivial at
  steady state: curl E = 0) is not used. This is a legitimate optimization (fewer
  hypotheses) but a physicist might notice the gap.

---

## Issue 9: The VMLInput "Analytical Interface"

**Severity: LOW (all derived, not assumed)**

The `VMLInput` structure contains fields like `hPolynomialIdentity`, `hJ_from_maxwellian`,
`hPB_eq`, and `hNormalization`. These look like hypotheses but are actually derived in
Theorem42's proof:

- `hPolynomialIdentity` <- `polynomial_identity_from_vlasov` (proved, Section5)
- `hJ_from_maxwellian` <- `gaussian_first_moment` (proved by Aristotle)
- `hPB_eq` <- `poisson_boltzmann_from_vlasov` (proved, Section7)
- `hNormalization` <- `gaussian_normalization_maxwellian` (proved by Aristotle)

No circularity or hidden assumptions. The VMLInput intermediate layer is well-designed.

---

## Summary

### What is formally proved (0 sorry's):

The abstract Theorem42: on any `[FlatTorus3 X]` (23 axioms, all proved on
`Fin 3 -> AddCircle 1`), for any smooth steady state (f, E, B) satisfying 13 explicit
hypotheses + 19 VelocityDecayConditions, f must be a spatially uniform zero-drift
Maxwellian, E = 0, B = const.

VelocityDecayConditions satisfiability: proved (0 sorry's) for 3 instances including
non-circular ones (but not for Coulomb).

### What is NOT formally proved:

CoulombConcreteTheorem42 has **6 sorry's** (0 helper + 6 main) -- all in
VelocityDecayConditions construction from Schwartz + ExpDecay hypotheses. These are:
- 3 PSD/Fubini integrability (hard, Coulomb-specific double-integral estimates)
- 1 hIBP_f_dg (hard, flux * score integrable)
- 2 Landau IBP/differentiability (moderate, diff under integral sign + derivative integrability)

All 6 are mathematically true, provable with sufficient effort, and submitted to Aristotle.

### Bottom line:

The abstract formalization is **solid and complete**. Lean's kernel confirms it.
The Coulomb specialization is **incomplete** with 6 sorry's. A claim of "full completion"
is defensible for the abstract theorem but not for the Coulomb case, which is the result
physicists actually care about.
