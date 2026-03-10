# Adversarial Critique: VML Steady-State Formalization (Coulomb Kernel on T^3)

**Reviewer posture:** Hostile. Looking for reasons to REJECT.

**Scope:** 24 `.lean` files, ~11,079 lines (by byte-based line estimates from file sizes), claimed 0 sorry's.

**Date:** 2026-03-10 (post-cleanup: 5 tautological theorems removed, hGradBound comment added).

---

## 1. Sorry's

**Verdict: PASS.**

A grep for `sorry` across all 24 files returns zero hits outside of comments (the word "sorry" appears only in documentation strings like "0 sorry's" in TorusInstance.lean and VelocityDecayInstance.lean). No `sorry` token is present in any proof term.

**Residual risk:** A stale `.olean` cache could in principle mask a `sorry` that Lean would catch on a fresh `lake build`. An ideal review would run `lake clean && lake update && lake exe cache get && lake build` from scratch.

---

## 2. Hidden Axioms

**Verdict: PASS.**

| Escape hatch | Status |
|---|---|
| `sorry` | 0 |
| `axiom` | 0 (all occurrences are in comments/docstrings describing FlatTorus3 axiom design) |
| `admit` | 0 |
| `native_decide` | 0 |
| `unsafe` | 0 |
| `Decidable.decide` | Used only via `simp +decide` for `Fin 3` case splits -- sound kernel reduction |

No user-declared axioms. The only axioms in the TCB are Lean 4's kernel axioms (`propext`, `Quot.sound`, `Classical.choice`) and Mathlib's, which is standard.

`set_option` usage:
- `linter.unusedSimpArgs false` in 3 files (Defs, Section3Helpers, Section7) -- suppresses a lint warning, does not affect soundness.
- `maxHeartbeats` raised in 32 locations across 13 files -- performance only, does not affect soundness.
- No `set_option pp.all false`, `set_option debug.*`, or other dangerous options.

---

## 3. Circularity (Import DAG)

**Verdict: PASS.**

The import DAG is a strict forest (DAG with no cycles):

```
Defs
  +-- Section2
  +-- Section3Helpers --> Section3
  +-- Section4 (imports Defs, Section3)
  +-- Section5 (imports Defs, Section3)
  +-- Section6
  +-- Section7 (imports Defs, Section3, Section6)
  +-- Section8 (imports Defs, Section6)
  +-- Section9 (imports Defs, Section3)
  +-- TorusInstance (imports Defs only)
  +-- LandauMatrixDerivBound (imports Defs only)
  +-- VMLInputDerive (imports Defs, Section3-9)
      +-- Theorem42
          +-- ConcreteTheorem42 (imports Theorem42, TorusInstance, VelocityDecayInstance)
              +-- CoulombKernel --> CoulombSpatialTransport
              +-- CoulombKernel --> NewtonianPotential --> CoulombFlux --> CoulombPSD
              +--                                         CoulombFlux --> CoulombFluxDiff
              +-- CoulombConcreteTheorem42 (imports CoulombSpatialTransport, CoulombFlux, CoulombPSD, CoulombFluxDiff)
          +-- VelocityDecayHelpers (imports Theorem42, LandauMatrixDerivBound)
              +-- VelocityDecayInstance
```

No cycles. Each file imports only upstream dependencies.

---

## 4. Hypothesis Audit

**Verdict: CONCERNS -- see below.**

### 4a. The FlatTorus3 typeclass (23 property fields)

This is an unusually large typeclass -- 23 fields encoding all properties of a flat compact 3-torus. While every field is proved for the concrete instance `Torus3 = Fin 3 -> AddCircle 1`, the design raises concerns:

**Concern 4a-1: Over-axiomatization.** Several fields are redundant or could be derived from others. For example:
- `hSpatialAdd` is just `integral_add` -- already a Mathlib lemma. Why is this an axiom of the typeclass rather than derived at use sites?
- `hGradIntegrable` (gradient components of differentiable functions are integrable) follows on any compact space from continuity + compactness. It should not need to be a typeclass field.
- `hDivLinear` is a trivial consequence of `fderiv` linearity.

These "axioms" are proved for the concrete instance, so they are not false, but stuffing them into the typeclass inflates the interface and obscures which properties are genuinely deep.

**Concern 4a-2: hSpatialVelocityFubini drops a hypothesis.** The field signature is:
```
hSpatialVelocityFubini : forall (F : X -> (Fin 3 -> R) -> R),
  (forall x, Integrable (F x)) ->
  Integrable (Function.uncurry F) (volume.prod volume) ->
  (integral x, integral v, F x v) = integral v, integral x, F x v
```
The concrete instance proves this by `integral_integral_swap hF_joint`, discarding the first hypothesis `(forall x, Integrable (F x))`. The abstract formulation demands joint integrability anyway, so the per-section integrability hypothesis is dead weight. This is not a soundness issue but a design smell.

### 4b. VelocityDecayConditions (18 fields)

This is a massive bundle of integrability and differentiability hypotheses passed to Theorem42. The 18 fields are:

- `hPSD_inner_int`, `hPSD_outer_int` (PSD integrand)
- `hFubini_double`, `hFubini_inner`, `hFubini_outer` (Fubini)
- `hSpatialTransport_int`, `hForceTransport_int` (transport)
- `hLandauFluxDiff` (flux differentiability)
- `hLandauIBP_df_g`, `hLandauIBP_f_dg`, `hLandauIBP_fg` (IBP integrability)
- `hLandauFluxInt` (flux integrability)
- `hForceIBP_f_dg`, `hForceIBP_fg` (force IBP)
- `hSpatialTransport_joint`, `hSpatTransComp` (joint integrability)
- `hf_velocity_dominated` (dominated convergence)
- `hPSD_cont`, `hD_cont` (continuity)

These are all verified for both the smooth kernel case (VelocityDecayInstance) and the Coulomb kernel case (CoulombConcreteTheorem42), so the bundle is honest. However:

**Concern 4b-1:** The abstract theorem (Theorem42) takes 18 hypotheses about velocity decay bundled into a structure, plus 13 more top-level hypotheses. This makes the abstract statement essentially unreadable. A reader cannot easily tell what the minimal assumptions are.

**Concern 4b-2:** The `hPSD_cont` field (PSD integrand is continuous) is a non-trivial mathematical requirement that goes far beyond "decay condition." For the Coulomb kernel, it requires a delicate cancellation argument (score difference O(|v-w|) cancels the |v-w|^{-3} singularity). Bundling this into "VelocityDecayConditions" is misleading nomenclature.

### 4c. CoulombConcreteTheorem42 hypotheses

The concrete theorem takes 13 hypotheses. They are:

1. `hnu : 0 < nu` -- standard
2. `hrho_ion : 0 < rho_ion` -- standard
3. `hf_pos : forall x v, 0 < f x v` -- **strong**
4. `hf_smooth_v : forall x, ContDiff R top (f x)` -- **strong**
5. `hf_smooth_x : forall v, ContDiff R top (periodicLift (fun x => f x v))` -- **strong**
6. `hB_smooth : forall i, ContDiff R top (periodicLift (fun x => B x i))` -- standard for steady state
7. `hSchwartz : UniformSchwartzDecay f` -- **very strong**
8. `hExpDecay : exists C K, forall x v, exp(-C*(1+||v||)^K) <= f x v` -- **strong**
9. `hGradBound : exists Cg Kg, forall x v i, |df/dv_i| <= Cg*(1+||v||)^Kg * f x v` -- **redundant** (see below)
10-13: The PDE system (Vlasov, Ampere, Gauss, divB=0)

**Concern 4c-1: Redundancy of hGradBound (hypothesis 9).**

The comment in CoulombConcreteTheorem42.lean (lines 71-73) now reads:

```
-- NOTE: Likely derivable from hSchwartz + hExpDecay (Schwartz numerator /
-- stretched-exponential denominator -> polynomial growth), but proving this
-- in Lean is nontrivial. Stated separately; the hypothesis list is not minimal.
```

This is an honest acknowledgment that the hypothesis list is not minimal. The derivation is indeed straightforward in informal mathematics: if `f` is Schwartz with `|df/dv_i| * (1+||v||)^N <= C_N` for all N, and `f(v) >= exp(-C*(1+||v||)^K)`, then `|df/dv_i| / f(v) <= C_N * (1+||v||)^{-N} / exp(-C*(1+||v||)^K)`. Choosing N large enough absorbs the exponential. The result is polynomial growth of the score, which is exactly hypothesis 9.

**Updated verdict:** The comment is appropriate and honest. The hypothesis list contains 13 stated hypotheses but only 12 are genuinely independent. This is a known formalization debt, not a hidden issue. A hostile reviewer would still note that the theorem as stated is weaker than the mathematical result it claims to formalize.

**Concern 4c-2: The stretched-exponential lower bound (hypothesis 8).** This is a physically reasonable but mathematically non-trivial assumption. For steady-state solutions of VML, such a lower bound is not obviously a consequence of the other hypotheses. The paper should justify this assumption more carefully.

---

## 5. Mathematical Correctness

**Verdict: MINOR CONCERNS (improved from previous review).**

### 5a. Tautological theorems -- RESOLVED

The previous critique identified 5 tautological/dead theorems:
- `lhs_entropy_vanishes` (identity function)
- `symmetrized_weak_form` (identity function)
- `polynomial_identity_velocity` (conclusion was `True`)
- `energy_conserved` (trivial forwarding)
- `B_mean_conserved` (trivial forwarding)

**All 5 have been removed.** This was the most significant presentation concern and it has been addressed.

### 5b. Remaining near-tautological lemmas

A few lemmas in Section3Helpers.lean are still borderline tautological:

- **`transport_entropy_vanishes_torus` (line 707):** Takes `htransport` as a hypothesis and returns it. The proof is literally `htransport`. However, this lemma is no longer called from the main proof chain (it was used by the removed `lhs_entropy_vanishes`), so it is now **dead code**.

- **`nonpositive_integral_zero_compact` (line 728):** Takes `hfaithful` as a hypothesis and applies it. The proof is `hfaithful g hnonpos hintegral`. This is still called from Section4.lean (lines 27 and 45). It is a thin wrapper, not a genuine mathematical contribution.

- **`divergence_scalar_linear` (line 825):** Takes `hLinear` as a hypothesis and applies it. The proof is `fun x => hLinear c F x`. Called from Section7.lean. Another thin wrapper.

- **`vml_energy_conservation` (line 898):** Proof is `aesop` on trivial hypotheses. No longer called from the main chain -- **dead code**.

- **`B_mean_conserved_from_axioms` (line 864):** Proof is `aesop`. No longer called from the main chain -- **dead code**.

- **`faraday_stokes_integral_zero_v2` (line 882):** Proof is `aesop`. No longer called from the main chain -- **dead code**.

**Verdict:** The 5 explicitly tautological theorems were removed, which is good. However, 4 dead-code lemmas remain in Section3Helpers.lean (`transport_entropy_vanishes_torus`, `vml_energy_conservation`, `B_mean_conserved_from_axioms`, `faraday_stokes_integral_zero_v2`). These should be cleaned up.

### 5c. The core proof chain IS nontrivial

The genuinely nontrivial parts of the formalization are:
1. **H-theorem** (Section3.lean): D(f) <= 0 via PSD quadratic form. Real proof content.
2. **D=0 => Maxwellian** (Section3Helpers.lean): Parallelism argument, affine gradient recovery, functional equation solution. All proved by Aristotle with substantial proofs (the `parallel_curl_free_affine` proof alone is ~100 lines).
3. **Polynomial identity extraction** (Section5.lean): Expanding the collisionless transport equation, 220 lines. Real proof content.
4. **Maximum principle** (Section7.lean): Poisson-Boltzmann from Vlasov + Laplacian at extrema. 270 lines. Real proof content.
5. **Coulomb PSD continuity** (CoulombPSD.lean): Cancellation of the |z|^{-3} singularity via score difference regularity. Real proof content.
6. **Coulomb flux differentiability** (CoulombFluxDiff.lean): Differentiation under the integral sign via `hasFDerivAt_integral_of_dominated_of_fderiv_le`. Real proof content.
7. **Torus instance** (TorusInstance.lean): All 23 fields proved for the concrete torus. Real proof content.
8. **VelocityDecayConditions for Coulomb** (CoulombConcreteTheorem42.lean): All 18 fields proved. Real proof content.
9. **Newtonian potential** (NewtonianPotential.lean): `newtonian_schwartz_uniform_bound` (exists M>0, forall v, integral ||v-w||^{-1}|g(w)| <= M) is a genuine analysis result.

### 5d. The IsMaxwellian extraction uses Classical.choice

In `VMLInputDerive.lean:65`:
```
private def VMLInput.isMaxwellian_at (p : VMLInput X) (x : X) : IsMaxwellian (p.f x) := ...
noncomputable def VMLInput.a_loc (p : VMLInput X) : X -> R := fun x => (p.isMaxwellian_at x).choose
```

The Maxwellian parameters (a, b, c) are extracted via `Classical.choice` from the existential proof that f is Maxwellian. This is mathematically sound (the parameters are uniquely determined by f), but the use of `choice` means the extracted functions `a_loc`, `b_loc`, `c_loc` are definitionally opaque. The formalization then needs to thread differentiability of these functions through the FlatTorus3 machinery, which it does via `maxwellian_params_isSpatiallyDiff`. This is correct but inelegant.

### 5e. The hardcoded dimension 3

The entire formalization is hardcoded to `Fin 3 -> R` for velocity space. This is physically correct (3D plasma) but mathematically restrictive. The abstract theory (H-theorem, nullspace characterization) works in any dimension d >= 2. The cross product `cross` and the specific matrix algebra are 3-dimensional, but much of the structure could be generalized.

---

## 6. Code Quality

### 6a. File sizes

| File | Size (bytes) | Assessment |
|---|---|---|
| TorusInstance.lean | 69,823 | Large (~1,200 lines). Could split spatial IBP proofs out. |
| VelocityDecayHelpers.lean | 59,071 | Large (~1,000 lines). Borderline. |
| VelocityDecayInstance.lean | 64,833 | Large (~1,000 lines). Borderline. |
| Section3Helpers.lean | 58,328 | Large (~930 lines). OK for a helpers file. |
| CoulombPSD.lean | 46,331 | ~716 lines. OK. |
| Defs.lean | 39,723 | ~776 lines. Heavy for a definitions file (contains FlatTorus3 + derived lemmas). |
| CoulombSpatialTransport.lean | 38,339 | ~660 lines. OK. |
| CoulombFluxDiff.lean | 37,923 | ~630 lines. OK. |
| CoulombFlux.lean | 34,703 | ~610 lines. OK. |
| LandauMatrixDerivBound.lean | 26,296 | ~428 lines (recently cleaned up from 644). Good. |

No file exceeds ~1,200 lines, which is acceptable.

### 6b. Heartbeat overrides

**32 `set_option maxHeartbeats` directives across 13 files.** This is a high count. The worst offenders:

| File | Max heartbeats | Count |
|---|---|---|
| VelocityDecayInstance.lean | 4,000,000 | 1 |
| NewtonianPotential.lean | 3,200,000 | 1 |
| CoulombPSD.lean | 3,200,000 | 3 |
| CoulombFlux.lean | 3,200,000 | 2 |
| CoulombSpatialTransport.lean | 1,600,000 | 2 |
| CoulombFluxDiff.lean | 1,600,000 | 1 |
| LandauMatrixDerivBound.lean | 1,600,000 | 1 |

The default is 200,000. A 4,000,000 heartbeat proof is 20x the default -- a sign of typeclass search hell or deeply nested unfolding. The `synthInstance.maxHeartbeats 160000` in CoulombSpatialTransport.lean confirms typeclass diamond issues with `HSMul` resolution.

**Verdict:** Not a soundness issue, but indicates that the code would be fragile under Mathlib updates. High heartbeat proofs are a maintenance time bomb.

### 6c. Duplicate definitions

**MAJOR CONCERN.** The following definitions are duplicated across files:

| Definition | Defs.lean (VML namespace) | LandauMatrixDerivBound.lean | CoulombFlux.lean |
|---|---|---|---|
| `normSq` / `normSq'` | Yes | Yes | Yes |
| `eucNorm` / `eucNorm'` | Yes | Yes | Yes |
| `innerLandauMatrix` / `innerLandauMatrix'` | Yes | Yes | Yes |
| `landauMatrix` / `landauMatrix'` | Yes (parametric) | Yes (parametric) | Yes (Coulomb-specialized) |

Additionally, CoulombFlux.lean defines `coulombKernel'` duplicating `coulombKernel` from CoulombKernel.lean, and `vGrad'` duplicating `vGrad` from Defs.lean.

LandauMatrixDerivBound.lean has bridging lemmas (lines 377-380):
```
lemma normSq'_eq_VML : normSq' = VML.normSq := rfl
lemma eucNorm'_eq_VML : eucNorm' = VML.eucNorm := rfl
lemma innerLandauMatrix'_eq_VML : innerLandauMatrix' = VML.innerLandauMatrix := rfl
lemma landauMatrix'_eq_VML : landauMatrix' = VML.landauMatrix := rfl
```

These confirm the duplicates are definitionally equal. But:
- 3 copies of the same 4-6 definitions = ~15 redundant definitions total.
- Readers must verify that the primed definitions match the unprimed ones.
- Refactoring either copy risks silent divergence.
- CoulombFlux.lean has `PSDIntegrand'` (a 7th duplicate) duplicating `PSDIntegrand` from Defs.lean.

### 6d. Linter suppressions

Three files suppress `linter.unusedSimpArgs`:
- Defs.lean, Section3Helpers.lean, Section7.lean

This is benign (the linter is overzealous about `simp` argument usage), but it would be better to fix the root cause.

---

## 7. Documentation

**Verdict: GOOD.**

**Strengths:**
- Every major theorem has a docstring with reference to the tex document (e.g., "Reference: Lemma 20 (lem:poisson_boltzmann)").
- The FlatTorus3 class has a detailed 40-line comment block explaining the axiom design (lines 279-318 of Defs.lean), including justification for why each axiom requires IsSpatiallyDiff guards.
- The Coulomb files explain the singularity cancellation argument in header comments.
- The hGradBound redundancy is now explicitly documented in the CoulombConcreteTheorem42 header (lines 71-73).
- MEMORY.md is thorough and up to date (last updated cycle 24, correctly reports 0 sorry's and all key lemma statuses).

**Gaps:**
- No standalone documentation of the overall proof strategy. A reader must reconstruct the proof flow from import chains and docstrings. A top-level ARCHITECTURE.md or a proof outline in the main theorem's docstring would help.
- Dead code in Section3Helpers.lean (4 unused lemmas: `transport_entropy_vanishes_torus`, `vml_energy_conservation`, `B_mean_conserved_from_axioms`, `faraday_stokes_integral_zero_v2`) should be removed or marked as unused.

---

## 8. Generalization Opportunities

1. **Dimension generalization.** The formalization is hardcoded to `Fin 3`. The abstract chain (Sections 2-9) could work for `Fin n` with `n >= 2`, except for the cross product (which is specific to n=3). This would require replacing `cross` with a wedge product or exterior derivative formulation.

2. **Kernel generalization.** The abstract Theorem42 is already parametric in Psi. However, the concrete theorem is stated only for the Coulomb kernel. The smooth-kernel instance (VelocityDecayInstance / `schwartzDecayConditions`) is proved but not packaged into an end-user theorem analogous to `CoulombConcreteTheorem42`. This means the "smooth kernel" case is only half-finished from a user perspective.

3. **FlatTorus3 could be split.** The 23-field typeclass combines differential operators (grad, div, curl), integration axioms (Fubini, IBP), compact-space analysis (harmonic => constant, Laplacian at extrema), and flat geometry (Killing => harmonic, irrotational+solenoidal => harmonic). Splitting into `SmoothManifold3`, `CompactMeasuredSpace`, and `FlatMetric` would improve modularity and make each component individually reusable.

4. **The IsMaxwellian/IsLogQuadratic characterization** could be generalized to any dimension and any quadratic form, not just the Euclidean normSq.

---

## 9. Mathlib Upstreamability

| Component | Upstreamable? | Notes |
|---|---|---|
| `normSq`, `eucNorm` | NO | Mathlib already has `inner_self_eq_norm_sq`, `EuclideanDist` |
| `cross` | MAYBE | Mathlib has `crossProduct` for `Fin 3 -> R`; this duplicates it |
| `velocity_ibp` | MAYBE | Wraps Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` per component |
| `inverse_poly_integrable` | YES | General integrability of `(1+||v||)^{-N}` in `R^n` for `N > n`. Currently proved for n=3, N=4 but the argument generalizes. |
| `inv_norm_local_integrable` (NewtonianPotential) | YES | `||v||^{-1}` is locally integrable in R^3; useful for PDE library |
| `newtonian_schwartz_uniform_bound` | YES | Convolution of Newtonian kernel with Schwartz function is uniformly bounded |
| `landauMatrix_entry_fderiv_norm_bound` | MAYBE | Specific to Landau collision operator |
| Torus instance helper lemmas | YES | `integral_derivative_periodic_zero` (fundamental theorem of calculus for periodic functions), `torus_hIBP_spatial` (IBP on AddCircle), `torus_hHarmonic_const` (harmonic implies constant on torus) |
| `analysis_nonneg_dbl_zero` | MAYBE | Nonneg continuous double integral = 0 implies pointwise = 0. General enough for Mathlib. |
| `gaussian_first_moment` | MAYBE | Gaussian first moment formula. Could generalize beyond Fin 3. |

Most of the project-specific material is too specialized for Mathlib. The Newtonian potential, integrability lemmas, and torus IBP helpers would be the best candidates.

---

## 10. Overall Assessment

### Summary Table

| Criterion | Verdict | Severity | Change from previous review |
|---|---|---|---|
| Sorry's | PASS | -- | No change |
| Hidden axioms | PASS | -- | No change |
| Circularity | PASS | -- | No change |
| Hypothesis audit | CONCERN | Medium | Improved (hGradBound comment added) |
| Mathematical correctness | MINOR CONCERN | Low-Medium | Improved (5 tautologies removed) |
| Code quality | CONCERN | Medium | No change (duplicates + heartbeats remain) |
| Documentation | GOOD | -- | Improved (hGradBound documented) |
| Generalization | Opportunities noted | Low | No change |
| Upstreamability | Limited | Low | No change |

### Key findings

**In favor of acceptance:**
- Zero sorry's, zero hidden axioms, clean import DAG.
- The core mathematical content is nontrivial and correctly formalized: H-theorem, nullspace characterization, polynomial identity extraction, maximum principle, Coulomb PSD continuity, flux differentiability under the integral sign.
- The concrete torus instance (~1,200 lines) is fully proved -- all 23 FlatTorus3 fields.
- The Coulomb VelocityDecayConditions (18 fields) are all proved from the 13 hypotheses of CoulombConcreteTheorem42.
- The overall proof structure faithfully follows the standard kinetic-theory argument (Desvillettes-Villani style).
- The 5 tautological theorems identified in the previous review have been removed.
- The hGradBound redundancy is now explicitly documented.

**Against acceptance:**

1. **Dead code remains.** Four lemmas in Section3Helpers.lean are no longer called from the main proof chain: `transport_entropy_vanishes_torus`, `vml_energy_conservation`, `B_mean_conserved_from_axioms`, `faraday_stokes_integral_zero_v2`. These are artifacts of removed tautological theorems and should be cleaned up.

2. **Duplicate definitions persist.** ~15 redundant primed definitions (`normSq'`, `eucNorm'`, `innerLandauMatrix'`, `landauMatrix'`, `coulombKernel'`, `vGrad'`, `PSDIntegrand'`) across CoulombFlux.lean and LandauMatrixDerivBound.lean. The Aristotle prover compatibility excuse is understandable but the duplicates should be eliminated in a polished submission.

3. **Hypothesis non-minimality in CoulombConcreteTheorem42.** The polynomial score bound (hypothesis 9, `hGradBound`) is derivable from Schwartz decay + stretched-exponential lower bound (hypotheses 7-8). The comment is honest, but the theorem as stated is weaker than the mathematical result it claims to formalize. This remains the most substantive mathematical criticism.

4. **32 heartbeat overrides** (up to 20x default) indicate fragile proofs that may break on Mathlib version bumps.

5. **The abstract Theorem42 is borderline unreadable** due to 31 hypotheses (13 top-level + 18 bundled). While each is justified, the theorem statement alone is ~150 lines. Compare this to the 13-hypothesis CoulombConcreteTheorem42 statement, which is the version a mathematician would actually read.

6. **Near-tautological wrappers remain.** `nonpositive_integral_zero_compact` and `divergence_scalar_linear` in Section3Helpers.lean are still thin wrappers that just apply their hypothesis. They are called from the proof chain but contribute no mathematical content.

### Recommendation

**ACCEPT WITH MINOR REVISIONS.**

The mathematical content is correct and substantial. The formalization achieves something genuinely difficult: a fully kernel-verified proof of the VML steady-state characterization for the physically relevant Coulomb kernel, with all integrability conditions discharged. The improvement since the last review (5 tautological theorems removed, hGradBound redundancy documented) shows responsiveness to critique. The remaining concerns are:

- **Required:** Remove dead code (4 unused lemmas in Section3Helpers.lean).
- **Recommended:** Eliminate duplicate primed definitions by having Aristotle-generated proofs import the canonical definitions.
- **Recommended:** Prove hGradBound from hypotheses 7-8, or accept the non-minimality as a known limitation.
- **Nice to have:** Audit heartbeat-heavy proofs for potential simplification.
