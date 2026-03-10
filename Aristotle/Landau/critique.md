# Adversarial Critique: VML Steady-State Formalization (Coulomb Kernel on T^3)

**Reviewer posture:** Hostile. Looking for reasons to REJECT.

**Scope:** 24 `.lean` files, 11,193 lines, claimed 0 sorry's.

---

## 1. Sorry's

**Verdict: PASS (with caveat).**

A grep for `\bsorry\b` across all 24 files returns zero hits outside of comments (the word "sorry" appears only in comments like "0 sorry's"). No `sorry` token is present in proof terms.

**Caveat:** The project has not been rebuilt from scratch in this review session. A stale `.olean` cache could in principle mask a `sorry` that Lean would catch on a fresh `lake build`. The reviewer would ideally run a clean build. This is a procedural gap, not a logical one.

---

## 2. Hidden Axioms

**Verdict: PASS.**

| Escape hatch | Status |
|---|---|
| `sorry` | 0 |
| `axiom` | 0 (all "axiom" occurrences are in comments/docstrings) |
| `admit` | 0 |
| `native_decide` | 0 |
| `unsafe` | 0 |
| `Decidable.decide` | Used only via `simp +decide` for `Fin 3` case splits -- this is sound Lean 4 kernel reduction, not native code execution |

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
9. `hGradBound : exists Cg Kg, forall x v i, |df/dv_i| <= Cg*(1+||v||)^Kg * f x v` -- **strong**
10-13: The PDE system (Vlasov, Ampere, Gauss, divB=0)

**Concern 4c-1: Redundancy of hGradBound.** For a function that is both C-infinity and Schwartz (hypotheses 4 and 7), the polynomial score bound (hypothesis 9) is automatic: if f is Schwartz and f > 0 with stretched-exponential lower bound (hypothesis 8), then |df/dv_i|/f = |d(log f)/dv_i| grows at most polynomially (Schwartz numerator, lower-bounded denominator). The fact that hypothesis 9 is stated separately suggests the authors could not prove this derivation in Lean. This is not a soundness issue but a completeness gap -- the hypothesis list is not minimal.

**Concern 4c-2: The stretched-exponential lower bound (hypothesis 8).** This is a physically reasonable but mathematically non-trivial assumption. For steady-state solutions of VML, such a lower bound is not obviously a consequence of the other hypotheses. The paper should justify this assumption more carefully.

---

## 5. Mathematical Correctness

**Verdict: SUBSTANTIAL CONCERNS.**

### 5a. Tautological theorems

Several "theorems" in the formalization are literally their own hypothesis:

- **`lhs_entropy_vanishes` (Section4.lean:20):** Takes a hypothesis `htransport` that the transport integral vanishes, and returns `htransport`. The proof is literally `htransport`. This theorem contributes zero mathematical content.

- **`symmetrized_weak_form` (Section3.lean:22):** Takes a hypothesis `hSWF` asserting the symmetrized weak form identity, and returns `hSWF`. Proof is `hSWF`. Zero content.

- **`polynomial_identity_velocity` (Section5.lean:33):** Its conclusion is `True`. The proof is `intros; trivial`. This is a theorem that proves True.

- **`B_mean_conserved` (Section9.lean:35):** Proof is `B_mean_conserved_from_axioms X spatialIntegral B hLeibniz hComponent`, which just forwards to a helper that takes the same hypotheses.

- **`energy_conserved` (Section9.lean:22):** Proof is `vml_energy_conservation a b c totalEnergy _hE_def`, another forwarding.

These are not wrong -- Lean checks them -- but they inflate the theorem count without adding mathematical substance. A hostile reviewer would argue that these "theorems" are scaffolding dressed up as results.

### 5b. The core proof chain IS nontrivial

The genuinely nontrivial parts of the formalization are:
1. **H-theorem** (Section3.lean): D(f) <= 0 via PSD quadratic form. Real proof content.
2. **D=0 => Maxwellian** (Section3.lean): Parallelism argument, affine gradient recovery. Real proof content.
3. **Polynomial identity extraction** (Section5.lean): Expanding the collisionless transport equation. Real proof content.
4. **Maximum principle** (Section7.lean): Poisson-Boltzmann + Laplacian at extrema. Real proof content.
5. **Coulomb PSD continuity** (CoulombPSD.lean): Cancellation of singularity. Real proof content.
6. **Coulomb flux differentiability** (CoulombFluxDiff.lean): Differentiation under the integral sign. Real proof content.
7. **Torus instance** (TorusInstance.lean): All 23 fields proved. Real proof content.
8. **VelocityDecayConditions for Coulomb** (CoulombConcreteTheorem42.lean): All 18 fields proved. Real proof content.

### 5c. The IsMaxwellian extraction uses Classical.choice

In `VMLInputDerive.lean:65`:
```
private def VMLInput.isMaxwellian_at (p : VMLInput X) (x : X) : IsMaxwellian (p.f x) := ...
noncomputable def VMLInput.a_loc (p : VMLInput X) : X -> R := fun x => (p.isMaxwellian_at x).choose
```

The Maxwellian parameters (a, b, c) are extracted via `Classical.choice` from the existential proof that f is Maxwellian. This is mathematically sound (the parameters are uniquely determined by f), but the use of `choice` means the extracted functions `a_loc`, `b_loc`, `c_loc` are definitionally opaque. The formalization then needs to thread differentiability of these functions through the FlatTorus3 machinery, which it does via `maxwellian_params_isSpatiallyDiff`. This is correct but inelegant.

### 5d. The hardcoded dimension 3

The entire formalization is hardcoded to `Fin 3 -> R` for velocity space. This is physically correct (3D plasma) but mathematically restrictive. The abstract theory (H-theorem, nullspace characterization) works in any dimension d >= 2. The cross product `cross` and the specific matrix algebra are 3-dimensional, but much of the structure could be generalized.

---

## 6. Code Quality

### 6a. File sizes

| File | Lines | Assessment |
|---|---|---|
| TorusInstance.lean | 1,222 | Borderline. Could split spatial IBP proofs out. |
| VelocityDecayHelpers.lean | 1,002 | Borderline. |
| VelocityDecayInstance.lean | 1,001 | Borderline. |
| Section3Helpers.lean | 926 | OK for a helpers file. |
| Defs.lean | 776 | Heavy for a definitions file (contains FlatTorus3 + derived lemmas). |
| CoulombPSD.lean | 716 | OK. |
| CoulombSpatialTransport.lean | 661 | OK. |
| CoulombFluxDiff.lean | 627 | OK. |
| CoulombFlux.lean | 608 | OK. |

No file exceeds 1,300 lines, which is acceptable. The recent cleanup (LandauMatrixDerivBound: 644 -> 428) is noted.

### 6b. Heartbeat overrides

**32 `set_option maxHeartbeats` directives across 13 files.** This is a high count. The worst offenders:

| File | Max heartbeats | Count |
|---|---|---|
| VelocityDecayInstance.lean | 4,000,000 | 1 |
| NewtonianPotential.lean | 3,200,000 | 1 |
| CoulombPSD.lean | 3,200,000 | 3 |
| CoulombFlux.lean | 3,200,000 | 2 |
| CoulombSpatialTransport.lean | 1,600,000 | 2 |

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

The comments say "Inline definitions for standalone Aristotle proofs (all equal to VML defs by rfl)". This means these were created to interface with the Aristotle automated prover, which works on self-contained files. While the duplicates are definitionally equal (by rfl), this is a code quality problem:
- 3 copies of the same 4 definitions = 12 redundant definitions.
- Readers must verify that the primed definitions match the unprimed ones.
- Refactoring either copy risks silent divergence.

### 6d. Linter suppressions

Three files suppress `linter.unusedSimpArgs`:
- Defs.lean, Section3Helpers.lean, Section7.lean

This is benign (the linter is overzealous about `simp` argument usage), but it would be better to fix the root cause.

---

## 7. Documentation

**Verdict: GOOD, with gaps.**

**Strengths:**
- Every major theorem has a docstring with reference to the tex document (e.g., "Reference: Lemma 20 (lem:poisson_boltzmann)").
- The FlatTorus3 class has a detailed comment block explaining the axiom design.
- The Coulomb files explain the singularity cancellation argument.
- MEMORY.md is thorough and up to date.

**Gaps:**
- No standalone documentation of the overall proof strategy. A reader must reconstruct the proof flow from import chains and docstrings.
- The tautological theorems (Section 5a above) have detailed docstrings that describe mathematical content they do not actually prove.
- The primed duplicate definitions lack explanation of *why* they exist (Aristotle prover compatibility) in most locations.

---

## 8. Generalization Opportunities

1. **Dimension generalization.** The formalization is hardcoded to `Fin 3`. The abstract chain (Sections 2-9) could work for `Fin n` with `n >= 2`, except for the cross product (which is specific to n=3). This would require replacing `cross` with a wedge product or exterior derivative formulation.

2. **Kernel generalization.** The abstract Theorem42 is already parametric in Psi. However, the concrete theorem is stated only for the Coulomb kernel. The smooth-kernel instance (VelocityDecayInstance) is proved but not packaged into an end-user theorem analogous to CoulombConcreteTheorem42.

3. **FlatTorus3 could be split.** The 23-field typeclass combines differential operators, integration axioms, and harmonic analysis. Splitting into `SmoothManifold3`, `CompactMeasuredSpace`, and `FlatMetric` would improve modularity.

4. **The IsMaxwellian/IsLogQuadratic characterization** could be generalized to any dimension and any quadratic form, not just the Euclidean normSq.

---

## 9. Mathlib Upstreamability

| Component | Upstreamable? | Notes |
|---|---|---|
| `normSq`, `eucNorm` | NO | Mathlib already has `inner_self_eq_norm_sq`, `EuclideanDist` |
| `cross` | MAYBE | Mathlib has `crossProduct` for `Fin 3 -> R`; this duplicates it |
| `velocity_ibp` | MAYBE | Wraps Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` per component |
| `inverse_poly_integrable` | YES | General integrability of `(1+||v||)^{-N}` in `R^n` for `N > n` |
| `inv_norm_local_integrable` (NewtonianPotential) | YES | `||v||^{-1}` is locally integrable in R^3; useful for PDE library |
| `newtonian_schwartz_uniform_bound` | YES | Convolution of Newtonian kernel with Schwartz function is uniformly bounded |
| `landauMatrix_entry_fderiv_norm_bound` | MAYBE | Specific to Landau collision operator |
| Torus instance helper lemmas | YES | Periodicity, IBP on AddCircle, harmonic => constant |

Most of the project-specific material is too specialized for Mathlib. The Newtonian potential and integrability lemmas would be the best candidates.

---

## 10. Overall Assessment

### Summary Table

| Criterion | Verdict | Severity |
|---|---|---|
| Sorry's | PASS | -- |
| Hidden axioms | PASS | -- |
| Circularity | PASS | -- |
| Hypothesis audit | CONCERN | Medium |
| Mathematical correctness | CONCERN | Medium |
| Code quality | CONCERN | Medium |
| Documentation | GOOD | -- |
| Generalization | Opportunities noted | Low |
| Upstreamability | Limited | Low |

### Key findings

**In favor of acceptance:**
- Zero sorry's, zero hidden axioms, clean import DAG.
- The core mathematical content is nontrivial and correctly formalized: H-theorem, nullspace characterization, polynomial identity extraction, maximum principle, Coulomb PSD continuity, flux differentiability under the integral sign.
- The concrete torus instance (1,222 lines) is fully proved -- all 23 FlatTorus3 fields.
- The Coulomb VelocityDecayConditions (18 fields) are all proved from the 13 hypotheses of CoulombConcreteTheorem42.
- The overall proof structure faithfully follows the standard kinetic-theory argument (Desvillettes-Villani style).

**Against acceptance:**
1. **Tautological theorems inflate the result count.** At least 5 named theorems (lhs_entropy_vanishes, symmetrized_weak_form, polynomial_identity_velocity -> True, B_mean_conserved, energy_conserved) have trivial or forwarding proofs. This is intellectually dishonest presentation, even if each Lean term type-checks.

2. **Duplicate definitions.** Three copies of `normSq'`, `eucNorm'`, `innerLandauMatrix'`, `landauMatrix'` across Defs, LandauMatrixDerivBound, and CoulombFlux. The Aristotle prover compatibility excuse is understandable but the duplicates should be eliminated in a polished submission.

3. **Hypothesis non-minimality in CoulombConcreteTheorem42.** The polynomial score bound (hypothesis 9) should be derivable from Schwartz decay + stretched-exponential lower bound (hypotheses 7-8), but is stated as an independent hypothesis. This makes the theorem weaker than it should be.

4. **32 heartbeat overrides** (up to 20x default) indicate fragile proofs that may break on Mathlib version bumps.

5. **The abstract Theorem42 is borderline unreadable** due to 31 hypotheses (13 top-level + 18 bundled). While each is justified, the theorem statement alone is 150 lines. Compare this to the 13-hypothesis CoulombConcreteTheorem42 statement, which is the version a mathematician would actually read.

### Recommendation

**ACCEPT WITH REVISIONS.**

The mathematical content is correct and substantial. The formalization achieves something genuinely difficult: a fully kernel-verified proof of the VML steady-state characterization for the physically relevant Coulomb kernel, with all integrability conditions discharged. The concerns above are presentation and code quality issues, not soundness issues. Specifically:

- Remove or clearly mark the tautological theorems as "interface lemmas" rather than presenting them as mathematical results.
- Eliminate the duplicate primed definitions by having Aristotle-generated proofs import the canonical definitions.
- Either prove that hypothesis 9 (hGradBound) follows from hypotheses 7-8, or add a comment explaining the gap.
- Audit heartbeat-heavy proofs for potential simplification.
