# Adversarial Review: VML Steady-State Formalization in Lean 4

**Reviewer posture:** Hostile. Looking for reasons to REJECT.

**Scope:** 24 `.lean` files, ~10,001 lines, claimed 0 sorry's.

**Date:** 2026-03-10

---

## Verdict: ACCEPT WITH MINOR REVISIONS

The formalization achieves its stated goal: 0 sorry's across 24 files (~10,000 lines), with the main theorem (Theorem 42) and a concrete Coulomb instantiation (CoulombConcreteTheorem42) fully kernel-checked. The mathematical content is substantial and the architecture is sound. However, several issues warrant attention before this can be considered publication-ready.

---

## 1. Sorry Count

**Verdict: PASS.**

Grep for `sorry` across all 24 files in `Aristotle/Landau/main/*.lean` returns zero hits outside of comments. The word "sorry" appears only in documentation strings ("0 sorry's") in TorusInstance.lean:1137 and VelocityDecayInstance.lean:948. No `sorry` token is present in any proof term.

**Residual risk:** A stale `.olean` cache could in principle mask a `sorry` that Lean would catch on a fresh `lake build`. An ideal review would run `lake clean && lake update && lake exe cache get && lake build` from scratch.

No `axiom`, `admit`, `native_decide`, or `unsafe` declarations found.

---

## 2. Typeclass Fields as Axioms

### 2a. FlatTorus3: 23 property fields

The `FlatTorus3` typeclass (Defs.lean:308) bundles 23 property fields that act as axioms at the abstract level, plus 3 instance fields, 3 operator fields, and 1 predicate. This is an unusually large typeclass. The 23 property fields include:

- **Operator properties (5):** hDivLinear, hGradConst, hGradAdd, hGradScalarMul, hGradChainExp
- **Closed manifold integration (2):** hCurlIntZero, hIBP_spatial
- **Analysis on compact manifold (4):** hHarmonic_const, hLaplacianMaxNonpos, hSpatialPos, hSpatialNonnegZero
- **Flat geometry (2):** hKillingToHarmonic, hCurlZeroDivZeroHarmonic
- **Abstract measure (3):** hSpatialVelocityFubini, hSpatialAdd, hGradIntegrable
- **Differentiability predicate + closure (7):** IsSpatiallyDiff, hDiff_const, hDiff_add, hDiff_smul, hDiff_log, hDiff_continuous, hDiff_grad

**Mitigation:** All 23 property fields are proved for the concrete torus `Fin 3 -> AddCircle 1` in TorusInstance.lean (instance at line 1011). The instance fills every field with a proof verified by the Lean kernel.

**Remaining concerns:**

1. **Over-axiomatization.** Several fields are trivial consequences of the others or of general Mathlib results:
   - `hSpatialAdd` is literally `fun g1 g2 h1 h2 => integral_add h1 h2` in the concrete instance. It is Mathlib's `integral_add` -- why is this a typeclass field?
   - `hGradIntegrable` follows on any compact space from continuity + compactness (the concrete instance proves it in exactly this way).
   - `hDivLinear` is a trivial consequence of `fderiv` linearity.
   These "axioms" are proved for the concrete instance, so they are not false, but stuffing them into the typeclass inflates the interface and obscures which properties are genuinely deep (Hodge theory, maximum principle, Killing equation).

2. **hSpatialVelocityFubini drops a hypothesis.** The field signature takes both `(forall x, Integrable (F x))` and joint integrability on the product space. The concrete instance uses only the joint integrability (`integral_integral_swap hF_joint`), discarding the per-section hypothesis. This is dead weight in the interface.

### 2b. VMLSteadyState: An intermediate bundle of derived facts

The `VMLSteadyState` structure (Defs.lean:604) bundles the physical state together with derived analytical conclusions (Maxwellian form, temperature constancy, density constancy, normalization). Its docstring says it "Encodes: The VML equations at steady state / Analytical results from the H-theorem chain / Polynomial matching results / Maximum principle conclusion." This makes it sound like these are all assumptions.

In reality, `VMLSteadyState` is constructed from `VMLInput` via `toSteadyState` in VMLInputDerive.lean, and all the "derived" fields are proved there. So VMLSteadyState is an intermediate abstraction, not an input specification. This should be documented more clearly.

### 2c. VMLInput: 6 "analytical interface" hypotheses

The `VMLInput` structure (Defs.lean:678) contains 6 hypotheses that appear to be interface assumptions:

1. **hDiff_maxwellian** -- Maxwellian parameters are spatially differentiable
2. **hPolynomialIdentity** -- The polynomial identity from the Vlasov equation
3. **hJ_from_maxwellian** -- Current from Maxwellian: J = rho * drift
4. **hPB_eq** -- Poisson-Boltzmann equation
5. **hNormalization** -- Gaussian integral normalization
6. **hD_zero / hScoreForm** -- Entropy dissipation vanishes

**Key finding:** In Theorem42.lean, ALL of these are derived from genuine physical hypotheses before constructing VMLInput. None are additional assumptions at the top level. The VMLInput structure is used as an internal API, not as the theorem statement. The actual Theorem42 statement (line 111) takes only: physical state (f, E, B, Psi, nu, rho_ion), positivity, smoothness, integrability, Maxwell equations, Vlasov equation, spatial differentiability, and VelocityDecayConditions.

### 2d. VelocityDecayConditions: 18 integrability conditions

The `VelocityDecayConditions` structure (Theorem42.lean:24) bundles 18 integrability/decay conditions. For the Coulomb case, all 18 are proved in CoulombConcreteTheorem42.lean from the 13 physical hypotheses. For smooth kernels, `schwartzDecayConditions` proves them in VelocityDecayInstance.lean.

**Concern:** The `hPSD_cont` field (PSD integrand is jointly continuous) is a non-trivial mathematical requirement that goes far beyond "decay condition." For the Coulomb kernel, proving it requires a delicate cancellation argument (score difference O(|v-w|) cancels the |v-w|^{-3} singularity). Bundling this into "VelocityDecayConditions" is misleading nomenclature.

---

## 3. Dead Code

### 3a. Confirmed dead declarations

| Declaration | File | Lines | Status |
|---|---|---|---|
| `schwartzDecayConditionsEB` | VelocityDecayInstance.lean:949 | ~52 | Defined but never called anywhere |
| `Section9.lean` (entire file) | Section9.lean | 12 | Empty: just namespace/import boilerplate, no content |

`schwartzDecayConditionsEB` was intended to extend `schwartzDecayConditions` with E, B force transport conditions for smooth kernels, but the Coulomb formalization bypasses it entirely by constructing VelocityDecayConditions directly. The smooth kernel case has no end-user theorem.

Section9.lean references "Section 9 of tex / Lemma 25" (conservation laws) but contains no content. Either it should be deleted or a comment should explain why conservation laws are handled elsewhere (answer: normalization is handled by `hNormalization` in VMLInput).

### 3b. The smooth kernel path is incomplete

`schwartzDecayConditions` (VelocityDecayInstance.lean:401) constructs VelocityDecayConditions for smooth bounded kernels, and `schwartzDecayConditionsEB` extends it. But neither is assembled into a user-facing theorem analogous to CoulombConcreteTheorem42. A user wanting the smooth kernel result must manually thread the construction through Theorem42. This is a significant completeness gap.

---

## 4. Code Quality

### 4a. Files over 600 lines

9 of 24 files exceed 600 lines:

| File | Lines | Assessment |
|---|---|---|
| TorusInstance.lean | 1,164 | Largest file. Could split the 23 instance proofs from the helper theorem proofs. |
| VelocityDecayInstance.lean | 1,001 | Contains both the general smooth-kernel lemma (landau_flux_component_diff_with_bound, 373 lines) and the schwartzDecayConditions construction. |
| Defs.lean | 759 | Heavy: contains definitions, FlatTorus3 typeclass (23+ fields), derived lemmas, VMLSteadyState, VMLInput, VMLEquilibrium. |
| VelocityDecayHelpers.lean | 749 | Helper lemmas for decay conditions. |
| CoulombPSD.lean | 713 | PSD continuity and integrability for Coulomb. |
| CoulombSpatialTransport.lean | 661 | Spatial transport integrability for Coulomb. |
| Section3Helpers.lean | 637 | Core analysis lemmas (Gaussian integrals, functional equation, PSD arguments). |
| CoulombFluxDiff.lean | 627 | Flux differentiability for Coulomb. |
| CoulombFlux.lean | 608 | Flux integrability for Coulomb. |

### 4b. maxHeartbeats overrides: 32 total

**32 `set_option maxHeartbeats` overrides** across 11 files, plus 1 `synthInstance.maxHeartbeats` override:

| Heartbeat value | Multiple of default (200k) | Count |
|---|---|---|
| 800,000 | 4x | 13 |
| 1,600,000 | 8x | 8 |
| 3,200,000 | 16x | 6 |
| 4,000,000 | 20x | 1 |
| synthInstance 160,000 | (default 128k, 1.25x) | 1 |

The worst offenders:
- VelocityDecayInstance.lean:18 -- `landau_flux_component_diff_with_bound` at 4,000,000 (20x default)
- CoulombPSD.lean -- 7 overrides, 3 at 3,200,000
- CoulombFlux.lean -- 4 overrides, 2 at 3,200,000
- NewtonianPotential.lean -- 4 overrides, 1 at 3,200,000
- CoulombSpatialTransport.lean -- 7 overrides + 1 synthInstance override

The 4M heartbeat proof is a red flag for proof term size. These high heartbeat proofs are a maintenance time bomb that will likely break on Mathlib version updates. This is not a soundness issue but a significant engineering concern.

### 4c. Proof style

Many proofs (especially in Section3Helpers.lean) were generated by an AI system ("Proved by Aristotle") and have a compressed, hard-to-read style. For example, `gaussian_normalization_maxwellian` (Section3Helpers.lean:33-52) is a 20-line proof with dense `simp_all +decide` chains, `norm_num` invocations, and minimal comments. `parallel_curl_free_affine` (Section3Helpers.lean:398-503) is a 105-line proof that is difficult to audit manually.

The proofs ARE kernel-checked, so correctness is guaranteed. But readability suffers significantly. A total of ~36 lemmas are annotated "Proved by Aristotle" across the codebase.

---

## 5. Duplicate Primed Definitions

**This is the single largest code quality concern.**

7 distinct definitions are duplicated across files with primed names:

| Primed definition | Files where defined | VML equivalent |
|---|---|---|
| `normSq'` | LandauMatrixDerivBound.lean:36, CoulombFlux.lean:11 | `VML.normSq` |
| `eucNorm'` | LandauMatrixDerivBound.lean:38, CoulombFlux.lean:12 | `VML.eucNorm` |
| `innerLandauMatrix'` | LandauMatrixDerivBound.lean:40, CoulombFlux.lean:13 | `VML.innerLandauMatrix` |
| `landauMatrix'` | LandauMatrixDerivBound.lean:43, CoulombFlux.lean:16 | `VML.landauMatrix` |
| `coulombKernel'` | CoulombFlux.lean:15 | `VML.coulombKernel` |
| `vGrad'` | CoulombFlux.lean:18 | `VML.vGrad` |
| `PSDIntegrand'` | CoulombPSD.lean:8 | `VML.PSDIntegrand` |

Critical issues:
1. `normSq'`, `eucNorm'`, `innerLandauMatrix'`, and `landauMatrix'` are each defined **twice** (in both LandauMatrixDerivBound.lean and CoulombFlux.lean). Depending on import order, one shadows the other.
2. Only one bridging lemma exists: `landauMatrix'_eq_VML : landauMatrix' = VML.landauMatrix := rfl` (LandauMatrixDerivBound.lean:364). No formal verification exists for the other 6 primed definitions matching their canonical counterparts. While they ARE definitionally equal (Lean would catch any mismatch at use sites), the lack of explicit bridging lemmas is a documentation gap.
3. The duplicates exist because the Aristotle prover generates standalone proofs that define their own local copies of mathematical objects. This is understandable but should be cleaned up for publication.

---

## 6. Documentation Accuracy

### 6a. Hypothesis count claims

CoulombConcreteTheorem42.lean header says "13 hypotheses" but hypothesis 9 (`hGradBound`) is acknowledged in lines 71-73 as "likely derivable from hSchwartz + hExpDecay." The header should say "13 hypotheses (12 independent + 1 likely derivable)."

The derivation is straightforward: if `f` is Schwartz with `|df/dv_i| * (1+||v||)^N <= C_N` for all N, and `f(v) >= exp(-C*(1+||v||)^K)`, then `|df/dv_i| / f(v) <= C_N * exp(C*(1+||v||)^K) * (1+||v||)^{-N}`. Choosing N large enough absorbs the exponential, yielding polynomial score growth. This is honest documentation of a known formalization debt.

### 6b. Section9.lean is empty

References "Section 9 of tex / Lemma 25" but contains no content. Should be deleted or explained.

### 6c. VMLSteadyState vs VMLInput naming

VMLSteadyState's docstring makes it sound like an input specification when it is actually an intermediate bundle of derived facts. The distinction between "what we assume" (VMLInput / Theorem42 hypotheses) and "what we derive" (VMLSteadyState) should be clearer.

---

## 7. Physical Limitations

### 7a. Single species only

The formalization handles a single species of charged particles against a uniform neutralizing ion background (`rho_ion`). Multi-species plasmas (electron-ion, multiple ion species) are not covered. This is a significant limitation for physical applicability.

### 7b. Fixed spatial dimension (3D only)

Everything is hardcoded to `Fin 3 -> R` for velocity space and 3-torus for spatial domain. The abstract theory (H-theorem, nullspace characterization) works in any dimension d >= 2, but the cross product `cross` and specific matrix algebra are 3-dimensional. No mention of this limitation appears in the theorem statements.

### 7c. Non-relativistic only

The Vlasov equation is non-relativistic (`v * grad_x f`, not the relativistic form with Lorentz factors). This is standard for the Landau collision operator context but is not documented as a limitation.

### 7d. Kernel coverage

Only two kernel families are supported:

1. **Coulomb kernel** (CoulombConcreteTheorem42): `Psi(r) = r^{-3}`, the most important physical case. Fully proved with 13 hypotheses.

2. **Smooth bounded kernels** (VelocityDecayInstance): requires `Continuous Psi`, `ContDiff R 1 Psi`, bounded `Psi` and bounded `deriv Psi`. This excludes ALL physically relevant singular kernels.

**Not covered:**
- Soft potentials (`Psi(r) = r^gamma` for `-3 < gamma < 0`)
- Hard potentials (`Psi(r) = r^gamma` for `gamma > 0`)
- The Maxwell molecule case (`gamma = 0`, `Psi = const`)
- Any kernel with `gamma != -3` and singular at 0

The smooth kernel machinery cannot handle any singular kernel, and the Coulomb code is specific to `gamma = -3`. There is no intermediate construction.

### 7e. Existence assumption

The theorem assumes the existence of a smooth, positive, integrable, Schwartz-class steady-state solution. Existence of such solutions is itself a major open problem for the VML system. The formalization correctly states this as a hypothesis rather than proving existence, but this inherent limitation should be acknowledged: the theorem characterizes solutions conditional on their existence.

### 7f. Coulomb kernel definition at r=0

`coulombKernel` is defined as `if r <= 0 then 1 else r ^ (-3 : R)` (CoulombKernel.lean:16). The value 1 at `r <= 0` is arbitrary but ensures `forall r, 0 < coulombKernel r`. This is documented as irrelevant since `landauMatrix Psi 0 = 0` always (the projection `|z|^2 I - z z^T` vanishes at `z = 0`). This is mathematically correct.

---

## 8. Architectural Issues

### 8a. The two-step VMLInput -> VMLSteadyState -> main_steady_state pattern

The proof flows: build VMLInput -> derive VMLSteadyState via `toSteadyState` -> prove conclusion via `main_steady_state`. The indirection through VMLSteadyState adds complexity. A single function `VMLInput -> conclusion` would be more direct.

**Counter-argument:** The two-step design separates the derivation logic (Sections 3-7 via `toSteadyState`) from the final assembly (`main_steady_state`). The Section files (Section6, Section7, Section8) operate on VMLSteadyState, not VMLInput. This is a reasonable modularity choice.

### 8b. The abstract Theorem42 has 32 hypotheses

Theorem42 (line 111) takes 13 explicit hypotheses plus 19 bundled in VelocityDecayConditions, for 32 total. The statement is ~40 lines. This makes the abstract theorem essentially unreadable. The concrete CoulombConcreteTheorem42 with 13 hypotheses is the version a mathematician would actually read and cite.

### 8c. Classical.choice for Maxwellian parameter extraction

In VMLInputDerive.lean:65-76, the Maxwellian parameters (a, b, c) are extracted via `Classical.choice` from the existential proof that f is Maxwellian. This is mathematically sound (the parameters are uniquely determined by f), but makes the extracted functions `a_loc`, `b_loc`, `c_loc` definitionally opaque. The formalization then threads differentiability of these functions through FlatTorus3 via `maxwellian_params_isSpatiallyDiff`. This works but is inelegant -- a constructive extraction would be cleaner.

---

## Summary Table

| Category | Issues Found | Severity |
|---|---|---|
| Sorry count | 0 sorry's confirmed | None (clean) |
| Hidden axioms | 0 axioms, 0 unsafe | None (clean) |
| FlatTorus3 typeclass | 23 property fields, all proved for concrete torus | Minor (over-axiomatization) |
| VelocityDecayConditions | 18 fields, all proved for Coulomb and smooth kernels | Minor (naming/bundling) |
| Non-minimal hypothesis | hGradBound in Coulomb theorem likely redundant | Minor (documented) |
| Dead code | schwartzDecayConditionsEB never used; Section9.lean empty | Minor |
| File sizes | 9 files over 600 lines (max 1,164) | Minor |
| maxHeartbeats | 32 overrides, max 4,000,000 (20x default) | Minor (maintenance risk) |
| Primed duplicates | 7 definitions duplicated, 4 doubly-defined across 2 files | Moderate (tech debt) |
| Documentation | Hypothesis count slightly misleading; VMLSteadyState naming confusing | Minor |
| Physical scope | Single species, 3D, non-relativistic | Moderate (scope limitation) |
| Excluded kernels | Only Coulomb (gamma=-3) and smooth bounded kernels | Moderate (scope limitation) |
| Smooth kernel path | Proved but not packaged as user-facing theorem | Minor (incompleteness) |
| Existence assumption | Assumes smooth steady-state exists | Inherent (not a flaw) |

---

## Recommendations

**Required for acceptance:**
1. Remove the empty Section9.lean or add a comment explaining why it is empty.
2. Remove or mark `schwartzDecayConditionsEB` as unused.

**Strongly recommended:**
3. Eliminate duplicate primed definitions. At minimum, add bridging lemmas (`normSq'_eq_VML`, etc.) for all 7 primed definitions, not just `landauMatrix'`.
4. Document the non-minimality of hGradBound more prominently (in the theorem docstring, not just a NOTE comment).
5. Package the smooth kernel case into a user-facing theorem analogous to CoulombConcreteTheorem42.

**Recommended:**
6. Split Defs.lean (759 lines) into definitions and the FlatTorus3 typeclass.
7. Audit the highest heartbeat proofs (4M, 3.2M) for simplification opportunities.
8. Clarify in VMLSteadyState's docstring that it is an intermediate bundle of DERIVED facts, not input assumptions.
9. Add a note about the non-relativistic, single-species, 3D limitations to the main theorem docstrings.

**Overall assessment:** This is a substantial and technically sound formalization. The 0-sorry claim is verified. The core mathematical content is nontrivial and correctly formalized: H-theorem, nullspace characterization, polynomial identity extraction, maximum principle, Coulomb PSD continuity, flux differentiability under the integral sign, and a complete concrete torus instance. The primary weaknesses are code quality issues from AI-generated proofs (primed duplicates, high heartbeats) and scope limitations (single species, Coulomb only). None of these are blocking issues.
