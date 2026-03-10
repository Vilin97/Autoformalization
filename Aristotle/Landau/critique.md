# Adversarial Critique: VML Steady-State Formalization (Coulomb Kernel on T^3)

**Reviewer posture:** Hostile. Looking for reasons to REJECT.

**Scope:** 24 `.lean` files, 10,378 lines (by `wc -l`), claimed 0 sorry's.

**Date:** 2026-03-10 (post-cleanup cycle 48: major dead code removal -- uniformMaxwellianDecay block, Section3 dead theorems/helpers, scattered dead bridging lemmas).

**Changes since last critique (cycle 48):**
- VelocityDecayHelpers.lean (1002 to 749): Removed ~240-line `uniformMaxwellianDecay` block (dead code)
- Section3.lean (378 to 194): Removed 4 dead named theorems (`entropy_dissipation_formula`, `D_zero_implies_parallel`, `functional_eq_affine`, `nullspace_iff`) + 4 dead helper lemmas (`mulVec_integral_comm`, `ibp_real_line`, `dotProduct_integral_comm`, `const_times_integral_deriv_zero`)
- Section2.lean: Removed dead `vecMul_landauMatrix_self` (-14 lines)
- TorusInstance.lean: Removed dead `periodicLift_continuous` + `torus_hSpatialAdd` (-11 lines)
- LandauMatrixDerivBound.lean: Removed 3 dead bridging lemmas (`normSq'_eq_VML`, `eucNorm'_eq_VML`, `innerLandauMatrix'_eq_VML`) (-3 lines)
- CoulombPSD.lean: Removed dead `PSDIntegrand'_eq_PSDIntegrand` (-3 lines)
- Total: 10,837 to 10,378 lines (-459 lines)

---

## 1. Sorry's

**Verdict: PASS.**

A grep for `sorry` across all 24 files returns zero hits outside of comments. The word "sorry" appears only in documentation strings ("0 sorry's") in TorusInstance.lean and VelocityDecayInstance.lean. No `sorry` token is present in any proof term.

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
| `Decidable.decide` | Used only via `simp +decide` for `Fin 3` case splits -- sound kernel reduction. |

No user-declared axioms. The only axioms in the TCB are Lean 4's kernel axioms (`propext`, `Quot.sound`, `Classical.choice`) and Mathlib's, which is standard.

`set_option` usage (35 total across 13 files):
- `linter.unusedSimpArgs false` in 3 files (Defs, Section3Helpers, Section7) -- suppresses a lint warning, does not affect soundness.
- `maxHeartbeats` raised in 31 locations across 11 files -- performance only, does not affect soundness.
- `synthInstance.maxHeartbeats` raised in 1 location (CoulombSpatialTransport.lean) -- performance only.
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
              +-- CoulombKernel -->                        CoulombFlux --> CoulombFluxDiff
              +-- CoulombConcreteTheorem42 (imports CoulombSpatialTransport, CoulombFlux, CoulombPSD, CoulombFluxDiff)
          +-- VelocityDecayHelpers (imports Theorem42, LandauMatrixDerivBound)
              +-- VelocityDecayInstance
```

No cycles. Each file imports only upstream dependencies.

---

## 4. Hypothesis Audit

**Verdict: CONCERNS -- see below.**

### 4a. The FlatTorus3 typeclass (29 total items: 3 instances + 3 operators + 1 predicate + 22 properties)

This is an unusually large typeclass. While every field is proved for the concrete instance `Torus3 = Fin 3 -> AddCircle 1`, the design raises concerns:

**Concern 4a-1: Over-axiomatization.** Several fields are redundant or could be derived from others. For example:
- `hSpatialAdd` is just `integral_add` -- already a Mathlib lemma. The concrete instance proves this by literally `fun g1 g2 h1 h2 => integral_add h1 h2`. Why is this a typeclass field?
- `hGradIntegrable` (gradient components of differentiable functions are integrable) follows on any compact space from continuity + compactness. It should not need to be a typeclass field.
- `hDivLinear` is a trivial consequence of `fderiv` linearity.

These "axioms" are proved for the concrete instance, so they are not false, but stuffing them into the typeclass inflates the interface and obscures which properties are genuinely deep.

**Concern 4a-2: hSpatialVelocityFubini drops a hypothesis.** The field signature takes both `(forall x, Integrable (F x))` and joint integrability on the product space. The concrete instance proves this by `integral_integral_swap hF_joint`, discarding the per-section integrability hypothesis. The abstract formulation demands joint integrability anyway, so the per-section integrability hypothesis is dead weight. Not a soundness issue but a design smell.

### 4b. VelocityDecayConditions (19 fields)

This is a massive bundle of integrability and differentiability hypotheses passed to Theorem42. All 19 fields are verified for both the smooth kernel case (VelocityDecayInstance) and the Coulomb kernel case (CoulombConcreteTheorem42), so the bundle is honest. However:

**Concern 4b-1:** The abstract Theorem42 takes 19 hypotheses bundled into VelocityDecayConditions, plus 13 more top-level hypotheses (hnu, hrho_ion, hPsi, hf_pos, hf_smooth, hf_int, hAmpere, hGauss, hDivB, hDiff_B, hVlasov, hDiff_fv, hDecay). Total: 32 hypotheses. This makes the abstract statement essentially unreadable. A reader cannot easily tell what the minimal assumptions are.

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

The comment in CoulombConcreteTheorem42.lean (lines 71-73) reads:

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

**Verdict: MINOR CONCERNS -- dead code substantially reduced but not fully eliminated.**

### 5a. Previous dead code from cycle 47 -- RESOLVED

All items identified in the cycle 47 critique have been removed:
- 9 dead lemmas from Section3Helpers.lean
- 3 dead definitions from Defs.lean (`IsLogQuadratic`, `IsMaxwellian.isLogQuadratic`, `hDiff_sub`)

### 5b. Previous dead code from cycle 48 critique -- RESOLVED

All items identified in the cycle 48 critique have been removed:
- ~240-line `uniformMaxwellianDecay` block from VelocityDecayHelpers.lean
- 4 dead named theorems + 4 dead helper lemmas from Section3.lean
- `vecMul_landauMatrix_self` from Section2.lean
- `periodicLift_continuous` + `torus_hSpatialAdd` from TorusInstance.lean
- 3 dead bridging lemmas from LandauMatrixDerivBound.lean
- `PSDIntegrand'_eq_PSDIntegrand` from CoulombPSD.lean

**Responsiveness to critique demonstrated across two review cycles.** All 23+ flagged items have been removed.

### 5c. NEW dead code found (third round)

Despite two rounds of cleanup, a third exhaustive search reveals additional dead code that was not previously identified. This dead code falls into three tiers:

**Tier 1: Dead "library" theorems in Section files (~90 lines across 6 files)**

These are named theorems that correspond to numbered lemmas in the paper but are never referenced by the proof chain. The proof chain bypasses them, using VMLInputDerive.lean to directly invoke the Section3Helpers lemmas.

| Dead theorem | File:Line | Lines | Mathematical content |
|---|---|---|---|
| `global_entropy_production_zero` | Section4.lean:17 | 11 | Wrapper around `nonpositive_integral_zero_compact` |
| `pointwise_entropy_dissipation_zero` | Section4.lean:37 | 9 | Wrapper around `nonpositive_integral_zero_compact` |
| `bulk_velocity_constant` | Section5.lean:50 | 11 | Wrapper around `killing_constant_torus` |
| `force_balance` | Section5.lean:73 | 10 | Wrapper around `force_balance_from_polynomial` |
| `E_dot_u_zero` | Section5.lean:89 | 10 | E . u = 0 from zeroth-order term |
| `ampere_steady_state` | Section6.lean:26 | 10 | `curX B x = rho x * u_infty` (trivial rewrite) |
| `poisson_boltzmann_density` | Section7.lean:46 | 16 | PB equation for density |
| `density_constant_max_principle` | Section7.lean:71 | 14 | Wrapper around `poisson_boltzmann_max_principle` |
| `laplacian_nonpos_at_max` | Section7.lean:124 | 4 | Wrapper around `FlatTorus3.hLaplacianMaxNonpos` |
| `laplacian_nonneg_at_min` | Section7.lean:131 | 4 | Wrapper around `FlatTorus3.hLaplacianMinNonneg` |
| `B_compatible_maxwellian` | Section8.lean:20 | 11 | `(v x B) . v = 0` |
| `B_infty_determination` | Section9.lean:14 | 6 | B_infty as spatial mean |
| `T_infty_determination` | Section9.lean:25 | 8 | T_infty from energy conservation |
| `T_positive` | Section9.lean:39 | 13 | T_infty > 0 from Jensen |

**Total: 14 dead theorems, ~137 lines** (including docstrings/comments). These exist as standalone mathematical statements corresponding to numbered lemmas in the paper. They were presumably added for expository completeness but are not on the critical proof path.

**Tier 2: Transitively dead Section3Helpers lemmas (~35 lines)**

These Section3Helpers lemmas are used ONLY by the dead Section theorems above and have no other callers:

| Dead lemma | File:Line | Lines | Only caller |
|---|---|---|---|
| `nonpositive_integral_zero_compact` | Section3Helpers.lean:561 | 9 | `global_entropy_production_zero`, `pointwise_entropy_dissipation_zero` (both dead) |
| `killing_constant_torus` | Section3Helpers.lean:628 | 18 | `bulk_velocity_constant` (dead) |
| `divergence_scalar_linear` | Section3Helpers.lean:646 | 9 | `poisson_boltzmann_density` (dead) |
| `force_balance_from_polynomial` | Section3Helpers.lean:685 | 16 | `force_balance` (dead) |

**Note:** `nonpositive_integral_zero_compact` was flagged as "near-tautological" in the previous critique. Now it is also transitively dead. Similarly, `divergence_scalar_linear` was flagged as a thin wrapper; it is now also transitively dead. Both critiques are vindicated.

**Tier 3: Dead utility lemmas in other files (~60 lines)**

| Dead declaration | File:Line | Lines | Notes |
|---|---|---|---|
| `landauMatrix_symmetric` | Section2.lean:26 | 4 | Proved but never used |
| `innerLandauMatrix_symmetric` | Section2.lean:16 | 8 | Used only by dead `landauMatrix_symmetric` |
| `norm_le_eucNorm'` | LandauMatrixDerivBound.lean:61 | 11 | Proved but never used |
| `innerLandauEntry_val` | LandauMatrixDerivBound.lean:128 | 10 | Proved but never used |
| `torusMk_continuous` | TorusInstance.lean:41 | 2 | Proved but never used (torusMk is continuous by construction; the proof is trivial and nobody references it) |
| `laplacian_nonpos_at_max_rn` | TorusInstance.lean:728 | 41 | General R^n Laplacian max principle. Never called -- `torus_hLaplacianMaxNonpos` re-proves the result directly for the torus via a self-contained 63-line proof. This is the second-largest single dead code block. |

**Total new dead code: ~232 lines across 11 files.** Breakdown:
- Tier 1 (dead Section theorems): ~137 lines across Section4-9
- Tier 2 (transitively dead Section3Helpers lemmas): ~52 lines
- Tier 3 (dead utility lemmas): ~76 lines (including `laplacian_nonpos_at_max_rn` at 41 lines)

### 5d. Assessment of dead code severity

The dead code in Tiers 1-2 consists primarily of **named paper theorems** (Lemma 18, Lemma 19, Lemma 20, etc.) that are stated as individual `theorem` declarations but bypassed by the actual proof chain, which uses VMLInputDerive.lean to directly chain the underlying helper lemmas. This means:

1. The Section files (4-9) function as a "library" of paper-matching theorem statements, but the actual proof takes a shortcut by calling the helpers directly.
2. The dead theorems are not mathematically incorrect -- they are correct restatements of results that happen to be proved differently in the critical path.
3. The dead code creates confusion about which declarations are load-bearing. A reader of Section5.lean would see 5 theorems and assume all are part of the proof chain, but only `polynomial_identity_from_vlasov` is.

**This is a design issue, not a correctness issue.** But it inflates the codebase by ~2.2% with unused material.

### 5e. Near-tautological wrappers remaining in the proof chain

The previous critique flagged `nonpositive_integral_zero_compact` and `divergence_scalar_linear` as near-tautological. Both are now transitively dead (see 5c Tier 2). The proof chain no longer relies on any tautological wrappers.

### 5f. The core proof chain IS nontrivial

The genuinely nontrivial parts of the formalization remain impressive:
1. **H-theorem** (Section3.lean): D(f) <= 0 via PSD quadratic form.
2. **D=0 => Maxwellian** (Section3Helpers.lean): Parallelism argument, affine gradient recovery, functional equation solution.
3. **Polynomial identity extraction** (Section5.lean): Expanding the collisionless transport equation, 222 lines.
4. **Maximum principle** (Section7.lean): Poisson-Boltzmann from Vlasov + Laplacian at extrema, 267 lines.
5. **Coulomb PSD continuity** (CoulombPSD.lean): Cancellation of the |z|^{-3} singularity via score difference regularity, 713 lines.
6. **Coulomb flux differentiability** (CoulombFluxDiff.lean): Differentiation under the integral sign via `hasFDerivAt_integral_of_dominated_of_fderiv_le`, 627 lines.
7. **Torus instance** (TorusInstance.lean): All 29 FlatTorus3 items proved for the concrete torus, 1,211 lines.
8. **VelocityDecayConditions for Coulomb** (CoulombConcreteTheorem42.lean): All 19 fields proved, 283 lines.
9. **Newtonian potential** (NewtonianPotential.lean): `newtonian_schwartz_uniform_bound` is a genuine analysis result.

### 5g. The IsMaxwellian extraction uses Classical.choice

In `VMLInputDerive.lean:65`:
```
private def VMLInput.isMaxwellian_at (p : VMLInput X) (x : X) : IsMaxwellian (p.f x) := ...
noncomputable def VMLInput.a_loc (p : VMLInput X) : X -> R := fun x => (p.isMaxwellian_at x).choose
```

The Maxwellian parameters (a, b, c) are extracted via `Classical.choice` from the existential proof that f is Maxwellian. This is mathematically sound (the parameters are uniquely determined by f), but the use of `choice` means the extracted functions `a_loc`, `b_loc`, `c_loc` are definitionally opaque. The formalization then needs to thread differentiability of these functions through the FlatTorus3 machinery, which it does via `maxwellian_params_isSpatiallyDiff`. This is correct but inelegant.

### 5h. The hardcoded dimension 3

The entire formalization is hardcoded to `Fin 3 -> R` for velocity space. This is physically correct (3D plasma) but mathematically restrictive. The abstract theory (H-theorem, nullspace characterization) works in any dimension d >= 2. The cross product `cross` and the specific matrix algebra are 3-dimensional, but much of the structure could be generalized.

### 5i. Smooth kernel instance is not packaged as an end-user theorem

`schwartzDecayConditionsEB` in VelocityDecayInstance.lean constructs the VelocityDecayConditions for a smooth bounded kernel, but it is never assembled into an analogue of CoulombConcreteTheorem42. A reader who wants the smooth kernel result must manually thread `schwartzDecayConditionsEB` through Theorem42.

---

## 6. Code Quality

### 6a. File sizes

| File | Lines | Assessment |
|---|---|---|
| TorusInstance.lean | 1,211 | Large. Contains 41-line dead `laplacian_nonpos_at_max_rn`. Could split spatial IBP proofs out. |
| VelocityDecayInstance.lean | 1,001 | Large. Borderline. |
| VelocityDecayHelpers.lean | 749 | Improved significantly (was 1,002). Good. |
| Defs.lean | 759 | Heavy for a definitions file (contains FlatTorus3 + 29 items + derived lemmas). |
| CoulombPSD.lean | 713 | OK. |
| Section3Helpers.lean | 701 | Contains ~52 lines of transitively dead code (Tier 2). Would drop to ~649. |
| CoulombSpatialTransport.lean | 661 | OK. |
| CoulombFluxDiff.lean | 627 | OK. |
| CoulombFlux.lean | 608 | OK. |
| LandauMatrixDerivBound.lean | 425 | Contains ~21 lines of dead code. |

No file exceeds ~1,211 lines, which is acceptable.

### 6b. Heartbeat overrides

**32 `set_option` heartbeat directives across 11 files.** This is a high count. Breakdown by value:

| Heartbeat value | Multiple of default (200k) | Count |
|---|---|---|
| 800,000 | 4x | 13 |
| 1,600,000 | 8x | 11 |
| 3,200,000 | 16x | 6 |
| 4,000,000 | 20x | 1 |
| synthInstance 160,000 | (default 128k, 1.25x) | 1 |

The worst offenders by file:

| File | Max heartbeats | Count |
|---|---|---|
| CoulombSpatialTransport.lean | 1,600,000 | 7 (+1 synthInstance) |
| CoulombPSD.lean | 3,200,000 | 7 |
| CoulombFlux.lean | 3,200,000 | 4 |
| NewtonianPotential.lean | 3,200,000 | 4 |
| Section3Helpers.lean | 800,000 | 2 |
| LandauMatrixDerivBound.lean | 1,600,000 | 2 |
| VelocityDecayInstance.lean | 4,000,000 | 1 |
| CoulombFluxDiff.lean | 1,600,000 | 1 |
| Section3.lean | 800,000 | 1 |
| TorusInstance.lean | 800,000 | 1 |
| VelocityDecayHelpers.lean | 800,000 | 1 |

The default is 200,000. A 4,000,000 heartbeat proof is 20x the default -- a sign of typeclass search hell or deeply nested unfolding. The `synthInstance.maxHeartbeats 160000` in CoulombSpatialTransport.lean confirms typeclass diamond issues with `HSMul` resolution.

**Verdict:** Not a soundness issue, but indicates that the code would be fragile under Mathlib updates. High heartbeat proofs are a maintenance time bomb.

### 6c. Duplicate definitions

**MAJOR CONCERN (unchanged from previous review; worsened by expanded count).** The following definitions are duplicated across files:

| Definition | Defs.lean (VML namespace) | LandauMatrixDerivBound.lean | CoulombFlux.lean | CoulombPSD.lean |
|---|---|---|---|---|
| `normSq` / `normSq'` | Yes | Yes | Yes | Yes |
| `eucNorm` / `eucNorm'` | Yes | Yes | Yes | Yes |
| `innerLandauMatrix` / `innerLandauMatrix'` | Yes | Yes | Yes | -- |
| `landauMatrix` / `landauMatrix'` | Yes (parametric) | Yes (parametric) | Yes (Coulomb-specialized) | Yes |
| `coulombKernel` / `coulombKernel'` | -- (in CoulombKernel.lean) | -- | Yes | Yes |
| `vGrad` / `vGrad'` | Yes | -- | Yes | Yes |
| `PSDIntegrand` / `PSDIntegrand'` | Yes | -- | -- | Yes |

Total: **7 distinct definitions duplicated** across files. Precise occurrence counts in non-comment code:

| Primed identifier | Total occurrences | Distribution by file |
|---|---|---|
| `normSq'` | 58 | LandauMatrixDerivBound: 42, CoulombFluxDiff: 6, CoulombFlux: 5, CoulombPSD: 5 |
| `eucNorm'` | 91 | LandauMatrixDerivBound: 60, CoulombPSD: 22, CoulombFluxDiff: 6, CoulombFlux: 3 |
| `innerLandauMatrix'` | 31 | LandauMatrixDerivBound: 20, CoulombFluxDiff: 7, CoulombFlux: 3, CoulombPSD: 1 |
| `landauMatrix'` | 58 | CoulombFluxDiff: 27, LandauMatrixDerivBound: 17, CoulombPSD: 10, CoulombFlux: 4 |
| `coulombKernel'` | 12 | CoulombFluxDiff: 6, CoulombFlux: 3, CoulombPSD: 3 |
| `vGrad'` | 14 | CoulombFlux: 10, CoulombPSD: 4 |
| `PSDIntegrand'` | 2 | CoulombPSD: 2 |
| **Total** | **266** | LandauMatrixDerivBound: 139, CoulombFluxDiff: 52, CoulombPSD: 47, CoulombFlux: 28 |

**266 total occurrences of primed identifiers across 4 files** (up from the previously reported 240, due to more careful counting). These duplicates exist because the Aristotle prover generates standalone proofs that define their own local copies of the mathematical objects. The bridging lemma `landauMatrix'_eq_VML : landauMatrix' = VML.landauMatrix := rfl` in LandauMatrixDerivBound.lean confirms definitional equality. However:

- The previous cycle removed 4 of 5 dead bridging lemmas (`normSq'_eq_VML`, `eucNorm'_eq_VML`, `innerLandauMatrix'_eq_VML`, `PSDIntegrand'_eq_PSDIntegrand`). Only `landauMatrix'_eq_VML` survives (used at lines 418, 427). This means **no formal verification exists that the 6 other primed definitions match their canonical counterparts.** A reader must manually inspect each `def` to confirm `normSq' = normSq`, etc. While they are definitionally equal (and Lean would catch any mismatch at use sites), the lack of explicit bridging lemmas is a documentation gap.
- Refactoring one copy risks silent divergence in the other.
- This remains the single largest code quality concern.

### 6d. Linter suppressions

Three files suppress `linter.unusedSimpArgs`:
- Defs.lean, Section3Helpers.lean, Section7.lean

This is benign (the linter is overzealous about `simp` argument usage), but it would be better to fix the root cause.

---

## 7. Documentation

**Verdict: GOOD (improved by dead code removal).**

**Strengths:**
- Every major theorem has a docstring with reference to the tex document (e.g., "Reference: Lemma 20 (lem:poisson_boltzmann)").
- The FlatTorus3 class has detailed comment blocks explaining the axiom design, including justification for why each axiom requires IsSpatiallyDiff guards.
- The Coulomb files explain the singularity cancellation argument in header comments.
- The hGradBound redundancy is explicitly documented in the CoulombConcreteTheorem42 header (lines 71-73).
- Dead code removal from cycle 48 significantly clarified VelocityDecayHelpers.lean (no more unused uniformMaxwellianDecay block) and Section3.lean (no more dead expository theorems).

**Remaining gaps:**
- No standalone documentation of the overall proof strategy. A reader must reconstruct the proof flow from import chains and docstrings.
- The remaining dead code in Sections 4-9 creates confusion about which lemmas are load-bearing. Section5.lean has 5 theorems but only 1 (`polynomial_identity_from_vlasov`) is on the critical path. Section7.lean has 10 declarations but only 4 (`poisson_boltzmann_algebraic`, `electric_field_zero`, `continuous_attains_max/min`, `poisson_boltzmann_from_vlasov`) are used.
- The header comment of CoulombConcreteTheorem42 says "13 total, down from 15 in ConcreteTheorem42" but ConcreteTheorem42.lean says "15 total." Neither file explains which hypotheses were dropped, making the "down from 15" claim hard to verify without cross-referencing.

---

## 8. Generalization Opportunities

1. **Dimension generalization.** The formalization is hardcoded to `Fin 3`. The abstract chain (Sections 2-9) could work for `Fin n` with `n >= 2`, except for the cross product (which is specific to n=3). This would require replacing `cross` with a wedge product or exterior derivative formulation.

2. **Kernel generalization.** The abstract Theorem42 is already parametric in Psi. However, the concrete theorem is stated only for the Coulomb kernel. The smooth-kernel instance (VelocityDecayInstance / `schwartzDecayConditionsEB`) is proved but not packaged into an end-user theorem analogous to `CoulombConcreteTheorem42`. That means the "smooth kernel" case is only half-finished from a user perspective.

3. **FlatTorus3 could be split.** The 29-item typeclass combines differential operators (grad, div, curl), integration axioms (Fubini, IBP), compact-space analysis (harmonic => constant, Laplacian at extrema), and flat geometry (Killing => harmonic, irrotational+solenoidal => harmonic). Splitting into `SmoothManifold3`, `CompactMeasuredSpace`, and `FlatMetric` would improve modularity and make each component individually reusable.

4. **The IsMaxwellian characterization** could be generalized to any dimension and any quadratic form, not just the Euclidean normSq.

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
| Hypothesis audit | CONCERN | Medium | No change |
| Mathematical correctness | MINOR CONCERN | Low | **Improved** -- all previously-flagged dead items removed; ~232 new lines found |
| Code quality | CONCERN | Medium | No change (duplicates + heartbeats remain) |
| Documentation | GOOD | -- | **Improved** (dead code removal clarified VelocityDecayHelpers, Section3) |
| Generalization | Opportunities noted | Low | No change |
| Upstreamability | Limited | Low | No change |

### Key findings

**In favor of acceptance:**
- Zero sorry's, zero hidden axioms, clean import DAG.
- The core mathematical content is nontrivial and correctly formalized: H-theorem, nullspace characterization, polynomial identity extraction, maximum principle, Coulomb PSD continuity, flux differentiability under the integral sign.
- The concrete torus instance (~1,211 lines) is fully proved -- all 29 FlatTorus3 items.
- The Coulomb VelocityDecayConditions (19 fields) are all proved from the 13 hypotheses of CoulombConcreteTheorem42.
- The overall proof structure faithfully follows the standard kinetic-theory argument (Desvillettes-Villani style).
- **Two rounds of dead code cleanup have been executed in response to previous critiques.** All 23+ previously-flagged items were removed. Total codebase reduced from 11,011 to 10,378 lines (-633 lines, -5.7%). Responsiveness to critique is strongly demonstrated.
- The hGradBound redundancy is honestly documented.

**Against acceptance:**

1. **Dead code persists at reduced scale.** Despite removing all previously-identified dead code, ~232 new lines of dead code remain:
   - **14 dead Section theorems (~137 lines):** `global_entropy_production_zero`, `pointwise_entropy_dissipation_zero`, `bulk_velocity_constant`, `force_balance`, `E_dot_u_zero`, `ampere_steady_state`, `poisson_boltzmann_density`, `density_constant_max_principle`, `laplacian_nonpos_at_max`, `laplacian_nonneg_at_min`, `B_compatible_maxwellian`, `B_infty_determination`, `T_infty_determination`, `T_positive`. These are paper-matching theorem statements (Lemmas 11-12, 15-16, 17-18, 20-21, 23, 26-28) that are bypassed by the actual proof chain.
   - **4 transitively dead Section3Helpers lemmas (~52 lines):** `nonpositive_integral_zero_compact`, `killing_constant_torus`, `divergence_scalar_linear`, `force_balance_from_polynomial`. Their only callers are the dead Section theorems above.
   - **6 dead utility lemmas (~76 lines):** `landauMatrix_symmetric` + `innerLandauMatrix_symmetric` (Section2), `norm_le_eucNorm'` + `innerLandauEntry_val` (LandauMatrixDerivBound), `torusMk_continuous` (TorusInstance), `laplacian_nonpos_at_max_rn` (TorusInstance, 41 lines alone).

   The dead code represents ~2.2% of the codebase. While reduced from the previous ~3.4%, it is still non-trivial.

2. **Duplicate definitions persist.** 7 distinct definitions duplicated across files, totaling **266 occurrences of primed identifiers** across CoulombFlux.lean, CoulombFluxDiff.lean, CoulombPSD.lean, and LandauMatrixDerivBound.lean. The Aristotle prover compatibility excuse is understandable but the duplicates should be eliminated in a polished submission. The removal of 4 bridging lemmas in cycle 48 actually *worsened* the situation: there is now no formal proof that 6 of the 7 primed definitions match their canonical counterparts (only `landauMatrix'_eq_VML` survives). While Lean guarantees definitional equality at use sites, the absence of explicit bridging lemmas is a regression in documentation.

3. **Hypothesis non-minimality in CoulombConcreteTheorem42.** The polynomial score bound (hypothesis 9, `hGradBound`) is derivable from Schwartz decay + stretched-exponential lower bound (hypotheses 7-8). The comment is honest, but the theorem as stated is weaker than the mathematical result it claims to formalize.

4. **32 heartbeat overrides** (up to 20x default) across 11 files indicate fragile proofs that may break on Mathlib version bumps. 6 of the 32 are at 16x (3,200,000) and 1 is at 20x (4,000,000).

5. **The abstract Theorem42 is borderline unreadable** due to 32 hypotheses (13 top-level + 19 bundled). While each is justified, the theorem statement alone is ~40 lines. Compare this to the 13-hypothesis CoulombConcreteTheorem42 statement, which is the version a mathematician would actually read.

6. **Smooth kernel case is incomplete.** `schwartzDecayConditionsEB` constructs VelocityDecayConditions for smooth bounded kernels but is never assembled into a user-facing theorem. A user must manually thread it through Theorem42.

7. **`laplacian_nonpos_at_max_rn` (41 lines) is a significant dead code block** in TorusInstance.lean. It proves the general R^n Laplacian maximum principle but `torus_hLaplacianMaxNonpos` re-proves the same result from scratch via a different, torus-specific approach (lines 837-899). This is wasted effort.

### Recommendation

**ACCEPT WITH MINOR REVISIONS.**

The mathematical content is correct and substantial. The formalization achieves something genuinely difficult: a fully kernel-verified proof of the VML steady-state characterization for the physically relevant Coulomb kernel, with all integrability conditions discharged. Two rounds of responsive dead code cleanup demonstrate engagement with review. The remaining concerns are:

- **Required:** Remove `laplacian_nonpos_at_max_rn` (41 lines of dead general-purpose lemma in TorusInstance.lean, superseded by the torus-specific proof).
- **Required:** Remove `norm_le_eucNorm'` and `innerLandauEntry_val` from LandauMatrixDerivBound.lean (dead utility lemmas, 21 lines).
- **Recommended:** Remove the 14 dead Section theorems (Sections 4-9, ~137 lines) or explicitly mark them as library-only results not on the critical path. If retaining for exposition, add a comment `-- NOTE: Not on the critical proof path; retained as a standalone statement of Lemma N.`
- **Recommended:** Remove the 4 transitively dead Section3Helpers lemmas (`nonpositive_integral_zero_compact`, `killing_constant_torus`, `divergence_scalar_linear`, `force_balance_from_polynomial`, ~52 lines).
- **Recommended:** Remove `landauMatrix_symmetric` + `innerLandauMatrix_symmetric` from Section2.lean (12 lines, never used).
- **Recommended:** Remove `torusMk_continuous` from TorusInstance.lean (2 lines, never used).
- **Recommended:** Eliminate duplicate primed definitions by having Aristotle-generated proofs import the canonical definitions. At minimum, restore bridging lemmas for the 6 primed definitions that lost their explicit equality proofs.
- **Recommended:** Prove hGradBound from hypotheses 7-8, or accept the non-minimality as a known limitation.
- **Recommended:** Package the smooth kernel case into a user-facing theorem analogous to CoulombConcreteTheorem42.
- **Nice to have:** Audit heartbeat-heavy proofs for potential simplification.
