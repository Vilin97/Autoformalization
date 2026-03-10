# Adversarial Review: Lean 4 Formalization of VML Steady-State Theorem

**Reviewer posture:** Hostile -- looking for every weakness, gap, and issue.

**Scope:** 23 `.lean` files in `Aristotle/Landau/main/`, 9,801 lines total.

**Date:** 2026-03-10

---

## Verdict: ACCEPT WITH MINOR REVISIONS

The formalization is technically sound (0 sorry's, all FlatTorus3 axioms discharged on a concrete instance, Coulomb theorem fully kernel-verified). However, significant dead code, primed-definition duplication, hypothesis non-minimality, and an incomplete smooth-kernel path weaken the contribution.

---

## 1. Sorry Count

**Result: 0 sorry's.**

Grep for `sorry` across all 23 files returns exactly 2 hits, both in comments:
- `TorusInstance.lean:1008` -- "0 sorry's" in a status comment
- `TorusInstance.lean:1137` -- "0 sorry's" in a summary comment

No `sorry` token appears in any proof term. No `axiom` declarations found. No `admit`, `native_decide`, or `unsafe` declarations found.

**Residual risk:** A stale `.olean` cache could mask a sorry. A fresh `lake clean && lake build` should be run to verify.

**Assessment: PASS.**

---

## 2. Typeclass Fields as Axioms

### 2a. FlatTorus3 (23 property fields)

`FlatTorus3` (Defs.lean:308) is a typeclass with 23 property fields plus 3 instance fields and 3 operator fields. **All 23 property fields are fully proved** in the concrete instance on `Torus3 = Fin 3 -> AddCircle 1` (TorusInstance.lean:1011-1129). No field is left as `sorry` or `by exact?`.

**Concerns:**

1. **Over-axiomatization.** Several fields are trivial consequences of Mathlib:
   - `hSpatialAdd` is literally `fun g1 g2 h1 h2 => integral_add h1 h2` -- this is Mathlib's `integral_add`, not a deep property.
   - `hGradIntegrable` is proved from continuity + compactness, a generic pattern.
   - `hDivLinear` follows directly from `fderiv` linearity.

   Stuffing these into the typeclass inflates the interface (23 fields!) and obscures which properties are genuinely deep (hHarmonic_const, hLaplacianMaxNonpos, hKillingToHarmonic).

2. **IsSpatiallyDiff = ContDiff R top (C-infinity).** The spatial differentiability predicate is set to "C-infinity" (`ContDiff R top (periodicLift f)`), which is stronger than the C^1 or C^2 regularity that suffices mathematically. This forces unnecessarily strong smoothness hypotheses at the theorem level. However, it simplifies closure properties (e.g., `hDiff_grad` giving `ContDiff top (fderiv)` for free) and is physically defensible for the smooth steady states under consideration.

3. **hSpatialVelocityFubini takes an unused hypothesis.** The field signature takes `(forall x, Integrable (F x))` AND joint integrability. The concrete instance ignores the per-section hypothesis entirely, using only `integral_integral_swap hF_joint`. The pointwise integrability argument is dead weight in the axiom signature.

### 2b. VMLSteadyState (intermediate derived structure)

`VMLSteadyState` (Defs.lean:606) is a structure with 26 fields. Its docstring correctly says "NOT an input specification -- all fields are proved from physical hypotheses in `VMLInput.toSteadyState`." All 26 fields are derived in VMLInputDerive.lean:357-421. This is sound design.

### 2c. VMLInput (physical input structure)

`VMLInput` (Defs.lean:680) has ~30 fields including 6 "analytical interface hypotheses" (hDiff_maxwellian, hPolynomialIdentity, hJ_from_maxwellian, hPB_eq, hNormalization, hD_zero/hScoreForm).

**Key finding:** In `Theorem42` (Theorem42.lean:111), all 6 analytical interface hypotheses are derived from genuine physical hypotheses before the VMLInput is constructed. The VMLInput is an internal API, not the theorem statement. The top-level Theorem42 takes only physical hypotheses + VelocityDecayConditions.

### 2d. VelocityDecayConditions (18 fields)

`VelocityDecayConditions` (Theorem42.lean:24) bundles 18 integrability/decay conditions. For the Coulomb case, all 18 are proved in CoulombConcreteTheorem42.lean (~230 lines of field-filling).

**Concern:** The `hPSD_cont` field (PSD integrand jointly continuous) is a non-trivial mathematical result, not merely a "decay condition." For Coulomb, proving it requires showing the score-difference cancels the kernel singularity. The bundling name is misleading.

**Assessment: PASS with concerns noted.**

---

## 3. Dead Code

### 3a. `schwartzDecayConditions` (DEAD -- ~400 lines)

`schwartzDecayConditions` (VelocityDecayInstance.lean:400) constructs a `VelocityDecayConditions` for smooth bounded kernels. It proves all 18 fields. But **no user-facing theorem ever calls it**. It is only mentioned in comments (ConcreteTheorem42.lean:12, VelocityDecayInstance.lean:6). The smooth-kernel concrete theorem does not exist.

This means approximately 400+ lines in VelocityDecayInstance.lean serve no purpose in the current build.

### 3b. Dependent dead lemmas

`lorentz_component_bound` (VelocityDecayInstance.lean:790) is used only inside `schwartzDecayConditions`. Therefore it is transitively dead.

### 3c. Missing smooth-kernel theorem

`ConcreteTheorem42.lean` (94 lines) defines `UniformSchwartzDecay`, `inverse_poly_integrable`, and two integrability lemmas, but **no theorem statement is present**. The file header says "For smooth bounded kernels, use `schwartzDecayConditions` + `Theorem42` (assembly required; no user-facing theorem yet)." This is an incomplete code path.

### 3d. All other declarations are live

Every other theorem/lemma/def (outside the smooth-kernel path) has at least one usage beyond its definition site. I checked all declarations with grep usage count = 2 (definition + one use) and confirmed each is genuinely used in the proof chain. There are no orphaned proofs in the Coulomb path.

**Assessment: MINOR ISSUE.** ~400 lines of dead code should be removed or clearly marked as future work. The incomplete smooth-kernel path should be documented or completed.

---

## 4. Code Quality

### 4a. File sizes

| File | Lines | Notes |
|---|---|---|
| TorusInstance.lean | 1,164 | Justified (proves 23 non-trivial axioms) |
| VelocityDecayInstance.lean | 809 | ~400 lines dead code |
| Defs.lean | 761 | Definitions + FlatTorus3 class + helpers |
| VelocityDecayHelpers.lean | 749 | Smooth-kernel helper lemmas |
| CoulombPSD.lean | 713 | PSD continuity + integrability |
| CoulombSpatialTransport.lean | 661 | Transport integrability |
| Section3Helpers.lean | 637 | Analytical gap lemmas |
| CoulombFluxDiff.lean | 627 | Flux differentiability |
| CoulombFlux.lean | 608 | Flux integrability |

9 of 23 files exceed 600 lines. This is borderline for maintainability but individually each file has a coherent theme.

### 4b. `maxHeartbeats` overrides: 31 total

31 `set_option maxHeartbeats` overrides across 11 files, plus 1 `synthInstance.maxHeartbeats`:

| Heartbeat level | Count | Peak files |
|---|---|---|
| 4,000,000 (20x default) | 1 | VelocityDecayInstance (dead code) |
| 3,200,000 (16x default) | 6 | CoulombPSD (3), CoulombFlux (2), NewtonianPotential (1) |
| 1,600,000 (8x default) | 9 | Various |
| 800,000 (4x default) | 12 | Various |
| synthInstance 160,000 | 1 | CoulombSpatialTransport |

The highest live-code override is 3,200,000 (16x default), appearing 6 times. These indicate heavy typeclass resolution from `Fin 3 -> R` interacting with Mathlib's `Pi` instances, especially for the Coulomb kernel. This is a maintenance risk on Mathlib updates but not a correctness issue.

### 4c. AI-generated proof style

Several lemmas in Section3Helpers.lean, LandauMatrixDerivBound.lean, CoulombFlux.lean, and CoulombPSD.lean are annotated "Proved by Aristotle" (the Harmonic automated prover). These proofs tend to use compressed tactics with heavy `simp_all +decide`, `nlinarith`, and `generalize_proofs` chains. Example: `gaussian_normalization_maxwellian` (Section3Helpers.lean:33-52) is 20 lines of dense chain reasoning. The proofs ARE kernel-checked, so correctness is guaranteed, but auditability suffers.

**Assessment: MINOR ISSUES.** The heartbeat overrides and file sizes could be improved. AI proof style reduces readability but not correctness.

---

## 5. Duplicate Primed Definitions

11 primed definitions duplicate VML namespace originals across 3 files:

| Primed name | Defined in | Canonical VML name |
|---|---|---|
| `normSq'` | CoulombFlux.lean:11, LandauMatrixDerivBound.lean:36 | `VML.normSq` |
| `eucNorm'` | CoulombFlux.lean:12, LandauMatrixDerivBound.lean:38 | `VML.eucNorm` |
| `innerLandauMatrix'` | CoulombFlux.lean:13, LandauMatrixDerivBound.lean:40 | `VML.innerLandauMatrix` |
| `landauMatrix'` | CoulombFlux.lean:16, LandauMatrixDerivBound.lean:43 | `VML.landauMatrix` |
| `coulombKernel'` | CoulombFlux.lean:15 | `VML.coulombKernel` |
| `vGrad'` | CoulombFlux.lean:18 | `VML.vGrad` |
| `PSDIntegrand'` | CoulombPSD.lean:8 | `VML.PSDIntegrand` |

**Issues:**
1. **Double definition.** `normSq'`, `eucNorm'`, `innerLandauMatrix'`, `landauMatrix'` are each defined **twice** -- in both `LandauMatrixDerivBound.lean` and `CoulombFlux.lean`. Due to namespace scoping (LandauMatrixDerivBound.lean is outside VML namespace; CoulombFlux.lean is inside VML namespace), these do not collide, but the duplication is confusing.

2. **Minimal bridging.** Only 1 formal bridging lemma exists (`landauMatrix'_eq_VML : landauMatrix' = VML.landauMatrix := rfl` at LandauMatrixDerivBound.lean:364). The other 10 primed definitions rely on definitional equality without formal verification.

3. **Origin.** These exist because the Aristotle prover generates standalone proofs with local definition copies. The CoulombFlux.lean header explicitly says "Inline definitions for standalone Aristotle proofs (all equal to VML defs by rfl)."

**Assessment: MINOR ISSUE.** The primed definitions are definitionally equal to their unprimed counterparts (`rfl`-equal by inspection), but the duplication and lack of systematic bridging is poor hygiene.

---

## 6. Documentation Accuracy

### 6a. Hypothesis count for CoulombConcreteTheorem42

The header claims "13 total, 12 independent + 1 likely derivable." Counting the actual explicit parameters in the theorem signature:

1. `hnu` (nu > 0)
2. `hrho_ion` (rho_ion > 0)
3. `hf_pos` (f > 0)
4. `hf_smooth_v` (f smooth in v)
5. `hf_smooth_x` (f smooth in x)
6. `hB_smooth` (B smooth)
7. `hSchwartz` (uniform Schwartz decay)
8. `hExpDecay` (stretched-exponential lower bound)
9. `hGradBound` (polynomial score bound -- the "likely derivable" one)
10. `hVlasov` (Vlasov equation)
11. `hAmpere` (Ampere's law)
12. `hGauss` (Gauss's law)
13. `hDivB` (div B = 0)

**Count is accurate.** The documentation is honest about hypothesis 9 being likely redundant.

### 6b. ConcreteTheorem42.lean misleading header

The file header says: "For smooth bounded kernels, use `schwartzDecayConditions` + `Theorem42` (assembly required; no user-facing theorem yet)." This is honest about the absence of a smooth-kernel theorem, but the file name `ConcreteTheorem42.lean` suggests a complete result.

### 6c. Physical limitations are documented

The `CoulombConcreteTheorem42` docstring explicitly states: "Single species, non-relativistic, 3D flat torus, Coulomb kernel." Scope limitations are not hidden.

**Assessment: PASS.**

---

## 7. Physical Limitations

### 7a. Kernel coverage

| Kernel | gamma | Status |
|---|---|---|
| Coulomb | -3 | Fully proved (CoulombConcreteTheorem42) |
| Smooth bounded | N/A | Infrastructure built but no theorem stated |
| Soft potentials | -3 < gamma < 0 | NOT covered |
| Hard potentials | gamma > 0 | NOT covered |
| Maxwell molecules | gamma = 0 | NOT covered |
| Hard spheres | compact support | Excluded by `hPsi : forall r, 0 < Psi r` |

Only the Coulomb case has a complete end-to-end theorem. The Coulomb kernel is the physically most important case.

### 7b. Dimension and domain

- Velocity space: hardcoded to `Fin 3 -> R`. The mathematical argument works in any dimension d >= 2, but `cross` is 3D-specific and the polynomial extraction lemmas are hardcoded for `Fin 3`.
- Spatial domain: flat tori only. `FlatTorus3` requires flatness axioms (Killing -> harmonic, curl-free + div-free -> harmonic). Curved geometries would fail.

### 7c. Other restrictions

- **Single species** against uniform ion background. No multi-species plasmas.
- **Non-relativistic** Vlasov equation.
- **Existence assumed.** The theorem characterizes solutions conditional on their existence. Existence of smooth steady states for VML is itself a major open problem.
- **Coulomb kernel value at 0:** Defined as `if r <= 0 then 1 else r ^ (-3)`. The value at 0 is irrelevant since `landauMatrix Psi 0 = 0` always (the projection |z|^2 I - z z^T vanishes at z = 0). This design choice is documented and sound.

**Assessment: PASS (within stated scope).** The physical limitations are inherent and documented.

---

## 8. Architecture Analysis

### 8a. Proof chain depth

The proof traverses 4 layers:
1. `CoulombConcreteTheorem42` (13 hypotheses, concrete torus, Coulomb kernel)
2. `Theorem42` (abstract FlatTorus3, abstract kernel, VelocityDecayConditions)
3. `main_from_physics` / `VMLInput.toSteadyState` (derives VMLSteadyState from VMLInput)
4. `main_steady_state` (uses VMLSteadyState to invoke individual section lemmas)

Each layer serves a purpose: (1) is user-facing with concrete types, (2) separates kernel-independent logic, (3) derives analytical conclusions from physical inputs, (4) assembles the final result from section-by-section proofs. The indirection is defensible but makes tracing a single mathematical fact through the codebase nontrivial.

### 8b. Classical.choice for parameter extraction

Maxwellian parameters (a_loc, b_loc, c_loc) are extracted via `Classical.choice` (VMLInputDerive.lean:64-76). The parameters are uniquely determined by f, but the extraction creates definitionally opaque functions. This is standard Lean practice and does not affect soundness.

### 8c. The b_0 rescaling in VMLSteadyState

In `VMLInput.toSteadyState` (VMLInputDerive.lean:386), the drift parameter `b_0` in VMLSteadyState is defined as `(-1 / (2 * p.c0)) * p.b0` rather than `p.b0` directly. This rescaling (drift velocity = (-1/(2c)) * b) corresponds to the physical drift velocity u = b/(-2c). The factor threading is correct but makes the code harder to follow. The proof that u = 0 (VMLInputDerive.lean:231-259) correctly shows that the rescaled b_0 being zero implies the original b_0 is zero (since c_0 != 0).

### 8d. Theorem42 has 54 effective conditions

Theorem42 takes 13 explicit hypotheses + 18 bundled in VelocityDecayConditions + the abstract `[FlatTorus3 X]` instance (23 fields) = 54 total conditions. The concrete CoulombConcreteTheorem42 collapses this to 13 hypotheses (all FlatTorus3 fields from the instance, all VelocityDecayConditions proved inline). This is the version a reader should evaluate.

**Assessment: PASS.** The architecture is complex but each abstraction layer is justified.

---

## Summary Table

| # | Category | Finding | Severity |
|---|---|---|---|
| 1 | Sorry count | 0 sorry's confirmed | None (strength) |
| 2a | FlatTorus3 axioms | All 23 fields proved on concrete torus | None (strength) |
| 2b | IsSpatiallyDiff | = ContDiff R top, stronger than needed | Minor |
| 2c | VMLInput interface | All analytical hypotheses honestly discharged | None (strength) |
| 2d | VelocityDecayConditions | All 18 fields proved for Coulomb | None (strength) |
| 3a | Dead code | ~400 lines: `schwartzDecayConditions` + helpers | Minor |
| 3b | Missing smooth theorem | ConcreteTheorem42.lean has no theorem | Minor |
| 4a | File sizes | 9 of 23 over 600 lines, max 1,164 | Minor |
| 4b | maxHeartbeats | 31 overrides, max 3.2M in live code | Minor |
| 4c | AI proof style | ~36 AI-generated proofs, compressed | Minor |
| 5 | Primed definitions | 11 duplicates across 3 files, 4 doubly-defined | Minor |
| 6 | Documentation | Accurate hypothesis counts, honest about gaps | Pass |
| 7a | Kernel coverage | Only Coulomb fully instantiated | Moderate |
| 7b | Dimension/domain | Hardcoded to 3D flat torus | Limitation |
| 7c | Physical scope | Single species, non-relativistic, existence assumed | Limitation |
| 8 | Architecture | 4-layer abstraction, justified but complex | Minor |

---

## Recommendations

**Required for acceptance:**
1. Remove or clearly mark as "future work" the ~400 lines of dead smooth-kernel code (`schwartzDecayConditions` and its exclusive dependencies).
2. Either complete `ConcreteTheorem42.lean` with an actual smooth-kernel theorem statement, or rename the file to `CoulombHelpers.lean` to avoid suggesting a missing theorem.

**Strongly recommended:**
3. Eliminate primed duplicates. Replace all primed uses with canonical VML namespace names, or at minimum add `rfl` bridging lemmas for all 11 primed definitions.
4. Remove the unused first argument of `hSpatialVelocityFubini` (the pointwise integrability hypothesis that is never used).

**Recommended:**
5. Document physical limitations (single species, 3D, non-relativistic) in the main theorem (`CoulombConcreteTheorem42`) docstring. Currently documented but could be more prominent.
6. Consider splitting Defs.lean (761 lines) into pure definitions and the FlatTorus3 typeclass.
7. Audit 3.2M heartbeat proofs for simplification opportunities.

---

## Final Assessment

This is a genuine, substantial formalization. The zero-sorry achievement across ~9,800 lines covering the full VML steady-state theorem for Coulomb collisions is technically impressive. The core mathematics -- H-theorem, nullspace characterization, polynomial identity extraction, Killing's equation on T^3, Poisson-Boltzmann maximum principle, Coulomb PSD continuity, flux differentiability -- is all correctly formalized and kernel-verified. The concrete theorem `CoulombConcreteTheorem42` has a clean 13-hypothesis statement that matches the physical content of Theorem 42 from the referenced paper.

The issues identified (dead code, primed definitions, missing smooth theorem, over-axiomatization of FlatTorus3) are engineering concerns that do not compromise mathematical validity. The physical limitations (dimension, domain, species, kernel) are inherent scope choices, honestly documented.

**ACCEPT WITH MINOR REVISIONS.**
