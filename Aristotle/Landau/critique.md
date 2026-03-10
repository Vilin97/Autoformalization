# Adversarial Critique: Coulomb Concrete Theorem 42

**Reviewer posture:** Hostile. Default verdict is REJECT. The formalization must earn approval through evidence.

**Reviewed:** Full codebase at `Aristotle/Landau/main/` (23 .lean files, 11,398 total lines)
**Main theorem:** `CoulombConcreteTheorem42` in `CoulombConcreteTheorem42.lean` (280 lines)
**Date:** 2026-03-10 (fresh analysis, supersedes all prior reviews)

**Claim:** Any sufficiently smooth, positive, Schwartz-class steady-state solution of the Vlasov-Maxwell-Landau system with Coulomb collisions on T^3 is a global Maxwellian equilibrium with E = 0 and B = const.

---

## 1. Sorry's

**There are 0 `sorry` tokens in the codebase.** Grep finds exactly 3 matches for "sorry" in comments only:

- `TorusInstance.lean:1066` -- comment: "0 sorry's"
- `TorusInstance.lean:1195` -- comment: "0 errors, 0 sorry's"
- `VelocityDecayInstance.lean:1931` -- comment: "0 sorry's"

None of these are in proof terms. Every lemma has a complete proof body.

### ~~Previous sorry's~~ FIXED

~~`coulomb_entry_conv_differentiable`~~ and ~~`coulomb_entry_conv_deriv_decay`~~ were the last two sorry's. Both resolved in cycle 24. The latter was discovered to be mathematically false and replaced with `coulomb_entry_conv_deriv_bounded`.

---

## 2. Hidden Axioms

### `admit`
Zero occurrences.

### `axiom`
Zero `axiom` declarations. The word "axiom" appears only in comments across Defs.lean, Section3Helpers.lean, Section7.lean, Section9.lean, and TorusInstance.lean, referring to the FlatTorus3 typeclass fields. No Lean `axiom` keyword is used.

### `native_decide`
Zero occurrences.

### `unsafe`, `implementedBy`, `extern`
Zero occurrences.

### `Classical.arbitrary` / `Classical.choice`
Used in 3 places:
- `Theorem42.lean:232` -- `Classical.arbitrary X` for picking a reference point in `VMLInput.x0`
- `Section3Helpers.lean:819-820` -- `Classical.arbitrary X` for extracting a constant from Killing equation
- `VMLInputDerive.lean:64` -- comment only

These are standard uses of classical logic for existential witnesses. No soundness concern.

### `set_option` flags
- `linter.unusedSimpArgs false` in 3 files (Defs.lean, Section3Helpers.lean, Section7.lean). Cosmetic suppression only; does not affect proof checking.
- No `linter.all false`, no `pp.all false`, no `kernel.check false`, no flags that compromise the kernel.

**Verdict on hidden axioms: CLEAN.** The proof depends only on Lean's standard foundational axioms (propext, Quot.sound, Classical.choice) and Mathlib. No user-declared axioms.

---

## 3. Circularity

### Import dependency DAG

```
Mathlib
  <- Defs.lean (definitions, FlatTorus3 class, VMLInput)
  <- LandauMatrixDerivBound.lean (also imports Mathlib directly)
  <- Section2.lean
  <- Section3Helpers.lean (imports Defs + Section2)
     <- Section3.lean
  <- Section4.lean
  <- Section5.lean
  <- Section6.lean
  <- Section7.lean
  <- Section8.lean
  <- Section9.lean
  <- VMLInputDerive.lean (imports Sections 3-9)
     <- Theorem42.lean (abstract theorem with VelocityDecayConditions)
        <- TorusInstance.lean (FlatTorus3 instance for T^3)
        <- VelocityDecayInstance.lean (satisfiability witnesses; imports LandauMatrixDerivBound)
           <- ConcreteTheorem42.lean (smooth kernel version, UniformSchwartzDecay)
              <- CoulombKernel.lean (Coulomb kernel definition)
                 <- NewtonianPotential.lean
                 <- CoulombSpatialTransport.lean
                    <- CoulombFlux.lean
                       <- CoulombFluxDiff.lean
                       <- CoulombPSD.lean
                          <- CoulombConcreteTheorem42.lean (MAIN THEOREM)
```

**No cycles.** The DAG is strictly acyclic. The abstract theorem (Theorem42.lean) does not import the Coulomb specialization. The Coulomb files only depend downward through CoulombKernel -> ConcreteTheorem42 -> Theorem42.

### Potential logical circularity check

The abstract `Theorem42` accepts `VelocityDecayConditions` as a hypothesis. `CoulombConcreteTheorem42` constructs this structure from Schwartz/Coulomb-specific lemmas. The construction in `CoulombConcreteTheorem42.lean:158-274` provides all 18+1 fields (18 VelocityDecayConditions + hD_cont) by calling lemmas from the Coulomb files. None of these lemmas use the main theorem. **No circularity.**

---

## 4. Hypothesis Audit

The main theorem `CoulombConcreteTheorem42` has exactly 13 hypotheses:

| # | Name | Type | Assessment |
|---|------|------|------------|
| 1 | `hnu` | `0 < nu` | Genuine physical parameter. Needed to divide by nu in entropy identity. |
| 2 | `hrho_ion` | `0 < rho_ion` | Genuine physical parameter. Used in Gauss's law normalization. |
| 3 | `hf_pos` | `forall x v, 0 < f x v` | **Strict everywhere positivity.** Stronger than a.e. positivity. Needed for log f, chain rule, score definition. Standard in Villani's treatment. Honest but restrictive. |
| 4 | `hf_smooth_v` | `forall x, ContDiff R top (f x)` | **C-infinity in velocity.** Overshoot: C^2 would suffice for the chain rule and IBP arguments. |
| 5 | `hf_smooth_x` | `forall v, ContDiff R top (periodicLift (fun x => f x v))` | C-infinity of the periodic lift in spatial coordinates. Needed for gradX, chain rule, Killing equation. Overshoot: C^2 would suffice. |
| 6 | `hB_smooth` | `forall i, ContDiff R top (periodicLift (fun x => B x i))` | C-infinity of B. Used only for IsSpatiallyDiff B, which on the concrete torus means smooth periodic lift. Overshoot: C^1 suffices for curlX integral zero. |
| 7 | `hSchwartz` | `UniformSchwartzDecay f` | **The heaviest hypothesis.** Two fields: (a) all velocity derivatives decay faster than any polynomial, uniformly in x; (b) spatial gradients of f also have Schwartz velocity decay. This is used throughout for integrability of the Landau flux, PSD integrand, transport terms. Honest and standard for kinetic theory. |
| 8 | `hExpDecay` | `exists C K, forall x v, exp(-C*(1+norm v)^K) <= f x v` | Stretched-exponential lower bound. Combined with Schwartz upper bound, gives polynomial log bound. Standard. |
| 9 | `hGradBound` | `exists Cg Kg, forall x v i, abs(fderiv f_x v e_i) <= Cg*(1+norm v)^Kg * f x v` | **Polynomial score bound.** Says the score (gradient of log f) grows at most polynomially. This is the most subtle hypothesis. Satisfied by Maxwellians (K=1), stretched-Gaussians, and polynomial-score distributions. Does NOT encode the conclusion (Maxwellianity). |
| 10 | `hVlasov` | Steady-state Vlasov equation with Coulomb kernel | The PDE being studied. Honest. |
| 11 | `hAmpere` | Ampere's law: curlX B = J | Maxwell equation. Honest. |
| 12 | `hGauss` | Gauss's law: divX E = rho - rho_ion | Maxwell equation. Honest. |
| 13 | `hDivB` | Solenoidal: divX B = 0 | Maxwell equation. Honest. |

### Hypothesis-conclusion overlap analysis

**Does any hypothesis encode the conclusion?**

The conclusion states: f is a spatially uniform Maxwellian, E = 0, B = const. None of the 13 hypotheses assume spatial uniformity, Maxwellian form, vanishing E, or constant B. The Schwartz decay (7) is a velocity-space condition; the equations (10-13) are the PDE system being solved.

The polynomial score bound (9) deserves extra scrutiny: it says |nabla(log f)| grows at most polynomially. For a Maxwellian f = exp(-|v|^2/(2T)), the score is |v/T| (polynomial). But the hypothesis does not force f to be Maxwellian --- any sub-Gaussian distribution with polynomial score growth satisfies it. The key mathematical content is that the entropy dissipation formula + PSD nonneg + Fubini symmetrization force the score difference to vanish, which then forces log f to be quadratic. This is genuinely proved, not assumed.

### VMLInput intermediate structure

The abstract `Theorem42` goes through an intermediate `VMLInput` structure with additional "analytical interface" fields:
- `hDiff_maxwellian`: Maxwellian parameters are spatially differentiable. **Proved** from hDiff_fv + hf_pos via `maxwellian_params_isSpatiallyDiff`.
- `hPolynomialIdentity`: polynomial identity from Vlasov + Maxwellian form. **Proved** from Vlasov equation via `polynomial_identity_from_vlasov` (Section5.lean).
- `hJ_from_maxwellian`: current = density * drift. **Proved** from Gaussian first moment via `gaussian_first_moment` (Section3Helpers.lean).
- `hPB_eq`: Poisson-Boltzmann equation. **Proved** from Vlasov via `poisson_boltzmann_from_vlasov` (Section7.lean).
- `hNormalization`: Gaussian normalization yields equilibriumMaxwellian. **Proved** via `gaussian_normalization_maxwellian` (Section3Helpers.lean).

All of these are filled in by `Theorem42.lean:231-298` from the Vlasov equation and Mathlib Gaussian integrals. None are left as hypotheses in the final theorem. **No hidden assumptions.**

---

## 5. Mathematical Correctness

### Proof strategy faithfulness

The proof follows the standard H-theorem rigidity argument for Vlasov-Maxwell-Landau:

1. **H-theorem chain** (Sections 2-4): Entropy dissipation D(f) <= 0 (from PSD of Landau matrix). Transport entropy identity gives integral of D = 0. On compact spatial domain, D(f(x)) = 0 for all x.
2. **Maxwellian characterization** (Section 3): D(f) = 0 implies score difference vanishes a.e. in (v,w). Continuity of PSD integrand promotes to pointwise. Score constant implies log f quadratic, i.e. f is local Maxwellian.
3. **Polynomial matching** (Section 5): Substituting local Maxwellian into collisionless Vlasov equation gives polynomial identity in v. Matching coefficients: c(x) = const (temperature uniform), Killing equation for b(x), force balance for grad a.
4. **Killing equation on T^3** (Section 6): Killing vector fields on flat torus are constant. So b(x) = b0.
5. **Drift = 0** (Section 6/VMLInputDerive): Ampere + Stokes on T^3 gives |u0|^2 * integral(rho) = 0, so u0 = 0.
6. **Density constant** (Section 7): Poisson-Boltzmann + maximum principle on compact domain gives rho = rho_ion.
7. **E = 0, B = const** (Sections 7-8): From force balance + harmonic analysis on T^3.
8. **Normalization** (Section 3): Gaussian integral fixes the Maxwellian to equilibriumMaxwellian.

This is faithful to the Desvillettes-Villani / Guo approach. The Coulomb kernel requires extra work (PSD continuity despite singular kernel) which is handled in CoulombPSD.lean.

### Key mathematical subtleties correctly handled

- **Coulomb singularity cancellation**: The PSD integrand involves A(v-w) * |score_diff|^2 where A diverges like |v-w|^{-1} but score_diff = O(|v-w|) by smoothness, so the product is O(|v-w|). Proved in `psd_continuous_coulomb`.
- **Differentiation under the integral sign**: For the Landau flux, uses `hasFDerivAt_integral_of_dominated_of_fderiv_le`. Correctly requires dominated convergence conditions.
- **Fubini symmetrization**: The identity 2 * int(score(v) . A . flux) = int(score_diff . A . score_diff * f*f') requires careful Fubini + variable swap. Proved in Section3.
- **Velocity-space IBP on R^3**: Uses Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`. Correct.
- **Force transport vanishes**: (E + v x B) . nabla_v(f * log f - f) integrates to 0 by IBP + div(v x B) = 0. Proved in Section4.

### Known mathematical limitations

- **Uniqueness of temperature**: The theorem proves existence of T_eq but does not explicitly prove uniqueness. The equilibriumMaxwellian normalization handles this implicitly.
- **No bootstrap from PDE**: The Schwartz regularity is assumed, not derived from the Vlasov equation. Standard in the literature but not self-contained.

---

## 6. Code Quality

### File sizes

| File | Lines | Assessment |
|------|-------|------------|
| VelocityDecayInstance.lean | 1,984 | **Too large.** Should be split (witness 1 / witness 2). |
| TorusInstance.lean | 1,222 | Acceptable for a single complex typeclass instance (23 fields). |
| ~~Section3.lean~~ | ~~1,307~~ | ~~Too large.~~ **FIXED: split into Section3.lean (391) + Section3Helpers.lean (926).** |
| Section3Helpers.lean | 926 | Acceptable post-split. Contains gap lemmas, Gaussian integrals, analytical utilities. |
| Defs.lean | 781 | Acceptable for definitions + FlatTorus3 class + VMLInput. |
| ~~CoulombPSD.lean~~ | ~~1,325~~ | ~~Too large.~~ **FIXED: split into CoulombPSD.lean (716) + CoulombFluxDiff.lean (627).** |
| CoulombPSD.lean | 716 | Acceptable post-split. |
| CoulombSpatialTransport.lean | 661 | Borderline. |
| LandauMatrixDerivBound.lean | 647 | Contains 202 lines of custom `generalize_proofs` tactic fork. |
| CoulombFluxDiff.lean | 627 | Borderline. |
| CoulombFlux.lean | 608 | Borderline. |

**Files over 600 lines:** 9 files. **Files over 1000 lines:** 2 files (down from 3).

### Heartbeat overrides

32 `maxHeartbeats` overrides + 1 `synthInstance.maxHeartbeats` override across 12 files:

| Value | Count | Severity | Action needed |
|-------|-------|----------|---------------|
| 4,000,000 (20x default) | 1 | **Critical** | VelocityDecayInstance.lean:1001. Refactor or split. |
| 3,200,000 (16x default) | 6 | **High** | CoulombPSD (3), CoulombFlux (2), NewtonianPotential (1). |
| 1,600,000 (8x default) | 11 | Moderate | Across 6 files. |
| 800,000 (4x default) | 14 | Acceptable | Across 8 files. |
| synthInstance 160,000 | 1 | Low | CoulombSpatialTransport typeclass diamond. |

The 4M-heartbeat proof (`landau_flux_component_diff_with_bound` at VelocityDecayInstance.lean:1001) is a maintenance hazard. A Mathlib version bump could easily break it.

### `import Mathlib` (full import)

Two files use `import Mathlib` instead of granular imports:
- `Defs.lean:9`
- `LandauMatrixDerivBound.lean:25`

This pulls in the entire Mathlib library. Slows compilation and hides actual dependencies. Not a soundness issue but terrible for maintainability.

### Duplicate primed definitions

`normSq'`, `eucNorm'`, `innerLandauMatrix'`, `landauMatrix'` are independently defined in:
- `CoulombFlux.lean:11-17` (inside `VML` namespace, so qualified as `VML.normSq'`, etc.)
- `LandauMatrixDerivBound.lean:240-248` (outside any namespace, top-level `normSq'`, etc.)

Additionally, `CoulombFlux.lean` defines `VML.coulombKernel'` and `VML.vGrad'` which have no counterpart in LandauMatrixDerivBound. The `landauMatrix'` in LandauMatrixDerivBound takes `Psi` as a parameter while the one in CoulombFlux hardcodes the Coulomb kernel. Bridge lemmas (`normSq'_eq_VML`, `eucNorm'_eq_VML`, etc.) in LandauMatrixDerivBound.lean:596-599 connect them, but the duplication is confusing.

Also, `CoulombPSD.lean:8` defines `PSDIntegrand'` with a bridge to `PSDIntegrand` at line 14.

### Custom tactic code

`LandauMatrixDerivBound.lean:30-232` contains a 202-line reimplementation of `generalize_proofs` by Aristotle (Harmonic), inside `namespace Harmonic.GeneralizeProofs`. This shadows Mathlib's `generalize_proofs` via `elab (name := generalizeProofsElab'')` at line 212. The custom tactic is used in 2 places within that same file (lines 582, 589). Standard Mathlib `generalize_proofs` is used in `Section3Helpers.lean:73,75` and `CoulombFlux.lean:64` (which do not import LandauMatrixDerivBound, so they use the unmodified version). **Risk**: if LandauMatrixDerivBound is ever imported alongside files using standard `generalize_proofs`, the shadowing could cause subtle behavior differences.

### Linter suppressions

`set_option linter.unusedSimpArgs false` in 3 files. Minor; the `unusedSimpArgs` linter is noisy. ~~`linter.all false`~~ previously in all files, now removed.

---

## 7. Documentation Lies

### MEMORY.md claims vs reality

| Claim in MEMORY.md | Reality | Status |
|----|---------|--------|
| "CoulombConcreteTheorem42.lean (~280 lines)" | 280 lines | Correct |
| "CoulombFlux.lean (~609 lines)" | 608 lines | Correct |
| "CoulombPSD.lean (~1325 lines)" | 716 lines (split; CoulombFluxDiff.lean has 627) | **STALE** |
| "21 files, ~11,400 lines" | 23 files, 11,398 lines | **STALE** (missing Section3Helpers.lean and CoulombFluxDiff.lean) |
| "0 SORRY'S (as of cycle 24)" | 0 sorry's | Correct |
| "Coulomb files (split from single 1827-line file)" | CoulombPSD + CoulombFluxDiff = 1,343 lines | Line counts stale |

MEMORY.md is missing Section3Helpers.lean (926 lines) and CoulombFluxDiff.lean (627 lines) from its file inventory. It lists 21 files instead of 23.

### Previous critique claims vs reality

The previous critique (cycle 39) claimed:
- "22 .lean files, 11,388 total lines" -- now 23 files, 11,398 lines (Section3.lean was split into Section3.lean + Section3Helpers.lean)
- "Section3.lean | 1,307" -- now Section3.lean (391) + Section3Helpers.lean (926)
- "3 files over 1000 lines" -- now 2 files over 1000 lines

---

## 8. Generalization Opportunities

### 1. Dimension generalization (3D -> nD)

The entire formalization is hardcoded to `Fin 3`. The cross product `cross : (Fin 3 -> R) -> (Fin 3 -> R) -> (Fin 3 -> R)` is used for the Lorentz force `v x B`. In dimension n != 3, the Lorentz force term would use the 2-form `F_{ij}` instead. The abstract proof chain (Sections 2-9) could be generalized to `Fin n` by replacing `cross` with an antisymmetric bilinear form, but this is a significant refactoring.

**Actionable:** Abstract the dimension as a parameter `n : Nat` with `[Fintype (Fin n)]` in the definitions. The cross product dependency would need to be replaced with a general antisymmetric 2-form. Estimated effort: medium.

### 2. Kernel generalization (Coulomb -> soft potentials)

The theorem has TWO versions: `ConcreteTheorem42` (smooth kernel, Continuous Psi required) and `CoulombConcreteTheorem42` (singular Coulomb kernel). The gap between these covers soft potentials with -3 < gamma < 0 where Psi(r) = r^gamma is singular but less so than Coulomb. The PSD continuity argument would need kernel-dependent singularity cancellation bounds.

**Actionable:** Introduce a typeclass `SingularKernel` with a cancellation bound `|Psi(r) * r^2| <= C * r^{2+gamma}` for gamma > -3, and prove PSD continuity for this class. This would cover Landau kernels for all soft potentials. Estimated effort: high.

### 3. Weaken C-infinity to C^2

The theorem assumes `ContDiff R top` (C-infinity) for f in velocity and spatial variables, and for B. The proof only uses:
- First and second derivatives of f(x,.) (for vGrad, IBP, fderiv.log)
- First derivatives of f(.,v) (for gradX)
- First derivatives of B (for curlX, divX)

Moreover, `IsSpatiallyDiff` on the concrete torus is defined as `ContDiff R top (periodicLift f)`, so the abstract interface already demands C-infinity for anything fed into gradient/divergence operators. Weakening to C^2 would require changing the `IsSpatiallyDiff` predicate to `ContDiff R 2`, and verifying that `hDiff_grad` (gradient closure) still works (it would, since `ContDiff.fderiv_right` takes `ContDiff R (n+1)` to `ContDiff R n`).

**Actionable:** Replace `ContDiff R top` with `ContDiff R 2` throughout. Estimated effort: low-medium.

### 4. Consolidate primed definitions into a shared utility file

The six primed helper definitions (`normSq'`, `eucNorm'`, `innerLandauMatrix'`, `landauMatrix'`, `coulombKernel'`, `vGrad'`) are used for standalone Aristotle-proved lemmas that need self-contained definitions. These should be consolidated into a single file (e.g., `CoulombHelpers.lean`) imported by both CoulombFlux and LandauMatrixDerivBound. This would eliminate the duplication and the need for bridge lemmas.

**Actionable:** Create shared helper file. Estimated effort: low.

---

## 9. Mathlib Upstreamability

### Candidates for upstreaming

1. **`gaussian_first_moment`** (Section3Helpers.lean): First moment of multivariate Gaussian. Nontrivial computation using Fubini + 1D Gaussian moment + odd function integral = 0. **High upstreaming value.** This is a standard result that Mathlib should have.

2. **`gaussian_normalization_maxwellian`** (Section3Helpers.lean): Normalization of Gaussian integral. Uses `integral_gaussian` from Mathlib. **Medium upstreaming value.**

3. **`inverse_poly_integrable`** (ConcreteTheorem42.lean:40-55): Integrability of `C / (1 + ||v||)^4` on R^3. Uses `integrable_rpow_neg_one_add_norm_sq`. Useful utility lemma. **Medium upstreaming value.**

4. **Schwartz derivative closure** (CoulombFluxDiff.lean): Partial derivatives of Schwartz functions are Schwartz. Uses `ContinuousLinearMap.iteratedFDeriv_comp_left`. **High upstreaming value** -- basic Schwartz space fact.

5. **Torus instance utilities** (TorusInstance.lean): The `periodicLift` construction, `periodicLift_periodic`, `periodicLift_continuous`, and the FlatTorus3 instance. **Medium upstreaming value.**

### Not suitable for upstreaming

- All VML-specific definitions (LandauOperator, PSDIntegrand, etc.)
- The Coulomb kernel-specific lemmas (too specialized)
- The custom `generalize_proofs` fork in Harmonic namespace (should be reconciled with Mathlib's version, not upstreamed as a fork)

---

## Overall Assessment

### Summary table

| Component | Files | Lines | Sorry's | Assessment |
|-----------|-------|-------|---------|------------|
| Definitions (Defs.lean) | 1 | 781 | 0 | Fully verified |
| Abstract proof chain (Sections 2-9 + helpers) | 9 | 3,210 | 0 | Fully verified |
| VMLInputDerive | 1 | 437 | 0 | Fully verified |
| Theorem42 (abstract) | 1 | 302 | 0 | Fully verified |
| FlatTorus3 instance | 1 | 1,222 | 0 | Fully verified |
| VelocityDecayInstance | 1 | 1,984 | 0 | Fully verified |
| ConcreteTheorem42 (smooth kernel) | 1 | 96 | 0 | Fully verified |
| LandauMatrixDerivBound | 1 | 647 | 0 | Fully verified |
| CoulombKernel | 1 | 113 | 0 | Fully verified |
| CoulombSpatialTransport | 1 | 661 | 0 | Fully verified |
| NewtonianPotential | 1 | 283 | 0 | Fully verified |
| CoulombFlux | 1 | 608 | 0 | Fully verified |
| CoulombFluxDiff | 1 | 627 | 0 | Fully verified |
| CoulombPSD | 1 | 716 | 0 | Fully verified |
| CoulombConcreteTheorem42 | 1 | 280 | 0 | Fully verified |
| **TOTAL** | **23** | **11,398** | **0** | **Fully verified** |

### What is proved

1. **The entire abstract proof chain is complete** (Sections 2-9 + Theorem42).
2. **The FlatTorus3 typeclass has a complete concrete instance** (all 23 property fields proved from Mathlib).
3. **All 18 VelocityDecayConditions fields + hD_cont are proved for the Coulomb kernel.**
4. **The smooth-kernel concrete theorem is fully proved.**
5. **The Coulomb Concrete Theorem 42 is fully proved** -- 0 sorry's in the entire 23-file, 11,398-line dependency chain.
6. **Two non-trivial satisfiability witnesses** confirm the hypotheses are satisfiable.

### Open issues (by severity)

**High priority:**
1. **4M-heartbeat proof** (VelocityDecayInstance.lean:1001). Fragile. Will likely break on Mathlib updates. Split the proof or find a more efficient approach.
2. **6 proofs at 3.2M heartbeats.** Same fragility concern.

**Medium priority:**
3. **`import Mathlib`** in Defs.lean and LandauMatrixDerivBound.lean. Replace with granular imports to speed compilation and clarify dependencies.
4. **VelocityDecayInstance.lean at 1,984 lines.** Only file over 1000 lines (besides TorusInstance at 1,222 which is acceptable for its 23-field typeclass). Split VelocityDecayInstance.
5. **Duplicate primed definitions** across CoulombFlux.lean (VML namespace) and LandauMatrixDerivBound.lean (top-level namespace), plus `PSDIntegrand'` in CoulombPSD.lean. Consolidate into a shared file.
6. **202 lines of custom tactic code** (`generalize_proofs` fork in `Harmonic.GeneralizeProofs` namespace). Shadows Mathlib's `generalize_proofs` via `elab (name := generalizeProofsElab'')`. Remove if Mathlib's version works; otherwise upstream the improvements.
7. **Stale MEMORY.md** (says 21 files, should be 23; missing Section3Helpers.lean and CoulombFluxDiff.lean; wrong CoulombPSD line count).

**Low priority:**
8. **C-infinity overshoot** when C^2 would suffice. Does not affect correctness.
9. **`linter.unusedSimpArgs false`** in 3 files. Cosmetic.

### Structural concerns (non-blocking)

1. ~~Universal linter suppression~~ **FIXED**
2. ~~Copy-paste in schwartzDecayConditionsEB~~ **FIXED**
3. ~~2 sorry's remaining~~ **FIXED**
4. ~~Section3.lean too large (1,307 lines)~~ **FIXED: split into Section3.lean (391) + Section3Helpers.lean (926)**
5. ~~CoulombPSD.lean too large (1,325 lines)~~ **FIXED: split into CoulombPSD.lean (716) + CoulombFluxDiff.lean (627)**

### Verdict: ACCEPT

The formalization is **mathematically complete and honest**. Every lemma in the 11,398-line codebase across 23 files has a machine-checked proof verified by the Lean 4 kernel. The 13 hypotheses of the main theorem are genuine analytical conditions (positivity, smoothness, Schwartz decay, polynomial score bound, and four Maxwell-Vlasov equations) that do not encode the conclusion. Two satisfiability witnesses confirm non-vacuity of the hypotheses. The import DAG is acyclic. No hidden axioms, no sorry's, no native_decide, no admit.

The open issues above are **code quality concerns**, not soundness concerns. None affect the mathematical validity of the proof.

**Remaining work (prioritized):**
1. Reduce the 4M-heartbeat proof in VelocityDecayInstance.lean
2. Replace `import Mathlib` with granular imports in Defs.lean and LandauMatrixDerivBound.lean
3. Split VelocityDecayInstance.lean (1,984 lines)
4. Consolidate primed definitions into a shared file
5. Update MEMORY.md with correct file count (23) and line counts
6. Remove or upstream Harmonic's custom generalize_proofs tactic fork
