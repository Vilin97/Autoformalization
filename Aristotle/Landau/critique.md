# Adversarial Critique: Coulomb Concrete Theorem 42

**Reviewer posture:** Hostile. Default verdict is REJECT. The formalization must earn approval through evidence.

**Reviewed:** Full codebase at `Aristotle/Landau/main/` (21 .lean files, 10,891 total lines)
**Main theorem:** `CoulombConcreteTheorem42` in `CoulombConcreteTheorem42.lean` (280 lines)
**Date:** 2026-03-09

**Claim:** Any sufficiently smooth, positive, Schwartz-class steady-state solution of the Vlasov-Maxwell-Landau system with Coulomb collisions on T^3 is a global Maxwellian equilibrium with E = 0 and B = const.

---

## 1. Remaining Sorry's and Their Mathematical Status

There are **2 sorry tokens** in the entire codebase, both in `CoulombPSD.lean`. A third lemma (`coulomb_ibp_df_g_integrable`) has its proof body fully written but depends on the two sorry'd lemmas, making it effectively sorry'd as well. Three fields in `VelocityDecayConditions` -- `hLandauFluxDiff`, `hLandauIBP_df_g`, and (transitively) all consumers of the flux derivative -- are tainted.

| # | Lemma | File:Line | Statement | Deps |
|---|-------|-----------|-----------|------|
| 1 | `coulomb_flux_differentiable` | CoulombPSD.lean:723-730 | `Differentiable R (v -> (integral_w A(v-w) [flux])_i)` | None |
| 2 | `coulomb_flux_deriv_schwartz_decay` | CoulombPSD.lean:735-742 | `exists C > 0, forall v, norm(fderiv(flux_i)(v)) * (1+norm(v))^N <= C` | None |
| (3) | `coulomb_ibp_df_g_integrable` | CoulombPSD.lean:746-792 | `Integrable (v -> fderiv(flux_i)(v)(e_i) * log(f(v)))` | Uses 1 and 2 |

### Assessment of sorry 1: `coulomb_flux_differentiable`

**Statement:** The map `v -> (integral_w A(v-w) [f(w) grad_v f(v) - f(v) grad_w f(w)])_i` is differentiable in v, where A is the Coulomb Landau matrix.

**Is it mathematically true?** Yes. This is differentiation under the integral sign for a convolution-type operator with a locally integrable singular kernel. The argument:

1. The Coulomb Landau matrix entries satisfy `|A(z)_{ij}| <= ||z||^{-1}` (proved in the codebase as `coulomb_landauMatrix_entry_le_pi`).
2. The v-derivative of the integrand introduces terms bounded by `||v-w||^{-2}` (from differentiating the kernel) times Schwartz functions. In dimension 3, `||z||^{-2}` is locally integrable.
3. The Schwartz decay of f provides the required global domination.
4. By Leibniz's integral rule (dominated convergence for the difference quotient), the flux is differentiable.

This is standard singular integral theory (Stein, "Singular Integrals and Differentiability Properties of Functions", Chapter II). The gap is the lack of Mathlib infrastructure for differentiation under the integral sign with singular kernels -- Mathlib's `HasFDerivAt.integral` requires a uniformly integrable dominator on a neighborhood, which must be constructed explicitly for the Coulomb kernel.

**Difficulty of filling in Lean:** Hard. Requires building dominated convergence machinery for parametric singular integrals. Approximately 200-400 lines of Lean, assuming familiarity with Mathlib's measure theory API. The key difficulty is not the mathematics but wrestling the Mathlib API for `fderiv` and `MeasureTheory.integral` into the right form.

**Is it provable in Mathlib?** Yes, in principle. The required Mathlib components exist (dominated convergence, Leibniz integral rule, local integrability of `||z||^{-alpha}` for alpha < n). But assembling them for this particular kernel is substantial boilerplate.

### Assessment of sorry 2: `coulomb_flux_deriv_schwartz_decay`

**Statement:** The derivative of the Coulomb flux component decays at Schwartz rate: for every N, there exists C > 0 such that `||fderiv(flux_i)(v)|| * (1+||v||)^N <= C`.

**Is it mathematically true?** Yes. The flux is a convolution of a locally integrable kernel (`||z||^{-1}` entries after the projection) with Schwartz-class functions. Derivatives of such convolutions preserve Schwartz decay because: (a) differentiating the convolution shifts derivatives onto the Schwartz factor, and (b) the resulting integrals are bounded by iterated convolutions of `||z||^{-k}` with Schwartz functions, which remain rapidly decreasing. This is a consequence of Calderon-Zygmund theory applied to Schwartz-class inputs.

**Difficulty of filling in Lean:** Very hard. This requires either: (a) a direct dominated-convergence argument estimating the v-derivative of the convolution integral against polynomial weights, or (b) importing Calderon-Zygmund theory into Mathlib, which does not exist. Likely 300-600 lines.

**Is it provable in Mathlib?** Yes, via explicit estimates. No Calderon-Zygmund theory is needed -- just polynomial bounding of the convolution integral after moving derivatives onto f via IBP or direct differentiation.

### Impact analysis

If sorry 1 is false (it is not), then the velocity-space IBP for the Landau operator fails, breaking the symmetrized weak form of the entropy dissipation. The entire H-theorem chain collapses.

If sorry 2 is false (it is not), then the integrability of `fderiv(flux) * log(f)` is unproved. The IBP in Section 3 requires this integrability. Again the H-theorem chain fails.

**Worst case:** Both sorry'd statements are true. The only question is whether Lean/Mathlib can express the proofs with current infrastructure. The answer is yes, but at substantial cost.

### Dependency flow

```
coulomb_flux_differentiable (sorry)
  -> used by hLandauFluxDiff (field of VelocityDecayConditions)
  -> used by coulomb_ibp_df_g_integrable (measurability sub-proof)

coulomb_flux_deriv_schwartz_decay (sorry)
  -> used by coulomb_ibp_df_g_integrable
     -> used by hLandauIBP_df_g (field of VelocityDecayConditions)
```

These two sorry's account for 2 of 18 VelocityDecayConditions fields (hLandauFluxDiff and hLandauIBP_df_g). The remaining 16 fields are fully proved. **Completeness: 16/18 = 89%.**

---

## 2. VelocityDecayConditions: Typeclass Fields as Axioms

### Structure of the abstraction

The `VelocityDecayConditions` structure (Theorem42.lean:25-88) has 18 fields encoding integrability, differentiability, continuity, and Fubini conditions needed for the H-theorem chain. These are consumed by `Theorem42` as a single bundled hypothesis `hDecay`.

**The positive framing:** All 18 fields are explicitly instantiated in `CoulombConcreteTheorem42.lean:158-274`. Each field is filled with a call to a named lemma, and 16 of those lemma bodies are complete proofs. This is not a black box -- the user can inspect exactly what is assumed.

**The negative framing:** The structure is 64 lines of type signatures. A reader must verify that each field is not smuggling in a non-obvious consequence of the conclusion. Specifically:

### Field-by-field non-circularity audit

| Field | Status | Could it smuggle the conclusion? |
|-------|--------|----------------------------------|
| `hPSD_inner_int` | PROVED | No -- integrability of a bilinear form |
| `hPSD_outer_int` | PROVED | No -- iterated integrability |
| `hFubini_double` | PROVED | No -- joint integrability on product space |
| `hFubini_inner` | PROVED | No -- inner Fubini slice integrability |
| `hFubini_outer` | PROVED | No -- outer Fubini integrability |
| `hSpatialTransport_int` | PROVED | No -- transport term integrability |
| `hForceTransport_int` | PROVED | No -- force transport integrability |
| `hLandauFluxDiff` | **SORRY** | **Risk: differentiability of the flux is used in the IBP that leads to D(f)=0. But the statement itself (differentiability) does not imply D(f)=0 or the Maxwellian form.** |
| `hLandauIBP_df_g` | **SORRY** | Same as above -- integrability for IBP, not a conclusion-equivalent. |
| `hLandauIBP_f_dg` | PROVED | No |
| `hLandauIBP_fg` | PROVED | No |
| `hLandauFluxInt` | PROVED | No |
| `hForceIBP_f_dg` | PROVED | No |
| `hForceIBP_fg` | PROVED | No |
| `hSpatialTransport_joint` | PROVED | No |
| `hSpatTransComp` | PROVED | No |
| `hf_velocity_dominated` | PROVED | No |
| `hPSD_cont` | PROVED | **Note: this field asserts continuity of the PSD integrand for Coulomb. Proved via `psd_continuous_coulomb`, which is a genuine 170-line proof handling the cancellation at the diagonal. This is the hardest proved field.** |
| `hD_cont` | PROVED | No |

**Verdict on hidden axioms:** None of the 18 fields encodes a statement equivalent to or implying the conclusion (f = Maxwellian, E = 0, B = const). They are all analytical regularity conditions. The sorry'd fields are the weakest link, but their statements are differentiability and integrability claims, not structural claims about f.

### Satisfiability witness

`VelocityDecayInstance.lean` (2019 lines) provides a complete satisfiability witness: the uniform isotropic Maxwellian `f(x,v) = exp(a + c|v|^2)` with E = 0, B = 0. All 18 fields are proved for this distribution (with arbitrary continuous Psi). This demonstrates the hypotheses are non-vacuous.

**Weakness:** This witness is for the equilibrium itself. What the reviewer really wants is a non-equilibrium Schwartz-class f satisfying all 18 fields. The current sorry's block exactly this: if sorry's 1-2 were filled, then `CoulombConcreteTheorem42` would itself be that witness (any Schwartz f solving Vlasov would satisfy the conditions, and the theorem would prove it must be Maxwellian). So the satisfiability question reduces to the same sorry's.

---

## 3. Circularity Concerns

### Import dependency DAG

```
Defs.lean
  <- Section2.lean (Landau matrix properties)
  <- Section3.lean (H-theorem: IBP, Fubini, PSD=0 -> Maxwellian)
  <- Section4.lean (transport constraints)
  <- Section5.lean (polynomial matching)
  <- Section6.lean (bulk velocity zero)
  <- Section7.lean (Poisson-Boltzmann, density constant)
  <- Section8.lean (B constant)
  <- Section9.lean (conservation laws)
  <- VMLInputDerive.lean (VMLInput -> VMLSteadyState)
     <- Theorem42.lean (main theorem from VMLSteadyState)
        <- TorusInstance.lean (FlatTorus3 for Fin 3 -> AddCircle 1)
        <- VelocityDecayInstance.lean (satisfiability witness)
           <- ConcreteTheorem42.lean (Schwartz-hypotheses version)
              <- CoulombKernel.lean
                 <- NewtonianPotential.lean
                 <- CoulombSpatialTransport.lean
                 <- CoulombFlux.lean
                 <- CoulombPSD.lean [2 sorry's here]
                    <- CoulombConcreteTheorem42.lean (main theorem)
```

**No cycles.** The flow is strictly: definitions -> abstract algebra -> analysis -> abstract theorem -> concrete instance -> Coulomb specialization.

### Is any hypothesis restating the conclusion?

No. The 13 hypotheses of `CoulombConcreteTheorem42` are:
- Physical parameters (nu > 0, rho_ion > 0)
- Strict positivity of f
- Smoothness of f and B
- Schwartz decay
- Stretched-exponential lower bound
- Polynomial score bound
- Four VML equations

None of these says "f is Maxwellian" or "E = 0" or "B = const". The score bound (hypothesis 9) is the most restrictive, requiring `|df/dv_i| <= Cg * (1+||v||)^Kg * f`, but this is satisfied by any Maxwellian (Kg = 1), any stretched-Gaussian, and more generally any f whose logarithmic gradient grows at most polynomially. It does not force f to be Maxwellian.

### FlatTorus3: are the 23+ axioms consistent and non-trivially satisfiable?

The `FlatTorus3` typeclass (Defs.lean:325-417) has:
- 3 topological/measure instances
- 3 differential operators (gradX, divX, curlX)
- 17 property axioms

All 23 fields are instantiated for `Torus3 = Fin 3 -> AddCircle 1` in `TorusInstance.lean` with 0 sorry's. The `IsSpatiallyDiff` predicate is instantiated as `ContDiff R top (periodicLift f)` (smooth periodic lift). This is the strongest possible choice: it makes the preconditions of axioms like `hGradChainExp` and `hHarmonic_const` easy to satisfy but the axiom conclusions harder to prove. The instance was checked.

**Potential issue:** Some FlatTorus3 axioms are stated with `IsSpatiallyDiff` guards (e.g., `hGradChainExp` requires `IsSpatiallyDiff phi`). On the concrete torus, `IsSpatiallyDiff = ContDiff R top circ periodicLift`, which is smooth. In the abstract proof, the guard ensures the axiom is only used for smooth functions, which is correct. Without the guard, on the concrete torus, `fderiv` returns 0 for non-differentiable functions, making both sides of `hGradChainExp` trivially 0 -- the axiom would be vacuously true but useless. The design is sound.

**Potential issue:** `hSpatialVelocityFubini` requires joint integrability as a hypothesis. On the concrete torus, this is proved via `integral_integral_swap`. In the abstract theorem, this joint integrability must be provided by the caller (via `hSpatialTransport_joint` in VelocityDecayConditions). This is not circular; it is an honest integrability requirement.

---

## 4. Physical Limitations

### Dimension restriction

The formalization is hardcoded to dimension 3 (`Fin 3 -> R`). This appears in:
- `landauMatrix` is a `Matrix (Fin 3) (Fin 3) R`
- `cross` is defined for `Fin 3 -> R` only
- `FlatTorus3` is 3-dimensional
- All Schwartz decay bounds use `Fin 3 -> R`

The dimension 3 restriction is physically correct (VML is a 3D theory), but the formalizer could have parameterized by dimension n >= 3. The cross product is inherently 3D, so the Lorentz force `E + v x B` requires n = 3. This is an acceptable restriction.

### Kernel restriction

The theorem covers **only** the Coulomb kernel `Psi(r) = r^{-3}` (gamma = -3 in the Landau classification). It does not cover:

1. **Smooth kernels** (`Psi` continuous): Covered by the separate `ConcreteTheorem42` with `Continuous Psi` hypothesis, which has its own satisfiability proof in `VelocityDecayInstance.lean`. This is a complete, sorry-free result.

2. **Hard-sphere kernels** (gamma = 0, `Psi(r) = 1`): Trivially covered by the smooth-kernel theorem since `Psi = 1` is continuous.

3. **Moderately soft potentials** (-2 < gamma < 0): Not covered. The Landau matrix entries satisfy `|A(z)_{ij}| <= ||z||^{gamma+2}`, and for gamma > -3 the singularity is weaker than Coulomb. The proofs in CoulombPSD.lean use the specific Coulomb bound `||z||^{-1}` and would need to be generalized.

4. **Very soft potentials** (gamma < -3): Not physically relevant and not covered.

The Coulomb case is the physically most important case for plasma physics. The restriction is reasonable but should be stated explicitly.

### Spatial domain restriction

The domain is T^3 = (R/Z)^3 (flat 3-torus with period 1). The formalization does not cover:
- Bounded domains with physical boundary conditions (specular/diffuse reflection)
- The whole space R^3 (no spatial compactness)
- Non-flat manifolds (curved tori, spheres)

The periodic domain is standard in kinetic theory (it eliminates boundary terms). This is acceptable.

### Steady-state assumption

The theorem assumes f, E, B are time-independent. It says nothing about:
- Time-dependent convergence to equilibrium (which is the subject of the full Desvillettes-Villani program)
- Rate of convergence
- Stability of the equilibrium

This is a characterization theorem, not a stability result. The distinction is important and is correctly stated.

### Positivity assumption

`hf_pos : forall x v, 0 < f x v` requires f to be strictly positive everywhere. In reality, distribution functions can vanish (vacuum regions). This is a standard simplification: the strict positivity ensures `log f` is well-defined everywhere and avoids measure-theoretic complications at the zero set. Weakening to a.e. positivity would be a major undertaking.

---

## 5. Code Style

### Files over 600 lines

| File | Lines | Assessment |
|------|-------|------------|
| VelocityDecayInstance.lean | 2019 | **Too large.** Should be split into at least 3 files: uniform Maxwellian properties (~200 lines), core flux/PSD vanishing (~600 lines), the 18-field instantiation (~1200 lines). The file is hard to navigate. |
| Section3.lean | 1308 | **Too large.** Contains the entire H-theorem chain: Fubini symmetrization, score form, PSD=0 implies Maxwellian. Should be split into at least 2 files. |
| TorusInstance.lean | 1223 | Acceptable -- one file per typeclass instance is defensible, even if large. |
| CoulombPSD.lean | 793 | Acceptable. |
| Defs.lean | 782 | Acceptable for a definitions file. |
| CoulombSpatialTransport.lean | 662 | Borderline. |
| LandauMatrixDerivBound.lean | 648 | Contains machine-generated proofs. Borderline. |
| CoulombFlux.lean | 609 | Borderline. |

### High heartbeat settings

31 `maxHeartbeats` overrides across 11 files:

| Value | Count | Severity |
|-------|-------|----------|
| 4,000,000 (20x default) | 1 | VelocityDecayInstance.lean:1002. **Fragile.** |
| 3,200,000 (16x default) | 4 | NewtonianPotential, CoulombFlux, CoulombPSD. High. |
| 1,600,000 (8x default) | 10 | Spread across 6 files. Moderate. |
| 800,000 (4x default) | 14 | Widespread but acceptable. |

Additionally, `synthInstance.maxHeartbeats 160000` appears in CoulombSpatialTransport.lean (2x default), indicating slow typeclass resolution.

The 4M-heartbeat proof is a maintenance hazard. Any Lean or Mathlib version bump could break it. The 3.2M proofs are also fragile.

### Universal linter suppression

`set_option linter.all false` appears in all 21 files. This disables:
- `unusedVariables`: catches dead hypotheses
- `unreachableTactic`: catches no-op tactics after sorry
- `deprec`: catches deprecated API usage
- All other linters

This is a red flag for code quality. It is understandable during rapid development but should not persist in a final submission.

### Machine-generated proof style

Several proofs (primarily those attributed to "Aristotle (Harmonic)") are single-line semicolon chains. Example from Section3.lean:19-29:

```lean
vGrad_exp_quadratic ... := by
  unfold vGrad normSq;
  intro v; ext i; erw [ fderiv_exp ] ; norm_num [ dotProduct, Fin.sum_univ_three ] ; ring;
  ...
```

These are essentially opaque proof scripts. They work, but they:
1. Are unmaintainable -- any Mathlib API change breaks them silently
2. Cannot be understood by reading them
3. Contain nested `; <;>` chains that are hard to debug

### Duplicate "primed" definitions

`CoulombPSD.lean` and `CoulombFlux.lean` define:
- `normSq'`, `eucNorm'`, `coulombKernel'`, `innerLandauMatrix'`, `landauMatrix'`, `vGrad'`, `PSDIntegrand'`

These are definitionally equal to their unprimed counterparts (e.g., `PSDIntegrand'_eq_PSDIntegrand` is proved by `rfl`). They exist because Aristotle (the automated prover) generated standalone proofs using its own definitions, and the maintainer bridged them with `rfl` lemmas. This is namespace pollution and adds confusion about which definition is canonical.

---

## 6. Documentation Accuracy

### MEMORY.md discrepancies

| Claim in MEMORY.md | Reality | Status |
|----|---------|--------|
| "CoulombConcreteTheorem42.lean (201 lines)" | 280 lines | **STALE** |
| "main theorem, 6 sorry's" | 0 sorry's in-file (2 in CoulombPSD.lean) | **STALE** |
| "CoulombFlux.lean (441 lines)" | 609 lines | **STALE** |
| "CoulombPSD.lean (170 lines)" | 793 lines | **STALE** |
| "CoulombKernel.lean (114 lines)" | 114 lines | Correct |
| "CoulombSpatialTransport.lean (662 lines)" | 662 lines | Correct |
| "NewtonianPotential.lean (284 lines)" | 284 lines | Correct |
| "5 jobs FAILED (API ReadTimeout)" | Unknown current status | Potentially stale |

### CLAUDE.md accuracy

The instructions in `CLAUDE.md` say: "The goal is not to end up with 0 sorry's! The goal is to make an honest formalization of the main theorem, with only the genuinely needed mathematical/physical assumptions." This is accurately reflected in the codebase. The sorry's are in analytical lemmas, not in logical structure or hidden assumptions.

### Docstrings

The main theorem `CoulombConcreteTheorem42` has an accurate, detailed docstring (lines 34-52) that correctly describes the 13 hypotheses. The hypothesis numbering in the docstring matches the code. The claim about polynomial score bound (hypothesis 9) being "the same hypothesis used by the smooth kernel instance" is accurate -- `schwartzDecayConditions` in the smooth-kernel path also takes this bound.

### Physical correctness of docstrings

The file header comment (lines 1-23) correctly explains:
- The Coulomb kernel singularity
- Why `coulombKernel` is set to 1 at r <= 0
- The PSD cancellation mechanism (score difference = O(|v-w|) cancels r^{-3} singularity)
- The hypothesis count (13)

One minor inaccuracy: the comment says "13 total, down from 15 in ConcreteTheorem42" but `ConcreteTheorem42` requires `Continuous Psi` and polynomial growth of Psi, which are 2 extra kernel-regularity hypotheses. The Coulomb version replaces these with the concrete kernel, reducing the count. This is correct.

---

## 7. Overall Assessment

### Summary table

| Component | Status | Sorry's | Assessment |
|-----------|--------|---------|------------|
| Abstract proof chain (Sections 2-9) | Complete | 0 | Fully verified |
| Theorem42 (VMLInput -> conclusion) | Complete | 0 | Fully verified |
| VMLInputDerive (VMLInput -> VMLSteadyState) | Complete | 0 | Fully verified |
| FlatTorus3 typeclass (23 axioms) | Complete | 0 | Fully verified |
| TorusInstance (concrete torus) | Complete | 0 | Fully verified |
| VelocityDecayInstance (satisfiability) | Complete | 0 | Fully verified |
| ConcreteTheorem42 (smooth kernel) | Complete | 0 | Fully verified |
| CoulombKernel (kernel definition) | Complete | 0 | Fully verified |
| NewtonianPotential (||z||^{-1} integrability) | Complete | 0 | Fully verified |
| CoulombSpatialTransport | Complete | 0 | Fully verified |
| CoulombFlux | Complete | 0 | Fully verified |
| CoulombPSD (PSD continuity + integrability) | **Incomplete** | **2** | Two sorry's: flux differentiability, flux derivative Schwartz decay |
| CoulombConcreteTheorem42 (main theorem) | **Depends on above** | 0 in-file | Uses sorry'd lemmas from CoulombPSD |

### What is genuinely proved

1. **The entire abstract proof chain is complete.** Given the hypotheses of `Theorem42` (positivity, smoothness, integrability, Maxwell equations, VelocityDecayConditions), the conclusion (f = Maxwellian, E = 0, B = const) follows with 0 sorry's. This is the mathematical core of the result.

2. **The FlatTorus3 typeclass has a complete, sorry-free concrete instance.** All 23 axioms about differential operators on the 3-torus are proved from Mathlib primitives.

3. **16 of 18 VelocityDecayConditions fields are proved for Coulomb.** This includes the hardest analytical result: `psd_continuous_coulomb` (170 lines), which proves that the PSD integrand is jointly continuous despite the Coulomb singularity.

4. **The smooth-kernel theorem is fully complete.** `ConcreteTheorem42` with `Continuous Psi` has 0 sorry's anywhere in its dependency chain.

### What is not proved

1. Differentiability of the Coulomb flux (differentiation under the integral with singular kernel).
2. Schwartz decay of the Coulomb flux derivative.

Both are standard singular integral theory results. They are mathematically true and provable in Lean/Mathlib, but require substantial effort (~500-1000 lines total) due to the lack of ready-made Mathlib infrastructure for parametric singular integrals.

### Verdict: CONDITIONAL ACCEPT

The formalization is honest, mathematically correct in its claims, and nearly complete. The 2 remaining sorry's are:

- Clearly identified and isolated
- Mathematically true (standard results in singular integral theory)
- Not smuggling the conclusion
- Not hiding structural problems

The abstract proof chain is fully verified. The Coulomb specialization is 89% complete. The smooth-kernel theorem is 100% complete.

**Grounds for acceptance:**
1. The mathematical contribution (formalizing the VML steady-state theorem) is significant regardless of the 2 sorry's.
2. Both sorry'd statements are independently verifiable claims about singular-kernel regularity, not hand-wavy gaps.
3. The codebase demonstrates substantial analytical work (10,891 lines, 16 proved VelocityDecayConditions fields for Coulomb).
4. The clean separation between abstract proof and Coulomb instantiation means the abstract result stands on its own.

**Conditions for unconditional acceptance:**
1. Fill the 2 sorry's in CoulombPSD.lean.
2. Correct stale line counts and sorry counts in MEMORY.md.
3. (Minor) Re-enable linters in at least the top-level theorem files.
4. (Minor) Split VelocityDecayInstance.lean (2019 lines) into smaller files.
5. (Minor) Remove or consolidate primed duplicate definitions.

### Comparison with previous critique

| Metric | Previous | Current | Change |
|--------|----------|---------|--------|
| Sorry's in main theorem file | 3 | 0 | All moved to lemma file |
| Sorry's total | 5 (or 3, depending on counting) | 2 | Reduction |
| VelocityDecayConditions completeness | ~82% | 89% (16/18) | +7% |
| hFubini_double | SORRY | PROVED | Fixed |
| hLandauFluxDiff | SORRY | SORRY (moved to CoulombPSD) | Unchanged |
| hLandauIBP_df_g | SORRY | Body proved, depends on sorry | Improved |
| Total codebase | ~10,500 lines | 10,891 lines | +391 lines |

The formalization has continued to make progress. The remaining gaps are genuine technical challenges in singular integral theory formalization, not conceptual holes.
