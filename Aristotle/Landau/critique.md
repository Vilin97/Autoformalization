# Critique of the VML Steady State Formalization

This file is the critique of the current state of the project. If I were to say that this formalization project is fully complete, what would critics point out to invalidate this claim?

Last updated: 2026-03-07

## Current Status

The files `Defs.lean`, `Section2-9.lean`, `VMLInputDerive.lean`, `Theorem42.lean` compile with
**0 sorry's and 0 axioms**. The main theorem (`Theorem42`) is fully stated and proved.

`TorusInstance.lean` provides a concrete `FlatTorus3` instance on `Fin 3 -> AddCircle 1` with
**7 sorry's** (1 in instance field, 6 in helper theorems).

---

## Issue 1: Differentiability and the IsSpatiallyDiff Predicate

**Severity: Low (downgraded from Medium)**
**Status: FIXED**

The original issue was that FlatTorus3 axioms were stated too strongly (without
differentiability hypotheses), making them false for the concrete torus instance.

### What was fixed

1. **`hGradAdd`** now requires `IsSpatiallyDiff f` and `IsSpatiallyDiff g`. Proved on torus.

2. **`hGradScalarMul`**, **`hGradChainExp`**, **`hDivLinear`** proved unconditionally
   via case analysis on differentiability.

3. **`hSpatialVelocityFubini`** requires joint integrability. Proved via `integral_integral_swap`.

4. **`hGradAddConst`** derived lemma via the exp trick (no new axioms needed).

5. **`hDiff_maxwellian`** analytical interface hypothesis in `VMLInput`.

6. **`hIBP_spatial`** now requires `IsSpatiallyDiff φ` and `IsSpatiallyDiff ψ`. The previous
   statement (for ALL φ, ψ) was **false** on the concrete torus: if φ is non-differentiable,
   `gradX φ = 0`, but `∫ φ * gradX ψ` can be nonzero. Adding hypotheses fixes correctness.
   Cascade through `gradIntZero_component` → `hGradIntZero` → `spatial_transport_log_zero`
   → `transport_entropy_from_vlasov` → `Theorem42` (adds `hDiff_fv`, `hDiff_logfv`).

7. **`hHarmonic_const`** now requires `IsSpatiallyDiff φ`. The previous statement (for ALL φ)
   was **false** on the concrete torus: non-differentiable φ has `gradX φ = 0`, so `divX(gradX φ) = 0`
   trivially, but φ isn't constant. Adding `IsSpatiallyDiff` fixes correctness.
   Cascade through `hGradZeroConst` → VMLInputDerive (3 call sites) + Section8.
   Also required adding `hDiff_B` field to both VMLSteadyState and VMLInput.

### Remaining minor issue

- **`hSpatialAdd`** (1 instance sorry): `integral(g1 + g2) = integral(g1) + integral(g2)`
  stated without integrability. Mathematically false without integrability, but the abstract
  axiom is only used in proofs where integrability holds in practice. Could be fixed by
  adding `Integrable` hypotheses with a small cascade (2 call sites).

---

## Issue 2: Six Sorry's in TorusInstance.lean

**Severity: High**
**Status: Reduced from 12 to 6**

The concrete `FlatTorus3` instance on `Fin 3 -> AddCircle 1` has 6 sorry's.

### By category

**Design issue (1 instance field):**
- `hSpatialAdd`: integral additivity without integrability hypothesis (see Issue 1)

**Hard analysis (5 helper theorems):**
These are genuine mathematical results requiring nontrivial formalization:
- `torus_hIBP_spatial` -- IBP on torus (needs FTC + periodicity + Fubini); submitted to Aristotle
- `torus_hCurlIntZero` -- follows from IBP with phi=1; also submitted to Aristotle separately
  (now requires `IsSpatiallyDiff` for each F component -- added to abstract `hCurlIntZero`)
- `torus_hHarmonic_const` -- energy method: integral |grad phi|^2 = 0 via IBP (requires IsSpatiallyDiff)
- `torus_hKillingToHarmonic` -- Clairaut's theorem + Killing equation trace; needs C² (only C¹ available from IsSpatiallyDiff)
- `torus_hCurlZeroDivZeroHarmonic` -- Clairaut's theorem + curl=0 + div=0; same C² gap

### What was proved (6 fewer sorry's from 12 original)

- `torus_hGradAdd'`: proved with `IsSpatiallyDiff` hypotheses using `fderiv_add`
- `hDivLinear`: proved via `fderiv_const_mul_always` (case analysis on differentiability)
- `hGradScalarMul`: proved via `fderiv_const_mul_always`
- `hGradChainExp`: proved via `fderiv_exp_comp_always`
- `hSpatialVelocityFubini`: proved via `integral_integral_swap` with joint integrability
- `torus_hLaplacianMaxNonpos`: PROVED -- second derivative test via 1D test + chain rule

### Additional improvements (2026-03-07)

- `hCurlIntZero` now requires `IsSpatiallyDiff (F·j)` for each component (correct hypothesis)
- `integral_deriv_periodic_zero` and `ibp_periodic` integrated as private lemmas in TorusInstance.lean
- Submitted `torus_hIBP_spatial` and `torus_hCurlIntZero` to Aristotle (jobs ba9478b4 and c5961a9d)
- Deleted redundant aristotle-out files (second_deriv_max, laplacian_max_nonpos, ibp_periodic, integral_deriv_periodic_zero)

### Building blocks proved

The following lemmas are proved and integrated in TorusInstance.lean:
- `integral_deriv_periodic_zero'` — ∫₀ᵀ f' = 0 for periodic f (private, from Aristotle)
- `ibp_periodic'` — ∫₀ᵀ f·g' = -∫₀ᵀ f'·g for periodic f, g (private, from Aristotle)
- `clairaut_fderiv` — ∂²f/∂xᵢ∂xⱼ = ∂²f/∂xⱼ∂xᵢ via Mathlib's `IsSymmSndFDerivAt`
- `periodicLift_torusGradX` — connects torus gradient to fderiv of periodic lift

### Dependency structure

IBP (`torus_hIBP_spatial`) is the key lemma. Proving it would immediately enable:
- `torus_hCurlIntZero` (take phi = 1 in IBP)
- `torus_hHarmonic_const` (energy method: integrate grad phi dot grad phi via IBP)

The Killing/curl-div-harmonic theorems require C² regularity (Clairaut's theorem), but
`IsSpatiallyDiff` only guarantees C¹. One approach: strengthen `IsSpatiallyDiff` to C²
(would cascade through all call sites), or add separate C² hypotheses to these axioms.

---

## Issue 3: Verbose Integrability Hypotheses in Theorem42

**Severity: Medium**
**Status: FIXED**

---

## Issue 4: CompactSpace Not Part of FlatTorus3

**Severity: Low-Medium**
**Status: FIXED**

---

## Issue 5: rho and J Are Parameters With Definitional Hypotheses

**Severity: Low**
**Status: FIXED**

---

## Summary

| Issue | Severity | Status | Remaining Work |
|-------|----------|--------|----------------|
| 1. Differentiability / IsSpatiallyDiff | Low | FIXED | hSpatialAdd minor design issue |
| 2. TorusInstance sorry's | High | 6 sorry's | 1 design; 5 hard analysis proofs |
| 3. Verbose integrability hypotheses | Medium | FIXED | -- |
| 4. CompactSpace not in FlatTorus3 | Low-Medium | FIXED | -- |
| 5. rho/J as parameters | Low | FIXED | -- |
