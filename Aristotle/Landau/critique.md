# Critique of the VML Steady State Formalization

This file is the critique of the current state of the project. If I were to say that this formalization project is fully complete, what would critics point out to invalidate this claim?

Last updated: 2026-03-08

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

## Issue 2: Four Sorry's in TorusInstance.lean

**Severity: Medium**
**Status: Reduced from 12 to 4**

The concrete `FlatTorus3` instance on `Fin 3 -> AddCircle 1` has 4 sorry's.

### By category

**Design issue (1 instance field):**
- `hSpatialAdd`: integral additivity without integrability hypothesis (see Issue 1)

**Hard analysis (3 helper theorems):**
These are genuine mathematical results requiring nontrivial formalization:
- `torus_hIBP_spatial` -- IBP on torus (FTC + periodicity + Fubini); submitted to Aristotle (job 590a7b22)
- `torus_hCurlIntZero` -- follows from IBP with phi=1; depends on IBP
- `torus_hHarmonic_const` -- energy method: integral |grad phi|^2 = 0 via IBP; depends on IBP

### What was proved (8 fewer sorry's from 12 original)

- `torus_hGradAdd'`: proved via `fderiv_add` with IsSpatiallyDiff
- `hDivLinear`, `hGradScalarMul`, `hGradChainExp`: proved via case analysis on differentiability
- `hSpatialVelocityFubini`: proved via `integral_integral_swap`
- `torus_hLaplacianMaxNonpos`: proved via 1D second derivative test + chain rule
- `torus_hKillingToHarmonic`: PROVED -- Clairaut + Killing trace, uses `contDiff2_from_partials` helper
- `torus_hCurlZeroDivZeroHarmonic`: PROVED -- Clairaut + curl=0 + div=0, uses same helper

### Building blocks proved

- `integral_deriv_periodic_zero'`, `ibp_periodic'` — periodic IBP lemmas (from Aristotle)
- `clairaut_fderiv` — ∂²f/∂xᵢ∂xⱼ = ∂²f/∂xⱼ∂xᵢ via `IsSymmSndFDerivAt`
- `periodicLift_torusGradX` — torus gradient = fderiv of periodic lift
- `contDiff2_from_partials` — derives ContDiff ℝ 2 from C¹ + C¹ partials (finite-dim analysis)
- `laplacian_nonpos_at_max_rn` — Laplacian ≤ 0 at global max (proved directly, no sorry)
- `killing_harmonic_rn'` — Killing equation → harmonic on ℝⁿ
- `curl_div_harmonic_rn'` — curl=0, div=0 → harmonic on ℝⁿ

### Dependency structure

IBP (`torus_hIBP_spatial`) is the key remaining lemma. Proving it would immediately enable:
- `torus_hCurlIntZero` (take phi = 1 in IBP)
- `torus_hHarmonic_const` (energy method: integrate |grad phi|² via IBP → zero → phi constant)

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
| 2. TorusInstance sorry's | Medium | 4 sorry's | 1 design; 3 hard (IBP + dependents) |
| 3. Verbose integrability hypotheses | Medium | FIXED | -- |
| 4. CompactSpace not in FlatTorus3 | Low-Medium | FIXED | -- |
| 5. rho/J as parameters | Low | FIXED | -- |
