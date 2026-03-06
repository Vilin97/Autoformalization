# Critique of the VML Steady State Formalization

This file is the critique of the current state of the project. If I were to say that this formalization project is fully complete, what would critics point out to invalidate this claim?

Last updated: 2026-03-05

## Current Status

The files `Defs.lean`, `Section2-9.lean`, `VMLInputDerive.lean`, `Theorem42.lean` compile with
**0 sorry's and 0 axioms**. The main theorem (`Theorem42`) is fully stated and proved.

`TorusInstance.lean` provides a concrete `FlatTorus3` instance on `Fin 3 -> AddCircle 1` with
**7 sorry's** (1 in instance field, 6 in helper theorems).

---

## Issue 1: Differentiability and the IsSpatiallyDiff Predicate

**Severity: Medium (downgraded from Critical)**
**Status: MOSTLY FIXED**

The original issue was that 6 FlatTorus3 axioms were stated too strongly (without
differentiability hypotheses), making them false for the concrete torus instance.

### What was fixed

1. **`hGradAdd`** now requires `IsSpatiallyDiff f` and `IsSpatiallyDiff g`. On the concrete
   torus, `IsSpatiallyDiff = Differentiable R . periodicLift`, so `torus_hGradAdd'` is now
   **fully proved** (no sorry) using `fderiv_add`.

2. **`hGradScalarMul`**, **`hGradChainExp`**, **`hDivLinear`** were proved unconditionally
   on the concrete torus via case analysis on differentiability (the `fderiv` of a
   non-differentiable function is 0, and both sides evaluate to 0).

3. **`hSpatialVelocityFubini`** now requires joint integrability and is proved via
   `integral_integral_swap`.

4. **`hGradAddConst`** derived lemma: `gradX(f + c) = gradX(f)` proved from
   `hGradChainExp` + `hGradScalarMul` via the exp trick (no new axioms needed).

5. **`hDiff_maxwellian`** added as an analytical interface hypothesis in `VMLInput`:
   if `f = exp(a + b.v + c|v|^2)`, then `a`, `b_j`, `c` are `IsSpatiallyDiff`.
   This is mathematically true (smooth f implies smooth parameters) but not proved formally.

### Remaining issue

- **`hSpatialAdd`** (1 instance sorry): `integral(g1 + g2) = integral(g1) + integral(g2)`
  stated without integrability. On a compact space all continuous functions are integrable,
  but the abstract axiom doesn't require continuity. Adding integrability hypotheses would
  cascade through `hGradIntZero`.

---

## Issue 2: Seven Sorry's in TorusInstance.lean

**Severity: High**
**Status: Reduced from 12 to 7**

The concrete `FlatTorus3` instance on `Fin 3 -> AddCircle 1` has 7 sorry's.

### By category

**Remaining sorry (1 instance field):**
- `hSpatialAdd`: integral additivity without integrability hypothesis (see Issue 1)

**Correct but hard (6 helper theorems):**
These are genuine mathematical results requiring nontrivial formalization:
- `torus_hIBP_spatial` -- IBP on torus (needs FTC + periodicity + Fubini; unlocks 2 below)
- `torus_hCurlIntZero` -- follows from IBP with phi=1
- `torus_hHarmonic_const` -- energy method: integral |grad phi|^2 = 0 via IBP
- `torus_hLaplacianMaxNonpos` -- second derivative test (not in Mathlib)
- `torus_hKillingToHarmonic` -- Clairaut's theorem + Killing equation trace
- `torus_hCurlZeroDivZeroHarmonic` -- Clairaut's theorem + curl=0 + div=0

### What was proved (5 fewer sorry's)

- `torus_hGradAdd'`: now proved with `IsSpatiallyDiff` hypotheses (was sorry'd)
- `hDivLinear`: proved via `fderiv_const_mul_always` (case analysis on differentiability)
- `hGradScalarMul`: proved via `fderiv_const_mul_always`
- `hGradChainExp`: proved via `fderiv_exp_comp_always`
- `hSpatialVelocityFubini`: proved via `integral_integral_swap` with joint integrability

### Dependency structure

IBP (`torus_hIBP_spatial`) is the key lemma. Proving it would immediately enable:
- `torus_hCurlIntZero` (take phi = 1 in IBP)
- `torus_hHarmonic_const` (energy method: integrate grad phi dot grad phi via IBP)

The remaining 3 (Laplacian max, Killing, curl-div-harmonic) require Clairaut's theorem
(commutativity of mixed partials) and the 1D second derivative test, neither of which
are in Mathlib.

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
| 1. Differentiability / IsSpatiallyDiff | Medium | MOSTLY FIXED | 1 sorry (hSpatialAdd integrability) |
| 2. TorusInstance sorry's | High | 7 sorry's | 1 blocked by Issue 1; 6 need hard PDE proofs |
| 3. Verbose integrability hypotheses | Medium | FIXED | -- |
| 4. CompactSpace not in FlatTorus3 | Low-Medium | FIXED | -- |
| 5. rho/J as parameters | Low | FIXED | -- |
