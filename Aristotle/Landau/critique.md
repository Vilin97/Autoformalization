# Critique of the VML Steady State Formalization

This file is the critique of the current state of the project. If I were to say that this        formalization project is fully complete, what would critics point out to invalidate this claim?

Last updated: 2026-03-05

## Current Status

The files `Defs.lean`, `Section2-9.lean`, `VMLInputDerive.lean`, `Theorem42.lean` compile with
**0 sorry's and 0 axioms**. The main theorem (`Theorem42`) is fully stated and proved.

`TorusInstance.lean` provides a concrete `FlatTorus3` instance on `Fin 3 -> AddCircle 1` with
**12 sorry's** (5 in instance fields, 7 in helper theorems).

---

## Issue 1: Six FlatTorus3 Axioms Are Literally False As Stated

**Severity: Critical**
**Status: Documented, not code-fixed (infeasible without major refactor)**

The `FlatTorus3` typeclass bundles 15 axioms about spatial operators. Six of these are stated
too strongly -- they omit necessary hypotheses and are therefore **false for the concrete torus
instance** (even though they are used correctly in the main proof).

### Missing differentiability hypotheses (4 axioms)

These axioms hold for differentiable functions but fail for arbitrary measurable functions,
because `fderiv` returns 0 when the function is not differentiable:

| Axiom | Statement | Missing Hypothesis |
|-------|-----------|-------------------|
| `hGradAdd` | `gradX(f+g) = gradX(f) + gradX(g)` | `Differentiable R f`, `Differentiable R g` |
| `hGradScalarMul` | `gradX(c*f) = c * gradX(f)` | `Differentiable R f` |
| `hGradChainExp` | `gradX(exp . phi) = exp(phi) * gradX(phi)` | `Differentiable R phi` |
| `hDivLinear` | `divX(a * G) = a * divX(G)` | `Differentiable R (fun x => G x i)` for each i |

**Counterexample**: If `f` is differentiable and `g` is not, then `fderiv(f+g) = 0` (not
differentiable), but `fderiv(f) + fderiv(g) = fderiv(f) + 0 = fderiv(f) != 0`.

### Missing integrability hypotheses (2 axioms)

| Axiom | Statement | Missing Hypothesis |
|-------|-----------|-------------------|
| `hSpatialAdd` | `integral(g1 + g2) = integral(g1) + integral(g2)` | `Integrable g1`, `Integrable g2` |
| `hSpatialVelocityFubini` | `integral_x integral_v F = integral_v integral_x F` | Joint integrability of `uncurry F` |

### Why this cannot be easily fixed

Adding differentiability hypotheses to the 4 gradient axioms requires a notion of
"spatially smooth function" on X. But X is only a `TopologicalSpace` + `MeasureSpace` --
it has no differentiable manifold structure. Options:

1. **Add `SmoothManifoldWithCorners` to FlatTorus3**: Major refactor, requires charts.
2. **Add abstract `IsSpatiallySmooth : (X -> R) -> Prop` predicate**: Adds ~8 new axioms
   (closure under add, scalar mul, exp, etc.) and cascades through all proofs.
3. **Current approach**: Document honestly, keep axioms universal for simplicity.

Adding `Integrable` to `hSpatialAdd` cascades to `hGradIntZero` (which needs integrability
of `gradX` outputs), requiring yet another axiom.

### Impact

- The main proof only applies these axioms to C-infinity / integrable functions, so the
  *proof* is mathematically correct.
- The *axiom statements* are overly strong, meaning the concrete instance must `sorry`
  5 fields (the 4 gradient axioms + hSpatialAdd; hSpatialVelocityFubini is separately sorry'd
  due to the abstract axiom omitting joint integrability).
- The FlatTorus3 docstring documents this design choice honestly.

---

## Issue 2: Twelve Sorry's in TorusInstance.lean

**Severity: High**
**Status: Reduced from 13 to 12 (proved torus_hSpatialVelocityFubini)**

The concrete `FlatTorus3` instance on `Fin 3 -> AddCircle 1` has 12 sorry's.

### By category

**False as stated (5 instance fields + 1 helper = 6):**
Cannot be proved because the abstract axioms lack hypotheses (see Issue 1).
- `hDivLinear`, `hGradScalarMul`, `hGradChainExp` (instance fields)
- `hSpatialAdd`, `hSpatialVelocityFubini` (instance fields)
- `torus_hGradAdd'` (helper theorem, same issue)

**Correct but hard (6 helper theorems):**
These are genuine mathematical results requiring nontrivial formalization:
- `torus_hIBP_spatial` -- IBP on torus (needs FTC + periodicity + Fubini; unlocks 2 below)
- `torus_hCurlIntZero` -- follows from IBP with phi=1
- `torus_hHarmonic_const` -- energy method: integral |grad phi|^2 = 0 via IBP
- `torus_hLaplacianMaxNonpos` -- second derivative test (not in Mathlib)
- `torus_hKillingToHarmonic` -- Clairaut's theorem + Killing equation trace
- `torus_hCurlZeroDivZeroHarmonic` -- Clairaut's theorem + curl=0 + div=0

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

All 15 integrability/decay conditions are now bundled into `VelocityDecayConditions`,
a structure in Theorem42.lean. The theorem takes a single `(hDecay : VelocityDecayConditions ...)`
instead of 15 separate hypotheses.

---

## Issue 4: CompactSpace Not Part of FlatTorus3

**Severity: Low-Medium**
**Status: FIXED**

`CompactSpace X` and `Nonempty X` are now fields of `FlatTorus3`, with instance registrations
so they're automatically available whenever `[FlatTorus3 X]` is in scope. Theorem42 no longer
takes `[CompactSpace X]` or `[Nonempty X]` separately.

---

## Issue 5: rho and J Are Parameters With Definitional Hypotheses

**Severity: Low**
**Status: FIXED**

rho and J are now computed from f via `set` in Theorem42:
```lean
set rho : X -> R := fun x => integral v, f x v with h_rho_def
set J : X -> (Fin 3 -> R) := fun x i => integral v, v i * f x v with hJ_def
```
They are no longer free parameters with definitional hypotheses.

---

## Summary

| Issue | Severity | Status | Remaining Work |
|-------|----------|--------|----------------|
| 1. False axioms (missing hypotheses) | Critical | Documented | Major refactor to fix (smoothness predicate) |
| 2. TorusInstance sorry's | High | 12 sorry's | 6 blocked by Issue 1; 6 need hard PDE proofs |
| 3. Verbose integrability hypotheses | Medium | FIXED | -- |
| 4. CompactSpace not in FlatTorus3 | Low-Medium | FIXED | -- |
| 5. rho/J as parameters | Low | FIXED | -- |
