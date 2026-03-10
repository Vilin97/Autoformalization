# Formalization Progress: Global Steady State of the VML System

**Files**: `Aristotle/Landau/main/*.lean` (21 files, ~7,900 lines)
**Blueprint**: `Aristotle/Landau/H-theorem-formal.tex` (Sections 1--10)
**Status**: 0 errors, 0 sorry's. Fully verified by Lean 4 kernel.

Last updated: 2026-03-10

## Summary

The formalization proves Theorem 42 (= Theorem 12 in the blueprint):
any smooth steady state (f, E, B) of the Vlasov--Maxwell--Landau system
on T^3 x R^3 with Coulomb kernel and collision frequency nu > 0 must satisfy:

  (i)   f is a spatially uniform, zero-drift Maxwellian
  (ii)  E = 0
  (iii) B = const
  (iv)  T > 0

The main proof chain (Defs, Section2-8, VMLInputDerive, Theorem42) is
**complete with 0 sorry's and 0 axioms**.

A concrete FlatTorus3 instance on `Fin 3 -> AddCircle 1` (TorusInstance.lean)
validates the typeclass with **0 sorry's**.

The concrete theorem `CoulombConcreteTheorem42` (13 hypotheses) proves all 19
VelocityDecayConditions fields inline for the Coulomb kernel Ψ(r) = r⁻³.

---

## File Structure

- `Defs.lean` -- FlatTorus3 typeclass, structures, base definitions
- `Section2.lean` -- Algebraic lemmas (Landau matrix properties)
- `Section3.lean` -- H-theorem (Lemmas 4-9, Theorems 3-5)
- `Section3Helpers.lean` -- Helper lemmas for Section 3
- `Section4.lean` -- Transport constraints (Lemmas 10-12)
- `Section5.lean` -- Polynomial matching (Lemmas 13-17)
- `Section6.lean` -- Bulk velocity (Lemma 19)
- `Section7.lean` -- Maximum principle (Lemmas 20-21, Corollary 3)
- `Section8.lean` -- Magnetic field (Lemma 22)
- `VMLInputDerive.lean` -- VMLInput.toSteadyState, main_steady_state, main_from_physics
- `Theorem42.lean` -- Main abstract theorem + VelocityDecayConditions bundle (19 fields)
- `TorusInstance.lean` -- Concrete FlatTorus3 instance on T³
- `SchwartzDecayDefs.lean` -- UniformSchwartzDecay, integrability helpers
- `VelocityDecayInstance.lean` -- lorentz_component_bound
- `CoulombKernel.lean` -- Coulomb kernel def, Schwartz helpers
- `CoulombSpatialTransport.lean` -- Spatial/force transport for Coulomb
- `NewtonianPotential.lean` -- Matrix bounds, inv-norm integrability
- `CoulombFlux.lean` -- Flux integrability, flux×log, flux component bound
- `CoulombFluxDiff.lean` -- Conv differentiability, flux diff/decay, IBP
- `CoulombPSD.lean` -- PSD continuity, inner/outer integrability, Fubini
- `CoulombConcreteTheorem42.lean` -- Main concrete theorem (13 hypotheses, 0 sorry's)

---

## Architecture

The `FlatTorus3` typeclass extends `MeasureSpace X, TopologicalSpace X` and includes
`CompactSpace X` and `Nonempty X`. It bundles 3 spatial operators (gradX, divX, curlX),
an abstract differentiability predicate `IsSpatiallyDiff`, and 22 axiom fields.
All validated by the concrete Torus3 instance.

The proof flows through three layers:

1. **Theorem42** (user-facing): Takes physical + VelocityDecayConditions over `[FlatTorus3 X]`.
   Computes rho and J from f. Constructs VMLInput.

2. **VMLInput -> main_from_physics**: Physical hypotheses + analytical interface.
   Derives VMLSteadyState.

3. **VMLSteadyState -> main_steady_state** (algebraic core): All analytical work done.
   Proves u = 0, E = 0, B = const, T > 0.

---

## FlatTorus3 Axioms (22)

**Operator properties (5):** hDivLinear, hGradConst, hGradAdd, hGradScalarMul, hGradChainExp

**Closed manifold integration (2):** hCurlIntZero, hIBP_spatial

**Compact manifold analysis (4):** hHarmonic_const, hLaplacianMaxNonpos, hSpatialPos, hSpatialNonnegZero

**Flat geometry (2):** hKillingToHarmonic, hCurlZeroDivZeroHarmonic

**Abstract measure (3):** hSpatialVelocityFubini, hSpatialAdd, hGradIntegrable

**IsSpatiallyDiff closure (6):** hDiff_const, hDiff_add, hDiff_smul, hDiff_log, hDiff_continuous, hDiff_grad

---

## Theorem42 Hypotheses

**Physical** (10): f > 0, f smooth, f integrable, nu > 0, rho_ion > 0, Psi > 0,
Vlasov equation, Maxwell equations (3).

**Spatial regularity** (2): hDiff_fv (f(·,v) spatially differentiable), hDiff_B (B spatially differentiable).

**Velocity-space decay** (1 structure): `VelocityDecayConditions` bundles 19
integrability/Fubini/IBP/differentiability/continuity conditions.

**CoulombConcreteTheorem42** collapses all of the above to 13 explicit hypotheses
(FlatTorus3 fields from the Torus3 instance, all 19 VelocityDecayConditions proved inline).
