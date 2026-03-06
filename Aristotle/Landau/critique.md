# Critique of the VML Steady State Formalization

Last updated: 2026-03-05

## Current Status

The files `Defs.lean`, `Section2-9.lean`, `VMLInputDerive.lean`, `Theorem42.lean` compile with
**0 sorry's and 0 axioms**. The main theorem (`Theorem42`) is fully stated and proved.

`TorusInstance.lean` provides a concrete `FlatTorus3` instance on `Fin 3 -> AddCircle 1` with
**13 sorry's** (5 in instance fields, 8 in helper theorems).

---

## Issue 1: Six FlatTorus3 Axioms Are Literally False As Stated

**Severity: Critical**

The `FlatTorus3` typeclass bundles 15 axioms about spatial operators. Six of these are stated
too strongly — they omit necessary hypotheses and are therefore **false for the concrete torus
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

Mathlib's `integral_add` requires integrability; without it, the Bochner integral can give
nonsensical results. Similarly, `integral_integral_swap` requires joint integrability.

### Impact

- The main proof only applies these axioms to C-infinity / integrable functions, so the
  *proof* is mathematically correct.
- But the *axiom statements* are wrong, meaning the `FlatTorus3` typeclass admits no
  honest instance — every concrete implementation must `sorry` these fields.
- A critic can say: "Your axioms are inconsistent with Mathlib's definitions."

### Fix

Add the missing hypotheses to each axiom, then update all call sites to provide them
(straightforward since the proof only uses these on smooth/integrable functions).

---

## Issue 2: Thirteen Sorry's in TorusInstance.lean

**Severity: High**

The concrete `FlatTorus3` instance on `Fin 3 -> AddCircle 1` has 13 sorry's. Without a
complete concrete instance, the 15 FlatTorus3 axioms could in principle be inconsistent.

### By difficulty tier

**Easy (provable once Issue 1 is fixed):**
- `hDivLinear` — fderiv linearity (becomes trivial with differentiability hypothesis)
- `hGradScalarMul` — `fderiv_const_mul` (becomes trivial with differentiability hypothesis)
- `hGradChainExp` — `HasFDerivAt.exp` + chain rule (becomes trivial with differentiability hypothesis)
- `hSpatialAdd` — `integral_add` (becomes trivial with integrability hypothesis)
- `torus_hGradAdd'` — `fderiv_add` (becomes trivial with differentiability hypothesis)

**Medium:**
- `hSpatialVelocityFubini` — Fubini with correct measure types + joint integrability

**Hard (genuine PDE/geometry):**
- `torus_hIBP_spatial` — IBP on the torus (core: fundamental theorem + periodicity + Fubini)
- `torus_hCurlIntZero` — Stokes theorem (depends on IBP)
- `torus_hHarmonic_const` — Harmonic functions on compact manifold are constant (energy method)
- `torus_hLaplacianMaxNonpos` — Second derivative test (Hessian trace argument)
- `torus_hKillingToHarmonic` — Killing vector fields have harmonic components (Clairaut + trace)
- `torus_hCurlZeroDivZeroHarmonic` — Irrotational + solenoidal implies harmonic (vector identity)

### Impact

Fixing Issue 1 immediately makes **5 of the 13 sorry's trivially provable**, reducing the
count to 8. The remaining 8 are genuine mathematical results that require nontrivial proofs.

---

## Issue 3: Verbose Integrability Hypotheses in Theorem42

**Severity: Medium**

Theorem42 has ~15 integrability/regularity hypotheses:

- `hPSD_inner_int`, `hPSD_outer_int` — PSD integrability
- `hFubini_double`, `hFubini_inner`, `hFubini_outer` — Fubini conditions
- `hSpatialTransport_int`, `hForceTransport_int` — transport integrability
- `hLandauFluxDiff` — Landau flux differentiability
- `hLandauIBP_df_g`, `hLandauIBP_f_dg`, `hLandauIBP_fg` — IBP component integrability
- `hLandauFluxInt` — Landau flux integrability
- `hForceIBP_f_dg`, `hForceIBP_fg` — force IBP integrability

In physics literature, a theorem says once: "assume f has sufficient velocity-space decay
(e.g., Schwartz class or sub-Gaussian tails)." Here, each integral is stated separately.

### Impact

- The theorem statement is correct and honest — it says exactly what's needed.
- But it's hard to read and parse for someone not familiar with the proof internals.
- A physicist would say: "This is 15 hypotheses that all say the same thing: f decays fast
  enough in velocity space."

### Fix

Bundle all integrability conditions into a single predicate:

```lean
def VelocityDecayConditions (Psi : R -> R) (f : X -> (Fin 3 -> R) -> R) (E B : X -> (Fin 3 -> R)) : Prop :=
  (forall x v, Integrable (PSDIntegrand Psi (f x) v)) /\
  (forall x, Integrable (fun v => integral w, PSDIntegrand Psi (f x) v w)) /\
  ... -- all 15 conditions
```

Then Theorem42 takes `(hDecay : VelocityDecayConditions Psi f E B)` instead of 15 separate hypotheses.

---

## Issue 4: CompactSpace Not Part of FlatTorus3

**Severity: Low-Medium**

Theorem42 separately requires `[CompactSpace X]`, but `FlatTorus3` doesn't extend it.
This means someone could instantiate `FlatTorus3` on a non-compact space, where axioms
like `hSpatialPos` (positive continuous function has positive integral) and
`hHarmonic_const` (harmonic functions are constant) would be false.

### Fix

Add `extends CompactSpace X` (or at minimum `[CompactSpace X]`) to the `FlatTorus3` class.
This is a one-line change. Since the concrete instance (`Fin 3 -> AddCircle 1`) already has
`CompactSpace` via `inferInstance`, no additional work is needed there.

---

## Issue 5: rho and J Are Parameters With Definitional Hypotheses

**Severity: Low**

Theorem42 takes `rho` and `J` as free parameters, then assumes:

```lean
(h_rho_def : forall x, rho x = integral v, f x v)
(hJ_def : forall x, J x = fun i => integral v, v i * f x v)
```

These are *definitions*, not hypotheses. A critic would say: "rho and J are determined by f;
they should be computed, not assumed."

### Fix

Option A: Make them `let` bindings in the theorem:

```lean
theorem Theorem42 ... (f : X -> (Fin 3 -> R) -> R) ... :=
  let rho := fun x => integral v, f x v
  let J := fun x i => integral v, v i * f x v
  ...
```

Option B: Make them fields of a `VMLState` structure that computes them from `f`.

This is a cosmetic improvement — mathematically nothing changes.

---

## Summary

| Issue | Severity | Effort | Impact |
|-------|----------|--------|--------|
| 1. False axioms (missing hypotheses) | Critical | Medium | Fixes axiom soundness + unblocks 5 sorry's |
| 2. TorusInstance sorry's | High | Hard (for remaining 8) | Validates axiom consistency |
| 3. Verbose integrability hypotheses | Medium | Low | Cleaner theorem statement |
| 4. CompactSpace not in FlatTorus3 | Low-Medium | Trivial | Prevents bad instantiation |
| 5. rho/J as parameters | Low | Low | Cleaner design |
