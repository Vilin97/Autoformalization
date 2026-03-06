# Critique of the VML Steady State Formalization

This file is the critique of the current state of the project. If I were to say that this formalization project is fully complete, what would critics point out to invalidate this claim?

Last updated: 2026-03-08

## Current Status

The files `Defs.lean`, `Section2-9.lean`, `VMLInputDerive.lean`, `Theorem42.lean` compile with
**0 sorry's and 0 axioms**. The main theorem (`Theorem42`) is fully stated and proved.

`TorusInstance.lean` provides a concrete `FlatTorus3` instance on `Fin 3 -> AddCircle 1` with
**3 sorry's** (0 instance fields, 3 helper theorems).

---

## Issue 1: The Concrete Instance Is Unfinished (Critical / Showstopper)

**Severity: Critical**
**Status: Active — 3 Aristotle jobs submitted**

The "0 sorry's" claim applies only to the *abstract* theorem over any `[FlatTorus3 X]`. But
`FlatTorus3` has never been instantiated to a *fully verified* concrete domain. The only candidate
instance (`Fin 3 → AddCircle 1`) has three analytically crucial holes:

- `torus_hIBP_spatial` — integration by parts on the torus. **Not proved.**
  The entire proof chain rests on IBP: it is used in
  `hGradIntZero → transport_entropy_from_vlasov → hD_zero`, and in
  `hHarmonic_const → magnetic_field_constant`.
- `torus_hCurlIntZero` — integral of any curl component is zero. **Not proved.** Depends on IBP.
- `torus_hHarmonic_const` — harmonic functions are constant. **Not proved.** Depends on IBP.

Note: `hGradIntegrable` (instance field) is now **proved** via IsOpenQuotientMap.piMap.

Until these are filled, Theorem42 has never been applied to an actual physical setting.

### Active Aristotle submissions

- `torus_gradX_integral_zero` (standalone): job 51d9e2a0
- `torus_hIBP_spatial` + `torus_gradX_integral_zero`: job 4b7ec531 (torus_ibp_v2.lean)
- `torus_hCurlIntZero`: job 1be0761f (torus_curl_int_zero.lean)
- `torus_hHarmonic_const`: job be472543 (torus_harmonic_const_submission.lean)

### Dependency structure

IBP (`torus_hIBP_spatial`) is the key building block. Proving it would immediately enable:

- `torus_hCurlIntZero` (integral of curl = integral of partial derivatives = 0 by IBP with φ=1)
- `torus_hHarmonic_const` (energy method: ∫|∇φ|² = -∫ φΔφ via IBP → zero → φ constant)

---

## Issue 2: `hSpatialAdd` Is False as Stated (Serious)

**Severity: Serious**
**Status: FIXED (2026-03-08)**

```lean
-- Old (false):
hSpatialAdd : ∀ (g₁ g₂ : X → ℝ), ∫ x, (g₁ x + g₂ x) = (∫ x, g₁ x) + ∫ x, g₂ x
-- New (honest):
hSpatialAdd : ∀ (g₁ g₂ : X → ℝ), Integrable g₁ → Integrable g₂ →
  ∫ x, (g₁ x + g₂ x) = (∫ x, g₁ x) + ∫ x, g₂ x
```

Also added:
- `hGradIntegrable : ∀ g, IsSpatiallyDiff g → ∀ i, Integrable (fun x => gradX g x i)` to FlatTorus3
- `hSpatTransComp : ∀ v i, Integrable (fun x => gradX(f·v) x i * log(f x v))` to VelocityDecayConditions

In TorusInstance: `hSpatialAdd` is now proved by `integral_add` (no sorry). `hGradIntegrable` has
a sorry for "continuity of C¹ gradient on torus" which is mathematically true but requires
connecting the `choose`-based `torusGradX` to fderiv continuity.

---

## Issue 3: `IsSpatiallyDiff` Hypotheses Are Inputs, Not Derivations (Medium)

**Severity: Medium**
**Status: Partially addressed (2026-03-09)**

`Theorem42` originally required as *input hypotheses*:

- `hDiff_fv : ∀ v, IsSpatiallyDiff (fun x => f x v)` — f(·,v) is spatially C¹ for each v
- ~~`hDiff_logfv`~~ — **DERIVED** from `hDiff_fv + hf_pos + FlatTorus3.hDiff_log`
- ~~`hDiff_maxwellian`~~ — **DERIVED** via `maxwellian_params_isSpatiallyDiff`
- ~~`hDiff_logRho`~~ — **DERIVED** via `hDiff_velocityIntegral + hGradFv_dominated + hDiff_log`
- `hDiff_maxwellian_C2`: gradient components of b are spatially C¹ (C² for b)
- `hDiff_B`: each component of B is spatially C¹
- `hDiff_B_C2`: gradient components of B are spatially C¹ (C² for B)

### Progress

1. `hDiff_logfv` derived via `hDiff_log + hDiff_fv + hf_pos`.
2. `hDiff_maxwellian` derived via `maxwellian_params_isSpatiallyDiff` (evaluating log f at v=0, eⱼ, 2e₀).
3. `hDiff_logRho` derived (2026-03-09) via new `FlatTorus3.hDiff_velocityIntegral` axiom
   (differentiation under the velocity integral) + `VelocityDecayConditions.hGradFv_dominated`
   (integrable dominator for |∇ₓ f(x,v)|) + `hDiff_log` + `hρ_pos`.

### Progress (2026-03-09)

`hDiff_logRho` **eliminated**: now derived internally via:
- `FlatTorus3.hDiff_velocityIntegral` (new axiom: differentiation under the velocity integral)
- `VelocityDecayConditions.hGradFv_dominated` (new field: ∃ integrable bound for |∇ₓ f(x,v)|)
- `FlatTorus3.hDiff_log` + `hρ_pos`

The `hGradFv_dominated` condition is more transparent than `hDiff_logRho`: instead of asserting
a regularity *conclusion* (log ρ is C¹), it asserts a *physical input* (spatial gradients of f
are dominated by an integrable function of v), which holds for sub-Gaussian distributions.

### Remaining

- `hDiff_B`: B is spatially C¹. Natural regularity assumption for the magnetic field.
- `hDiff_B_C2`: B is C² in x. Required by `hCurlZeroDivZeroHarmonic` (Laplacian of each B_i
  component). Would require C² of B from Maxwell's equations (elliptic regularity).
- `hDiff_maxwellian_C2`: Maxwellian drift parameters b are C² in x. Required by
  `hKillingToHarmonic`. Would need `IsSpatiallyDiff` closed under gradients (C¹→C²).

The `IsSpatiallyDiff` predicate is opaque in the typeclass (4 closure properties: const,
add, scalar mul, log). There is no axiom saying it implies any actual regularity of f, so the
axioms gated on it could hold vacuously if `IsSpatiallyDiff ≡ ⊥`.

---

## Issue 4: `VelocityDecayConditions` Are Unverified for Any Concrete f (Medium)

**Severity: Medium**
**Status: Open**

The `VelocityDecayConditions` structure bundles **16 integrability/Fubini/IBP conditions**:
Landau flux differentiability (differentiation under the integral sign), per-component
integrability for velocity-space IBP, joint integrability for Fubini, etc.

These are all *assumed*. The docstring says they "hold for distributions with Schwartz-class or
sub-Gaussian tails" but this is not proved in Lean. No `VelocityDecayConditions` is ever
constructed for any concrete `f` anywhere in the formalization.

Without a concrete construction, a skeptic could claim the full hypothesis set of Theorem42 is
inconsistent — i.e., the theorem is vacuously true because no `(f, E, B)` satisfies all 24+
hypotheses simultaneously.

---

## Issue 5: The "0 Axioms" Claim Is Misleading About `FlatTorus3` (Moderate)

**Severity: Moderate**
**Status: By design**

The `FlatTorus3` typeclass has **15 typeclass fields that function as axioms** the moment you
write `[FlatTorus3 X]`. The fact that they're phrased as a typeclass rather than Lean `axiom`
declarations doesn't change their epistemic status: they are *assumed*, not proved. The only
thing distinguishing them from axioms is the existence of an instance — but that instance has 4
sorry's (Issues 1 and 2).

The comment in `Defs.lean` essentially acknowledges this for the operator axioms:

> "The fix is to use distributional derivatives in the instance, not to weaken the axioms."

But distributional derivatives aren't used in `TorusInstance.lean`. The instance uses `fderiv`,
which returns 0 for non-differentiable functions — a Lean-specific junk-value behavior that makes
some axioms ("true" for non-differentiable inputs) hold for a coincidental reason.

Specifically, `hGradScalarMul`, `hGradChainExp`, and `hDivLinear` are stated for **all**
`φ : X → ℝ`. On the concrete torus, for non-differentiable `φ`, `gradX φ x = 0` (fderiv junk),
so both sides of each equation are 0 — the chain rule isn't actually being verified, both sides
are just zero.

---

## Summary

| Issue | Severity | Status | Remaining Work |
|---|---|---|---|
| 1. Concrete instance unfinished (IBP + dependents) | Critical | 3 sorry's; 4 Aristotle jobs active | Await Aristotle; integrate proofs |
| 2. hSpatialAdd false without integrability | Serious | **Fixed** | hSpatialAdd + hGradIntegrable both proved (no sorry's in instance fields) |
| 3. IsSpatiallyDiff regularity not derived | Medium | Partial — hDiff_logfv, hDiff_maxwellian, hDiff_logRho all derived; hDiff_maxwellian_C2, hDiff_B, hDiff_B_C2 remain | hDiff_B_C2 needs C² for B; hDiff_maxwellian_C2 needs C² for b |
| 4. VelocityDecayConditions unverified for any f | Medium | Open | Construct for a concrete example |
| 5. FlatTorus3 fields are functional axioms | Moderate | By design | Use distributional derivatives |

### Honest statement

The formalization proves: *for any abstract compact flat 3-torus domain satisfying 21 axioms, and
for any smooth steady-state (f, E, B) satisfying ~20 hypotheses, the conclusion holds.* The
abstract proof chain is complete and correct. What remains is connecting this abstract result to
a concrete physical setting: verifying the 21 domain axioms for the standard 3-torus (4 sorry's
in TorusInstance) and verifying that actual smooth solutions to the VML equations satisfy the
assumed regularity and decay conditions (Issues 3 and 4).

**Last updated: 2026-03-09**
