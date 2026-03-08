# Adversarial Critique of the VML Steady State Formalization

This file is an adversarial analysis: what would a determined critic attack to invalidate
claims of completeness? The formalization is mathematically correct (0 proof gaps), but has
meaningful epistemic and scope limitations.

Last updated: 2026-03-08 (session 5, adversarial rewrite)

## Current Status

| Component | Sorry's | Axioms | Notes |
|-----------|---------|--------|-------|
| Defs.lean | 0 | 0 | FlatTorus3 typeclass (22 property fields) + definitions |
| Section2-9.lean | 0 | 0 | Abstract proof chain (8 files, ~76 lemmas) |
| VMLInputDerive.lean | 0 | 0 | VMLInput -> VMLSteadyState derivation |
| Theorem42.lean | 0 | 0 | Main theorem statement + proof |
| TorusInstance.lean | 0 | 0 | Concrete FlatTorus3 on `Fin 3 -> AddCircle 1` |
| LandauMatrixDerivBound.lean | 0 | 0 | Quadratic matrix derivative bound (Aristotle) |
| VelocityDecayInstance.lean | 0 | 0 | Schwartz + uniform Maxwellian decay instances |

**Total: 0 sorry's, 0 axioms, 0 admits across 14 files.**

`lean_verify` on `VML.Theorem42` reports only `propext`, `Classical.choice`, `Quot.sound`.

---

## Issue 1: The Theorem Has ~54 Hypotheses, Not ~16 (Structural Dishonesty)

**Severity: HIGH (epistemic)**

The "clean" Theorem42 statement appears to have ~16 parameters. In reality:
- **14 explicit hypotheses** (hnu, hf_pos, hf_smooth, hVlasov, hAmpere, hGauss, hDivB, etc.)
- **17 VelocityDecayConditions fields** (bundled in `hDecay`)
- **23 FlatTorus3 typeclass fields** (implicit via `[FlatTorus3 X]`)

**Total: ~54 conditions.** The paper-style statement "any smooth steady state must be
Maxwellian" hides enormous technical baggage.

A critic would compare this to a theorem that says "under 54 assumptions, X holds" -- which
is much less impressive than it sounds. The hypotheses could be inconsistent for physically
relevant cases (see Issue 2), making the theorem vacuously true.

**Response:** This is standard mathematical practice -- "let M be a compact Riemannian
manifold" implicitly carries dozens of properties. The FlatTorus3 axioms are proved on a
concrete instance. The VelocityDecayConditions are proved satisfiable (with E=B=0). The
three-layer architecture (Theorem42 -> VMLInput -> VMLSteadyState) cleanly separates
physical hypotheses from technical conditions.

---

## Issue 2: VelocityDecayConditions May Be Vacuously Unsatisfiable with E, B != 0

**Severity: HIGH (mathematical substance) -- the single strongest adversarial argument**

The two concrete VelocityDecayConditions instances both use E = B = 0:

1. **uniformMaxwellianDecay**: f = Maxwellian, E=B=0. All integrands are identically 0.
   **Circular** (the Maxwellian is the theorem's conclusion).

2. **schwartzDecayConditions**: f = phi(v) spatially constant, E=B=0. **Not circular**
   (applies to non-Maxwellians like phi(v) = exp(-|v|^4)), but still field-free.

**No instance with nonzero electromagnetic fields exists.** This means:

- For the *physically interesting* case (plasma with electromagnetic fields), nobody has
  shown the 17 decay conditions can be simultaneously satisfied by any solution to the
  Vlasov equation.
- If the conditions are inconsistent with nonzero E, B (which hasn't been ruled out), the
  theorem is **vacuously true** for the interesting case.
- The Schwartz instance proves satisfiability for spatially-constant distributions with no
  fields -- a setting where the conclusion (f is Maxwellian) is already nearly obvious.

**What a critic would say:** "You've proved: IF these 17 conditions hold, THEN Maxwellian.
But you haven't shown the conditions CAN hold when it matters. The hard part of the physics
-- showing that a concrete PDE solution satisfies all these conditions -- is not addressed."

**Response:** The abstract theorem handles nonzero E, B correctly. The conditions involving
E and B (hForceTransport_int, hForceIBP_f_dg, hForceIBP_fg) are standard integrability
conditions that hold under reasonable decay. A future instance with nonzero E, B would
require more sophisticated arguments but is not fundamentally different. The Schwartz
instance with E=B=0 already demonstrates the technically hardest conditions (flux
differentiability, Fubini integrability).

---

## Issue 3: The Theorem Lives in an Abstract World Disconnected from PDEs

**Severity: MODERATE (scope)**

The Vlasov equation in Theorem42 is stated with abstract operators:
```
dotProduct v (FlatTorus3.gradX (fun y => f y v) x) +
dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
nu * LandauOperator Psi (f x) v
```

This uses `FlatTorus3.gradX` (abstract spatial gradient) and `vGrad` (fderiv-based velocity
gradient), not the actual PDE operators (partial derivatives on periodic domains).

To apply the theorem to a concrete PDE solution, one must:
1. Show the solution satisfies `hDiff_fv : forall v, IsSpatiallyDiff (fun x => f x v)`
   (= `ContDiff R top` of the periodic lift -- **much stronger** than what PDE existence
   theory typically provides)
2. Show the solution satisfies all 17 VelocityDecayConditions
3. Verify the abstract operators match the PDE operators (partially addressed by
   TorusInstance, but the user still needs their solution in the right function space)

The theorem is rigorously proved but only applies to solutions already known to be very
regular. The gap between "PDE solution exists" and "PDE solution satisfies Theorem42's
hypotheses" is itself a substantial analytical project.

---

## Issue 4: Coulomb Kernel Excluded by Hypotheses

**Severity: MODERATE (scope)**

The physically most important kernel (Coulomb: Psi(r) ~ 1/r^3) is singular at the origin --
unbounded, discontinuous, not C^1. The abstract Theorem42 requires `Continuous Psi` and
`forall r, 0 < Psi r`. The Schwartz instance additionally requires Psi to be C^1 with
bounded derivative. All three fail for bare Coulomb.

In practice, the Coulomb kernel is always **regularized** (Debye screening, Coulomb logarithm
cutoff), yielding bounded smooth Psi satisfying our hypotheses. So the formalization covers
the regularized Landau equation used in computational plasma physics, but not the bare
singular case used in foundational PDE theory.

---

## Issue 5: Three FlatTorus3 Axioms Hold via Junk Values

**Severity: MODERATE (epistemic)**

On the concrete torus, `gradX` is defined via `fderiv`, which returns **0 for non-differentiable
inputs** (Lean's junk value convention). Three operator axioms lack `IsSpatiallyDiff` guards:

- `hGradScalarMul : forall (c : R) (f : X -> R), forall x, gradX (c * f) x = c * gradX f x`
- `hGradChainExp : forall (phi : X -> R), forall x i, gradX (exp . phi) x i = exp(phi x) * gradX phi x i`
- `hDivLinear : forall (alpha : R) (G : X -> Fin 3 -> R), forall x, divX (alpha * G) x = alpha * divX G x`

For non-differentiable inputs, both sides collapse to 0 on the concrete torus (fderiv
returns 0), making the axiom vacuously true via junk values rather than genuine chain rule
reasoning.

The abstract proof only applies these to `IsSpatiallyDiff` functions (= `ContDiff R top` on
the torus), so junk cases never arise in practice. Note the inconsistency: `hGradAdd`
already requires `IsSpatiallyDiff f` and `IsSpatiallyDiff g` -- the three axioms above
should too, for honesty.

---

## Issue 6: hD_cont Is a Non-Obvious Hypothesis Hidden in VelocityDecayConditions

**Severity: MINOR (transparency)**

`hD_cont : Continuous (fun x => entropyDissipation Psi (f x))` says entropy dissipation is
continuous in x. This is used in the critical step going from "integral_X D(f) = 0 and
D(f) <= 0" to "D(f) = 0 everywhere" (via `hSpatialNonnegZero`).

This condition is NOT obviously derivable from the other hypotheses. It requires showing
that x -> integral_v Q(f(x,.)) . log f(x,.) is continuous -- a non-trivial result involving
the continuity of the Landau operator as a function of the spatial parameter. Bundling it
into VelocityDecayConditions obscures that it's an independent analytical requirement that
carries real mathematical content.

---

## Issue 7: VMLInput Analytical Interface Hypotheses

**Severity: MINOR (architecture)**
**Status: All discharged from proved lemmas**

The `VMLInput` structure contains **~14 analytical interface fields** beyond the physical
hypotheses. These are NOT assumed -- they are discharged in `Theorem42.lean` from proved
lemmas:

| Field | Discharged by | Status |
|-------|---------------|--------|
| hD_zero | H-theorem chain (Sections 3-4) | **Proved** |
| hScoreForm | entropy_score_form | **Proved** |
| hPSD_cont | PSDIntegrand_continuous | **Proved** |
| hPSD_inner/outer | VelocityDecayConditions bundle | Hypothesis |
| hDiff_maxwellian | maxwellian_params_isSpatiallyDiff | **Proved** |
| hPolynomialIdentity | polynomial_identity_from_vlasov | **Proved** |
| hJ_from_maxwellian | gaussian_first_moment | **Proved** |
| hPB_eq | poisson_boltzmann_from_vlasov | **Proved** |
| hNormalization | gaussian_normalization_maxwellian | **Proved** |
| x_max/x_min | Extreme value theorem on compact X | **Proved** |

The three-layer architecture (Theorem42 -> VMLInput -> VMLSteadyState) means the
mathematical content flows through two intermediate structures. A reviewer unfamiliar with
this pattern might struggle to trace which hypotheses are genuine vs. derived.

---

## Issue 8: Faraday's Law Is Not Assumed

**Severity: MINOR (looks odd)**

The four Maxwell equations at steady state are: curl B = J, div E = rho - rho_ion,
div B = 0, and **curl E = 0** (Faraday at steady state). Theorem42 only assumes the first
three. The fourth (curl E = 0) is never needed because the proof derives E = 0, which
implies curl E = 0 a fortiori.

This is actually a strength (fewer hypotheses), but a physicist reading the statement would
notice the omission and wonder if it's a bug. It's not -- the proof is correct without it.

---

## Issue 9: `set_option linter.all false` Everywhere

**Severity: MINOR (quality)**

Every file disables all Lean linters. This suppresses warnings about unused variables,
shadowed names, inefficient simp calls, and other quality checks. While correctness is
unaffected (Lean's kernel doesn't use linters), a Mathlib reviewer would reject this. The
codebase hasn't been polished to community standards.

---

## Issue 10: Performance Sensitivity

**Severity: COSMETIC (maintenance)**

Eight `set_option maxHeartbeats` declarations are needed across the codebase:

| File | Value | Context |
|------|-------|---------|
| Section3.lean (x3) | 800000 | Gaussian moments, Fubini symmetrization |
| LandauMatrixDerivBound.lean | 1600000 | Aristotle-generated proof |
| LandauMatrixDerivBound.lean | 800000 | Bound lemma |
| TorusInstance.lean | 800000 | Instance proof |
| VelocityDecayInstance.lean | 800000 | Flux zero proof |
| VelocityDecayInstance.lean | **4000000** | Schwartz decay conditions |

The 4M heartbeats for `schwartzDecayConditions` (20x the default) suggests the proof is
computationally expensive and potentially fragile under Mathlib updates.

---

## Issue 11: Stale Documentation

**Severity: COSMETIC (quality)**

- `Defs.lean:315`: Docstring says "Axioms (17)" but the actual count is 22 property fields
  (hDiff_continuous and hDiff_grad were added later)
- `progress.md`: Some counts are stale (e.g. "15" conditions vs actual 17 in
  VelocityDecayConditions)

---

## Summary

| # | Issue | Severity | Type |
|---|-------|----------|------|
| 1 | ~54 hidden hypotheses | HIGH | Epistemic |
| 2 | No VelocityDecayConditions with E,B!=0 | **HIGH** | Potential vacuity |
| 3 | Abstract operators, not concrete PDE | MODERATE | Scope |
| 4 | Coulomb kernel excluded | MODERATE | Scope |
| 5 | Junk value operator axioms | MODERATE | Epistemic |
| 6 | hD_cont is non-obvious | MINOR | Transparency |
| 7 | VMLInput interface hypotheses | MINOR | Architecture |
| 8 | Faraday's law omitted | MINOR | Looks odd |
| 9 | All linters disabled | MINOR | Quality |
| 10 | 4M heartbeats fragility | COSMETIC | Maintenance |
| 11 | Stale documentation | COSMETIC | Quality |

### Honest Statement

The formalization proves: *On any abstract compact flat 3-torus domain satisfying 23
typeclass fields, for any smooth steady-state (f, E, B) satisfying 14 explicit hypotheses
+ 17 velocity decay conditions (~54 total), f must be a spatially uniform Maxwellian with
zero drift, E must vanish, and B must be constant.*

The **entire proof chain is complete with 0 sorry's, 0 axioms, 0 admits** across 14 files.
`lean_verify` confirms only the standard three foundational axioms.

The concrete verification layer is also complete:
- **FlatTorus3 instance**: 0 sorry's, all 22 property fields proved on `Fin 3 -> AddCircle 1`
- **VelocityDecayConditions (Maxwellian)**: 0 sorry's, circular but consistent
- **VelocityDecayConditions (Schwartz)**: 0 sorry's, non-circular, all conditions proved

### Overall Assessment

The formalization is **correct**. Lean's kernel confirms it. There are no proof gaps.

The formalization is **conditional**. The real question is whether VelocityDecayConditions
can be satisfied for physically relevant solutions (nonzero E, B, non-constant f). Until an
instance with nonzero fields is constructed, the theorem is rigorously proved but potentially
vacuously true for the interesting case. **Issue #2 is the one a serious critic would hammer.**

The remaining issues (typeclass design, junk values, kernel scope, abstract-vs-PDE gap,
linter suppression) are architectural choices and scope limitations, not proof gaps. They
represent the normal trade-offs of a large formal verification project.
