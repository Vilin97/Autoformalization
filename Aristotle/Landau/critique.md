# Adversarial Critique of the VML Steady State Formalization

This file is an adversarial analysis: what would a determined critic attack to invalidate
claims of completeness? The formalization is mathematically correct (0 proof gaps), but has
meaningful epistemic and scope limitations.

Last updated: 2026-03-08 (session 7)

## Current Status

| Component | Sorry's | Axioms | Notes |
|-----------|---------|--------|-------|
| Defs.lean | 0 | 0 | FlatTorus3 typeclass (23 property fields) + definitions |
| Section2-9.lean | 0 | 0 | Abstract proof chain (8 files, ~76 lemmas) |
| VMLInputDerive.lean | 0 | 0 | VMLInput -> VMLSteadyState derivation |
| Theorem42.lean | 0 | 0 | Main theorem statement + proof |
| TorusInstance.lean | 0 | 0 | Concrete FlatTorus3 on `Fin 3 -> AddCircle 1` |
| LandauMatrixDerivBound.lean | 0 | 0 | Quadratic matrix derivative bound (Aristotle) |
| VelocityDecayInstance.lean | 0 | 0 | 3 instances: Maxwellian + Schwartz + Schwartz+EB |

**Total: 0 sorry's, 0 axioms, 0 admits across 14 files.**

`lean_verify` on `VML.Theorem42` reports only `propext`, `Classical.choice`, `Quot.sound`.
`lean_verify` on `VML.schwartzDecayConditionsEB` reports only `propext`, `Classical.choice`, `Quot.sound`.

---

## Issue 1: The Theorem Has ~55 Hypotheses, Not ~14 (Structural Dishonesty)

**Severity: HIGH (epistemic)**

The "clean" Theorem42 statement appears to have ~14 parameters. In reality:
- **14 explicit hypotheses** (hnu, hf_pos, hf_smooth, hVlasov, hAmpere, hGauss, hDivB, etc.)
- **18 VelocityDecayConditions fields** (bundled in `hDecay`)
- **23 FlatTorus3 typeclass fields** (implicit via `[FlatTorus3 X]`)

**Total: ~55 conditions.** The paper-style statement "any smooth steady state must be
Maxwellian" hides enormous technical baggage.

A critic would compare this to a theorem that says "under 55 assumptions, X holds" -- which
is much less impressive than it sounds. The hypotheses could be inconsistent for physically
relevant cases (see Issue 2), making the theorem vacuously true.

**Response:** This is standard mathematical practice -- "let M be a compact Riemannian
manifold" implicitly carries dozens of properties. The FlatTorus3 axioms are proved on a
concrete instance. The VelocityDecayConditions are proved satisfiable (with E=B=0, and
with constant E,B). The three-layer architecture (Theorem42 -> VMLInput -> VMLSteadyState)
cleanly separates physical hypotheses from technical conditions.

---

## Issue 2: VelocityDecayConditions Satisfiability with E, B != 0

**Severity: LOW (fully addressed)**

Three concrete VelocityDecayConditions instances exist, all with **0 sorry's**:

1. **uniformMaxwellianDecay**: f = Maxwellian, E=B=0. All integrands are identically 0.
   **Circular** (the Maxwellian is the theorem's conclusion), but demonstrates consistency.

2. **schwartzDecayConditions**: f = phi(v) spatially constant, E=B=0. **Not circular**
   (applies to non-Maxwellians like phi(v) = exp(-|v|^4)), but still field-free.

3. **schwartzDecayConditionsEB**: f = phi(v) spatially constant, E=E_0, B=B_0 (arbitrary
   constant fields). **Not circular, nonzero fields.** The 14 collision/spatial conditions
   are reused from schwartzDecayConditions. The 3 force conditions use the Lorentz bound
   |(E_0 + v x B_0)_i| <= CL*(1+||v||) combined with Schwartz decay. **All proved** (by
   Aristotle: force_transport_integrable, force_ibp_f_dg_integrable, force_ibp_fg_integrable).

**Status:** The hypothesis set IS satisfiable for nonzero E, B with **0 sorry's**.
`lean_verify` on `schwartzDecayConditionsEB` reports only `propext`, `Classical.choice`,
`Quot.sound`. Any Schwartz-class distribution with arbitrary constant electromagnetic
fields satisfies all 18 conditions.

**Remaining scope limitation:** The instances all use spatially-constant f. A fully
non-constant f(x,v) with nonzero E(x), B(x) satisfying the Vlasov equation would require
showing the PDE solution has sufficient decay -- a substantial analytical project beyond
the scope of this formalization.

**Additional restriction for Schwartz instances:** The `schwartzDecayConditions` and
`schwartzDecayConditionsEB` instances additionally require `ContDiff R 1 Psi` and bounded
Psi with bounded derivative (`exists C, forall r, |Psi r| <= C` and
`exists C', forall r, |deriv Psi r| <= C'`). These are stronger than the `Continuous Psi`
required by Theorem42 itself. The extra regularity is needed for the
`landau_flux_component_diff_with_bound` machinery (Leibniz integral rule). This does not
affect the abstract theorem, but it means the satisfiability instances only cover kernels
smoother than what the theorem abstractly allows.

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
2. Show the solution satisfies all 18 VelocityDecayConditions
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

## Issue 5: Junk Value Operator Axioms -- Partially Resolved

**Severity: LOW (epistemic, partially addressed)**

On the concrete torus, `gradX` is defined via `fderiv`, which returns **0 for non-differentiable
inputs** (Lean's junk value convention).

**Resolved:** `hGradChainExp` now requires `IsSpatiallyDiff phi`, matching `hGradAdd`'s design.
The chain rule `gradX(exp o phi) = exp(phi) * gradX(phi)` is a genuinely non-trivial fact that
should only hold for differentiable phi. All call sites (Section5, Section7, derived lemmas
hGradChainLog and hGradAddConst) now provide the IsSpatiallyDiff proof.

**Remaining (by design):** `hGradScalarMul` and `hDivLinear` remain unguarded. This is
intentional: linearity of `fderiv` genuinely holds for ALL functions (`fderiv(c*f) = c*fderiv(f)`
is true even for non-differentiable f, since both sides are 0 by Lean's `fderiv` definition).
These are not "junk value coincidences" but genuine properties of the fderiv API.

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

## Issue 11: Stale Comments and Documentation

**Severity: COSMETIC (mostly resolved)**

- **(Fixed)** VelocityDecayInstance.lean header: updated "15" to "18" conditions.
- **(Fixed)** TorusInstance.lean: removed stale "sorry" comments (lines 237, 285, 923, 991).
- **(Fixed)** LandauMatrixDerivBound.lean: removed Aristotle's internal "sorry" comments.
- `Defs.lean:324`: Derived lemmas list says "hGradChainLog, hGradIntZero, hLaplacianMinNonneg,
  hSpatialMul" but does not mention hGradAddConst and hDiff_sub, which are also derived.

---

## Issue 12: B_mean_conserved Takes Leibniz Rule as a Parameter

**Severity: MINOR (epistemic)**

Section9.lean's `B_mean_conserved` theorem takes a Leibniz rule as an explicit parameter:
```
(hLeibniz : forall (g : R -> X -> R) (t : R),
  deriv (fun t' => spatialIntegral (fun x => g t' x)) t =
  spatialIntegral (fun x => deriv (fun t' => g t' x) t))
```

This is an interchange of differentiation and integration that requires justification
(dominated convergence or similar). While the theorem is not used in the main proof chain
(the steady-state result does not invoke B_mean_conserved), a critic would note that it is
effectively assuming a mathematical result rather than proving it.

**Status:** Not a gap in Theorem42 itself, since `B_mean_conserved` is a standalone lemma
about time-dependent dynamics, not part of the steady-state proof chain.

---

## Issue 13: IsSpatiallyDiff Means Smooth, Not Just Differentiable

**Severity: MINOR (naming)**

On the concrete torus instance, `IsSpatiallyDiff f` is defined as
`ContDiff R top (periodicLift f)`, meaning the periodic lift is **smooth** (C^infinity),
not merely differentiable or C^1. The name `IsSpatiallyDiff` (suggesting "differentiable")
understates the actual requirement.

This has real consequences: the abstract FlatTorus3 typeclass has `hDiff_grad` which says
that if `IsSpatiallyDiff f`, then `IsSpatiallyDiff (fun x => gradX f x i)`. This is true
for smooth functions (taking the gradient preserves smoothness) but false for merely
differentiable functions (the gradient of a C^1 function need not be C^1). The `ContDiff R top`
definition is therefore necessary, not merely convenient.

A more honest name would be `IsSpatiallySmooth`, but renaming would require changes across
all 14 files.

---

## Summary

| # | Issue | Severity | Type |
|---|-------|----------|------|
| 1 | ~55 hidden hypotheses | HIGH | Epistemic |
| 2 | VelocityDecayConditions with E,B!=0 | LOW | Fully resolved |
| 3 | Abstract operators, not concrete PDE | MODERATE | Scope |
| 4 | Coulomb kernel excluded | MODERATE | Scope |
| 5 | Junk value axioms (hGradChainExp fixed) | LOW | Partially resolved |
| 6 | hD_cont is non-obvious | MINOR | Transparency |
| 7 | VMLInput interface hypotheses | MINOR | Architecture |
| 8 | Faraday's law omitted | MINOR | Looks odd |
| 9 | All linters disabled | MINOR | Quality |
| 10 | 4M heartbeats fragility | COSMETIC | Maintenance |
| 11 | Stale comments (mostly fixed, one remaining in Defs.lean) | COSMETIC | Mostly resolved |
| 12 | B_mean_conserved Leibniz parameter | MINOR | Epistemic |
| 13 | IsSpatiallyDiff means smooth, not diff | MINOR | Naming |

### Honest Statement

The formalization proves: *On any abstract compact flat 3-torus domain satisfying 23
typeclass fields, for any smooth steady-state (f, E, B) satisfying 14 explicit hypotheses
+ 18 velocity decay conditions (~55 total), f must be a spatially uniform Maxwellian with
zero drift, E must vanish, and B must be constant.*

**The entire formalization has 0 sorry's, 0 axioms, 0 admits** across all 14 files.
`lean_verify` confirms only the standard three foundational axioms.

The concrete verification layer:

- **FlatTorus3 instance**: 0 sorry's, all 23 property fields proved on `Fin 3 -> AddCircle 1`
- **VelocityDecayConditions (Maxwellian)**: 0 sorry's, circular but consistent
- **VelocityDecayConditions (Schwartz, E=B=0)**: 0 sorry's, non-circular, all conditions proved
- **VelocityDecayConditions (Schwartz, E=E_0, B=B_0)**: 0 sorry's, non-circular, nonzero fields.
  All 18 fields proved: 14 reused from E=B=0 instance, 3 force conditions proved by Aristotle,
  plus hf_velocity_dominated (trivially uniform in x for spatially-constant f).

### Overall Assessment

The formalization is **correct**. Lean's kernel confirms it. All proof chains have no gaps.

The formalization is **conditional** but **not vacuously so**: `schwartzDecayConditionsEB`
demonstrates satisfiability of VelocityDecayConditions for arbitrary constant E_0, B_0 with
any Schwartz-class distribution, with **0 sorry's**. This fully addresses the previously
strongest criticism (Issue #2).

The remaining issues (typeclass design, kernel scope, abstract-vs-PDE gap, linter
suppression) are architectural choices and scope limitations, not proof gaps. They
represent the normal trade-offs of a large formal verification project.
