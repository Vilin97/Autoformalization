# Critique of the VML Steady State Formalization

This file is the critique of the current state of the project. If I were to say that this formalization project is fully complete, what would critics point out to invalidate this claim?

Last updated: 2026-03-07

## Current Status

Main chain + TorusInstance: **0 sorry's and 0 axioms**.
VelocityDecayInstance: **3 sorry's** in `landau_flux_component_diff_with_bound` (Part 1 proved, Parts 2-4 remain).

- `Defs.lean`, `Section2-9.lean`, `VMLInputDerive.lean`, `Theorem42.lean`: abstract theorem proved
- `TorusInstance.lean`: concrete `FlatTorus3` instance on `Fin 3 -> AddCircle 1` fully verified
- `VelocityDecayInstance.lean`: `uniformMaxwellianDecay` (Maxwellian, 0 sorry's) + `schwartzDecayConditions` (Schwartz, 1 sorry)

---

## Issue 1: VelocityDecayConditions Schwartz Instance — Flux Differentiability (Minor)

**Severity: Minor (was Serious; reduced from 7 to 2 to 1 sorry)**
**Status: 1 sorry remaining — `landau_flux_component_diff_with_bound`**

The `VelocityDecayConditions` structure (Theorem42.lean:25-81) bundles **15 integrability/Fubini/IBP
conditions** that are assumed as a hypothesis of `Theorem42`.

**Resolution so far:**

1. `uniformMaxwellianDecay` (0 sorry's): Proves conditions for the uniform Maxwellian. **Circular**
   (the Maxwellian is the theorem's conclusion), but shows the hypothesis set is consistent.

2. `schwartzDecayConditions` (1 sorry): Proves conditions for **any** positive smooth function
   `φ` with Schwartz-like decay, C¹ bounded Ψ, gradient bound, and log bound.
   This construction is **not circular**: it applies to non-Maxwellians like `φ(v) = exp(-|v|⁴)`.

   - 14/15 conditions proved (5 transport + 9 collision)
   - `landau_flux_component_diff_with_bound` — a single helper lemma that provides:
     (1) flux integrand differentiable in v **(PROVED)**, (2) product-form derivative bound,
     (3) derivative integrable (AEStronglyMeasurable sorry), (4) flux integral derivative Schwartz bound
   - Part (1) uses `landauMatrix_entry_differentiable` (proved by Aristotle, job 648b5b5b)
   - Parts (2)-(4) submitted to Aristotle (jobs 31607b78, b8508ad1)

   Hypotheses added to unblock this:
   - `hΨ_diff : ContDiff ℝ 1 Ψ` (Ψ is C¹)
   - `hΨ'_bound : ∃ CΨ', ∀ r, |deriv Ψ r| ≤ CΨ'` (Ψ' bounded)
   - `hφ_deriv2_decay` (second derivative Schwartz decay)

   Both `hLandauFluxDiff` and `hLandauIBP_df_g` are fully proved modulo this one helper.
   Key infrastructure used: `differentiable_integral_of_product_dominated` (new),
   `measurable_fderiv_apply_const` (Mathlib)

---

## Issue 2: FlatTorus3 Typeclass Fields Function as Axioms (Moderate)

**Severity: Moderate**
**Status: By design (mitigated by concrete instance)**

The `FlatTorus3` typeclass has **21 fields** that function as axioms the moment you write
`[FlatTorus3 X]`. The "0 axioms" claim for `Theorem42` is technically correct (Lean reports
only `propext, Classical.choice, Quot.sound`) but epistemically misleading: the 21 typeclass
fields play exactly the same role as axioms in the abstract proof chain.

**Mitigating factor:** The concrete instance on `Fin 3 -> AddCircle 1` IS proved with 0 sorry's,
so the axiom system is at least consistent. But the abstract and concrete proofs are decoupled.

---

## Issue 3: Operator Axioms Hold via fderiv Junk Values (Moderate)

**Severity: Moderate**
**Status: By design**

On the concrete torus, `gradX` is defined via `fderiv`, which returns **0 for non-differentiable
inputs** (Lean's junk value). So for non-differentiable phi:
- `hGradScalarMul`: both sides are 0 (not actually verifying the chain rule)
- `hGradChainExp`: both sides are 0
- `hDivLinear`: both sides are 0

The abstract proof only applies these to `IsSpatiallyDiff` functions (= `ContDiff R top` on torus),
so junk cases never arise in practice. But a principled fix would either:
1. Restrict the axioms to `IsSpatiallyDiff` functions, or
2. Use distributional derivatives in the instance

---

## Issue 4: Coulomb Kernel Excluded by Hypotheses (Moderate)

**Severity: Moderate**
**Status: By design**

The physically most relevant collision kernel for Coulomb interactions has `Ψ(r) ~ 1/r³`,
which is singular at the origin: unbounded, discontinuous, and certainly not C¹. The
`schwartzDecayConditions` instance requires `Ψ` to be bounded, continuous, and C¹ with bounded
derivative — all three fail for the Coulomb kernel.

In practice, the Coulomb kernel is always **regularized** via Debye screening or a Coulomb
logarithm cutoff, yielding a bounded smooth `Ψ` that does satisfy our hypotheses. So the
formalization covers the regularized Landau equation (which is what is actually used in
plasma physics computations), but not the bare Coulomb case.

The `uniformMaxwellianDecay` instance (0 sorry's) only requires `∀ r, 0 < Ψ r` and does
not need boundedness, continuity, or differentiability of `Ψ`. So the abstract theorem
(`Theorem42`) itself is agnostic about `Ψ` regularity — the issue is only in the
non-circular Schwartz instance.

---

## Issue 5: Stale Documentation (Cosmetic)

**Severity: Cosmetic**
**Status: Mostly resolved**

- `Defs.lean:304` says "which is why those instance fields are sorry'd" -- all proved now
- Comment in Defs about Fubini "without explicit integrability hypothesis" is outdated

---

## Summary

| Issue | Severity | Status | Remaining Work |
|---|---|---|---|
| 1. Flux differentiability | **Minor** | Part 1 proved, 3 sorry's | Parts 2-4 of `landau_flux_component_diff_with_bound` |
| 2. FlatTorus3 fields = functional axioms | Moderate | By design | Mitigated by concrete instance |
| 3. Operator axioms via junk values | Moderate | By design | Restrict to IsSpatiallyDiff or use distributions |
| 4. Coulomb kernel excluded | Moderate | By design | Covers regularized Landau only |
| 5. Stale documentation | Cosmetic | Mostly resolved | Minor comment cleanup |

### Honest statement

The formalization proves: *for any abstract compact flat 3-torus domain satisfying 21 axioms, and
for any smooth steady-state (f, E, B) satisfying ~20 hypotheses + 15 velocity-decay conditions,
the conclusion holds.* The abstract proof chain is complete and correct. The concrete `FlatTorus3`
instance on `Fin 3 -> AddCircle 1` verifies all 21 axioms with 0 sorry's. Two concrete
`VelocityDecayConditions` instances are provided:

1. `uniformMaxwellianDecay` (0 sorry's): verifies conditions for the uniform Maxwellian.
   **Circular** but proves consistency.

2. `schwartzDecayConditions` (3 sorry's): verifies conditions for Schwartz-class φ with E=B=0.
   **Non-circular** — applies to genuinely non-Maxwellian distributions.
   14/15 conditions proved; 3 sorry's in `landau_flux_component_diff_with_bound` (Part 1 proved).
   Hypotheses now include `ContDiff ℝ 1 Ψ` + bounded derivative + pointwise second derivative bound.
   `hLandauFluxDiff` and `hLandauIBP_df_g` are fully reduced to this one helper lemma.

**Remaining work:** Prove Parts 2-4 of `landau_flux_component_diff_with_bound`:
- Part 1 (differentiability) is **proved** using `landauMatrix_entry_differentiable` (Aristotle).
- Part 2 (derivative bound) requires bounding D_v[A_{ij}(v-w)] ≤ C‖v-w‖ + product rule.
- Part 3 (integrability) requires AEStronglyMeasurable of fderiv + Part 2 bound.
- Part 4 (Schwartz bound on integral derivative) requires differentiation under integral sign.
- Submitted to Aristotle (jobs 31607b78, b8508ad1).
