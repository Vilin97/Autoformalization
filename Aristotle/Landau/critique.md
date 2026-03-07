# Critique of the VML Steady State Formalization

This file is the critique of the current state of the project. If I were to say that this formalization project is fully complete, what would critics point out to invalidate this claim?

Last updated: 2026-03-10

## Current Status

ALL files compile with **0 sorry's and 0 axioms**.

- `Defs.lean`, `Section2-9.lean`, `VMLInputDerive.lean`, `Theorem42.lean`: abstract theorem proved
- `TorusInstance.lean`: concrete `FlatTorus3` instance on `Fin 3 -> AddCircle 1` fully verified
- `VelocityDecayInstance.lean`: concrete `VelocityDecayConditions` for uniform Maxwellian fully verified

---

## Issue 1: VelocityDecayConditions Never Instantiated (Serious)

**Severity: Serious**
**Status: RESOLVED (2026-03-10)**

The `VelocityDecayConditions` structure (Theorem42.lean:25-81) bundles **15 integrability/Fubini/IBP
conditions** that are assumed as a hypothesis of `Theorem42`.

**Resolution:** `VelocityDecayInstance.lean` constructs `uniformMaxwellianDecay` — a concrete
`VelocityDecayConditions` instance for `f(x,v) = exp(a + c|v|²)` with `c < 0`, `E = 0`, `B = 0`.
The key insight: for the spatially uniform Maxwellian, the Landau flux vanishes by projection
annihilation (`A(v-w) *ᵥ (v-w) = 0`), all spatial gradients vanish (f is constant in x), and
all force terms vanish (E = B = 0). Therefore every integrand is identically 0 and integrability
follows from `integrable_zero`. The file compiles with **0 sorry's**.

This demonstrates the hypothesis set is satisfiable: the equilibrium solution itself satisfies
all 15 velocity-decay conditions.

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

## Issue 4: Stale Documentation (Cosmetic)

**Severity: Cosmetic**
**Status: Open**

- `Defs.lean:304` says "which is why those instance fields are sorry'd" -- all proved now
- `progress.md:24` says "4 sorry's" -- contradicted by the 0 sorry's status
- Comment in Defs about Fubini "without explicit integrability hypothesis" is outdated

---

## Summary

| Issue | Severity | Status | Remaining Work |
|---|---|---|---|
| 1. VelocityDecayConditions unverified | **Serious** | **Resolved** | `uniformMaxwellianDecay` in VelocityDecayInstance.lean |
| 2. FlatTorus3 fields = functional axioms | Moderate | By design | Mitigated by concrete instance |
| 3. Operator axioms via junk values | Moderate | By design | Restrict to IsSpatiallyDiff or use distributions |
| 4. Stale documentation | Cosmetic | Open | Update comments |

### Honest statement

The formalization proves: *for any abstract compact flat 3-torus domain satisfying 21 axioms, and
for any smooth steady-state (f, E, B) satisfying ~20 hypotheses + 15 velocity-decay conditions,
the conclusion holds.* The abstract proof chain is complete and correct. The concrete `FlatTorus3`
instance on `Fin 3 -> AddCircle 1` verifies all 21 axioms with 0 sorry's. The concrete
`uniformMaxwellianDecay` instance verifies all 15 velocity-decay conditions with 0 sorry's,
showing the hypothesis set is satisfiable.

The remaining critiques are epistemic (Issues 2-3): the FlatTorus3 typeclass fields function as
axioms in the abstract proof, and the concrete torus instance relies on fderiv junk values for
non-differentiable inputs. These are by-design tradeoffs, not correctness issues.
