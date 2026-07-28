/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RepresentationTheory.Invariants

/-!
# Relative traces on invariant submodules

Let `Q ≤ P` and let `ρ` be a linear representation of the finite group
`P`.  The relative trace from `Q` to `P` sends a `Q`-fixed vector `v` to

`∑_{gQ ∈ P/Q} ρ(g) v`.

The sum is independent of the chosen representatives because `v` is
`Q`-fixed, and it is `P`-fixed because left multiplication permutes the
cosets.  We use `Quotient.out` only to make one representative choice;
the proofs below establish both required independence properties.

Relative traces are the linear-algebraic input used to define the Brauer
quotient of a modular representation and, later, a Dade `P`-algebra.
-/

noncomputable section

open scoped BigOperators

namespace Representation

variable {k P V : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [AddCommGroup V] [Module k V]

noncomputable local instance leftCosetFintype
    (Q : Subgroup P) :
    Fintype (P ⧸ Q) :=
  Fintype.ofFinite (P ⧸ Q)

/-- The unbundled relative trace value, formed using the representatives
chosen by `Quotient.out`. -/
def relativeTraceValue
    (rho : Representation k P V)
    (Q : Subgroup P)
    (x : invariants (rho.comp Q.subtype)) : V :=
  ∑ c : P ⧸ Q, rho c.out x

omit [Fintype P] in
/-- Changing the representative of a left coset does not change its
action on a `Q`-fixed vector.  This is the termwise identity used in the
proof that the relative trace is `P`-invariant. -/
theorem relativeTrace_out_smul
    (rho : Representation k P V)
    (Q : Subgroup P)
    (x : invariants (rho.comp Q.subtype))
    (g : P) (c : P ⧸ Q) :
    rho (g * c.out) x =
      rho (g • c).out x := by
  have hquotient :
      QuotientGroup.mk (s := Q) ((g • c).out) =
        QuotientGroup.mk (s := Q) (g * c.out : P) := by
    calc
      QuotientGroup.mk ((g • c).out) = g • c :=
        QuotientGroup.out_eq' (g • c)
      _ = QuotientGroup.mk (g * c.out : P) := by
        simpa only [smul_eq_mul] using
          (MulAction.Quotient.mk_smul_out Q g c).symm
  have hmem :
      (g • c).out⁻¹ * (g * c.out) ∈ Q :=
    QuotientGroup.leftRel_apply.mp
      (Quotient.exact' hquotient)
  let q : Q :=
    ⟨(g • c).out⁻¹ * (g * c.out), hmem⟩
  have hfactor :
      g * c.out = (g • c).out * (q : P) := by
    dsimp [q]
    simp
  calc
    rho (g * c.out) x =
        rho ((g • c).out * (q : P)) x := by
          rw [hfactor]
    _ = rho (g • c).out (rho (q : P) x) := by
          rw [map_mul]
          rfl
    _ = rho (g • c).out x := by
          have hxq :
              rho (q : P) (x : V) = x :=
            x.property q
          rw [hxq]

/-- The relative trace value is fixed by the whole group `P`. -/
theorem relativeTraceValue_mem_invariants
    (rho : Representation k P V)
    (Q : Subgroup P)
    (x : invariants (rho.comp Q.subtype)) :
    relativeTraceValue rho Q x ∈ invariants rho := by
  intro g
  rw [relativeTraceValue, map_sum]
  calc
    ∑ c : P ⧸ Q, rho g (rho c.out x) =
        ∑ c : P ⧸ Q, rho (g * c.out) x := by
          apply Fintype.sum_congr
          intro c
          rw [map_mul]
          rfl
    _ = ∑ c : P ⧸ Q, rho (g • c).out x := by
          apply Fintype.sum_congr
          intro c
          exact relativeTrace_out_smul rho Q x g c
    _ = ∑ c : P ⧸ Q, rho c.out x := by
          exact
            Function.Bijective.sum_comp
              (MulAction.toPerm g).bijective
              (fun c : P ⧸ Q ↦ rho c.out x)

/-- The relative trace as a linear map from `Q`-invariants to
`P`-invariants. -/
def relativeTrace
    (rho : Representation k P V)
    (Q : Subgroup P) :
    invariants (rho.comp Q.subtype) →ₗ[k] invariants rho where
  toFun x :=
    ⟨relativeTraceValue rho Q x,
      relativeTraceValue_mem_invariants rho Q x⟩
  map_add' x y := by
    apply Subtype.ext
    change
      relativeTraceValue rho Q (x + y) =
        relativeTraceValue rho Q x +
          relativeTraceValue rho Q y
    simp only [relativeTraceValue, Submodule.coe_add, map_add]
    change
      (∑ c : P ⧸ Q,
          (rho c.out x + rho c.out y)) =
        (∑ c : P ⧸ Q, rho c.out x) +
          ∑ c : P ⧸ Q, rho c.out y
    exact Finset.sum_add_distrib
  map_smul' a x := by
    apply Subtype.ext
    change
      relativeTraceValue rho Q (a • x) =
        a • relativeTraceValue rho Q x
    simp only [relativeTraceValue, Submodule.coe_smul_of_tower,
      map_smul]
    change
      (∑ c : P ⧸ Q, a • rho c.out x) =
        a • ∑ c : P ⧸ Q, rho c.out x
    symm
    exact Finset.smul_sum

@[simp]
theorem relativeTrace_apply_coe
    (rho : Representation k P V)
    (Q : Subgroup P)
    (x : invariants (rho.comp Q.subtype)) :
    ((relativeTrace rho Q x : invariants rho) : V) =
      ∑ c : P ⧸ Q, rho c.out x :=
  rfl

end Representation
