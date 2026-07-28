/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerRelativeTrace
import Mathlib.Algebra.Algebra.Equiv

/-!
# Fixed algebras for group actions

Let a group `P` act on a `k`-algebra `A` by `k`-algebra
automorphisms.  This file packages the underlying linear representation
and its invariant submodule as the fixed subalgebra `Aᴾ`.

Keeping this identification explicit lets the linear relative trace API
feed into the multiplicative Brauer-quotient construction without
duplicating the coset calculation.
-/

noncomputable section

namespace Representation

variable {k P A : Type}
variable [CommRing k] [Group P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- The linear representation underlying an action by algebra
automorphisms. -/
def algebraActionRepresentation :
    Representation k P A :=
  DistribMulAction.toModuleEnd k A

@[simp]
theorem algebraActionRepresentation_apply
    (g : P) (a : A) :
    algebraActionRepresentation (k := k) (P := P) (A := A) g a =
      g • a :=
  rfl

/-- The subalgebra fixed pointwise by `P`. -/
def fixedSubalgebra : Subalgebra k A where
  carrier := {a | ∀ g : P, g • a = a}
  zero_mem' g := smul_zero g
  one_mem' g := smul_one g
  add_mem' ha hb g := by
    rw [smul_add, ha g, hb g]
  mul_mem' ha hb g := by
    rw [MulSemiringAction.smul_mul, ha g, hb g]
  algebraMap_mem' r g := smul_algebraMap g r

@[simp]
theorem mem_fixedSubalgebra
    (a : A) :
    a ∈ fixedSubalgebra (k := k) (P := P) (A := A) ↔
      ∀ g : P, g • a = a :=
  Iff.rfl

/-- The fixed subalgebra and the invariant submodule of the underlying
linear representation have the same carrier. -/
theorem fixedSubalgebra_toSubmodule :
    (fixedSubalgebra (k := k) (P := P) (A := A)).toSubmodule =
      invariants
        (algebraActionRepresentation (k := k) (P := P) (A := A)) :=
  rfl

/-- Identity-on-elements linear equivalence between the two fixed-point
packages. -/
def invariantsEquivFixedSubalgebra :
    invariants
        (algebraActionRepresentation (k := k) (P := P) (A := A)) ≃ₗ[k]
      fixedSubalgebra (k := k) (P := P) (A := A) :=
  LinearEquiv.ofEq _ _ fixedSubalgebra_toSubmodule.symm

@[simp]
theorem invariantsEquivFixedSubalgebra_apply
    (a :
      invariants
        (algebraActionRepresentation (k := k) (P := P) (A := A))) :
    ((invariantsEquivFixedSubalgebra
      (k := k) (P := P) (A := A) a :
        fixedSubalgebra (k := k) (P := P) (A := A)) : A) =
      a :=
  rfl

/-- A `P`-fixed element is fixed by every subgroup `Q ≤ P`. -/
def fixedSubalgebraRestriction
    (Q : Subgroup P) :
    fixedSubalgebra (k := k) (P := P) (A := A) →ₐ[k]
      fixedSubalgebra (k := k) (P := Q) (A := A) where
  toFun a := ⟨a, fun q ↦ a.property q⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem fixedSubalgebraRestriction_apply
    (Q : Subgroup P)
    (a : fixedSubalgebra (k := k) (P := P) (A := A)) :
    ((fixedSubalgebraRestriction
      (k := k) (P := P) (A := A) Q a :
        fixedSubalgebra (k := k) (P := Q) (A := A)) : A) =
      a :=
  rfl

end Representation
