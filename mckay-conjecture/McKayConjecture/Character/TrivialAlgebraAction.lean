/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerFixedAlgebra

/-!
# Trivial actions on algebras

This file records the elementary fixed-point theory of a genuinely
trivial algebra action.  It provides both an explicit canonical
`MulSemiringAction` and a theorem applicable to any existing action
whose scalar operation is pointwise trivial.
-/

noncomputable section

namespace Representation

/-- The canonical trivial action of a monoid on a semiring.  This is
kept as an explicit definition, rather than a global instance, so that
it cannot compete with a nontrivial action in downstream files. -/
@[instance_reducible]
def trivialAlgebraMulSemiringAction
    (P A : Type) [Monoid P] [Semiring A] :
    MulSemiringAction P A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- Scalar multiplication commutes with the canonical trivial algebra
action. -/
theorem trivialAlgebraSMulCommClass
    (P k A : Type)
    [Monoid P] [Semiring k] [Semiring A] [Module k A] :
    letI : MulSemiringAction P A :=
      trivialAlgebraMulSemiringAction P A
    SMulCommClass P k A := by
  letI : MulSemiringAction P A :=
    trivialAlgebraMulSemiringAction P A
  exact ⟨fun _ _ _ ↦ rfl⟩

/-- An existing algebra action is pointwise trivial. -/
def IsTrivialAlgebraAction
    (P A : Type) [Monoid P] [Semiring A]
    [MulSemiringAction P A] : Prop :=
  ∀ g : P, ∀ a : A, g • a = a

@[simp]
theorem trivialAlgebraMulSemiringAction_smul
    (P A : Type) [Monoid P] [Semiring A]
    (g : P) (a : A) :
    letI : MulSemiringAction P A :=
      trivialAlgebraMulSemiringAction P A
    g • a = a :=
  rfl

theorem isTrivialAlgebraAction_trivial
    (P A : Type) [Monoid P] [Semiring A] :
    letI : MulSemiringAction P A :=
      trivialAlgebraMulSemiringAction P A
    IsTrivialAlgebraAction P A := by
  letI : MulSemiringAction P A :=
    trivialAlgebraMulSemiringAction P A
  exact fun _ _ ↦ rfl

variable {k P A : Type}
variable [CommRing k] [Group P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- Under a pointwise trivial action, the fixed subalgebra is the whole
algebra. -/
theorem fixedSubalgebra_eq_top_of_trivialAction
    (htriv : IsTrivialAlgebraAction P A) :
    fixedSubalgebra (k := k) (P := P) (A := A) = ⊤ := by
  exact eq_top_iff.2 (fun a _ g ↦ htriv g a)

/-- Identity-on-elements algebra equivalence from an algebra to the
fixed subalgebra of a pointwise trivial action. -/
def fixedSubalgebraAlgEquivOfTrivialAction
    (htriv : IsTrivialAlgebraAction P A) :
    A ≃ₐ[k] fixedSubalgebra (k := k) (P := P) (A := A) where
  toFun a := ⟨a, fun g ↦ htriv g a⟩
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem fixedSubalgebraAlgEquivOfTrivialAction_apply
    (htriv : IsTrivialAlgebraAction P A)
    (a : A) :
    ((fixedSubalgebraAlgEquivOfTrivialAction
        (k := k) (P := P) (A := A) htriv a :
      fixedSubalgebra (k := k) (P := P) (A := A)) : A) =
      a :=
  rfl

@[simp]
theorem fixedSubalgebraAlgEquivOfTrivialAction_symm_apply
    (htriv : IsTrivialAlgebraAction P A)
    (a : fixedSubalgebra (k := k) (P := P) (A := A)) :
    (fixedSubalgebraAlgEquivOfTrivialAction
      (k := k) (P := P) (A := A) htriv).symm a =
      (a : A) :=
  rfl

end Representation
