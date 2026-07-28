/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismInteriorAction
import McKayConjecture.Character.TrivialAlgebraAction

/-!
# The trivial endomorphism interior action

The endomorphism algebra of a trivial linear action is an interior
algebra whose implementing-unit image is trivial.  Consequently every
endomorphism-algebra unit belongs to its interior normalizer.

This small construction is useful when an invariant subspace has first
been identified from a nontrivial ambient representation: the induced
action on the invariant subspace is genuinely trivial, and projective
operators on that subspace may therefore be placed in its interior
normalizer without an extra membership hypothesis.
-/

noncomputable section

namespace Representation

variable {k P V : Type}
variable [Field k] [Group P]
variable [AddCommGroup V] [Module k V]

/-- The trivial linear action, bundled by linear automorphisms. -/
def trivialLinearAction :
    P →* (V ≃ₗ[k] V) :=
  1

@[simp]
theorem trivialLinearAction_apply
    (g : P) :
    trivialLinearAction (k := k) (V := V) g = 1 :=
  rfl

/-- The interior action on an endomorphism algebra implemented by the
trivial linear action. -/
def trivialEndomorphismInteriorAction :
    letI :=
      endomorphismConjugationMulSemiringAction
        (trivialLinearAction (k := k) (P := P) (V := V))
    InteriorAction (P := P) (A := Module.End k V) := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (trivialLinearAction (k := k) (P := P) (V := V))
  exact
    interiorActionOfLinearAction
      (trivialLinearAction (k := k) (P := P) (V := V))

section Conjugation

local instance :
    MulSemiringAction P (Module.End k V) :=
  endomorphismConjugationMulSemiringAction
    (trivialLinearAction (k := k) (P := P) (V := V))

local instance :
    SMulCommClass P k (Module.End k V) :=
  endomorphismConjugation_smulCommClass
    (trivialLinearAction (k := k) (P := P) (V := V))

/-- Conjugation by the trivial linear action is pointwise the trivial
algebra action. -/
theorem isTrivialAlgebraAction_endomorphismConjugation_trivialLinearAction :
    IsTrivialAlgebraAction P (Module.End k V) := by
  intro g f
  rfl

/-- Every unit normalizes the implementing image of the trivial
endomorphism interior action. -/
theorem mem_trivialEndomorphismInteriorAction_unitNormalizer
    (u : (Module.End k V)ˣ) :
    u ∈
      (trivialEndomorphismInteriorAction
        (k := k) (P := P) (V := V)).unitNormalizer := by
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  rcases ht with ⟨g, rfl⟩
  change
    u *
        linearActionUnit
          (trivialLinearAction (k := k) (P := P) (V := V)) g =
      linearActionUnit
          (trivialLinearAction (k := k) (P := P) (V := V)) g *
        u
  have hunit :
      linearActionUnit
          (trivialLinearAction (k := k) (P := P) (V := V)) g =
        1 := by
    apply
      (LinearMap.GeneralLinearGroup.generalLinearEquiv
        k V).injective
    rw [generalLinearEquiv_linearActionUnit]
    simp
  rw [hunit, one_mul, mul_one]

end Conjugation

end Representation
