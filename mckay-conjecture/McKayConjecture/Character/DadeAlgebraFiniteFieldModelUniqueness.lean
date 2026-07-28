/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraFiniteFieldModel
import McKayConjecture.Character.FiniteFieldEndomorphismActionUniqueness

/-!
# Uniqueness of the linear action in a finite-field Dade model

The action on a split Dade algebra over a finite field is implemented
by a unique honest linear action.  Existence is supplied by finite-field
projective linearization, while uniqueness follows because a finite
`p`-group has no nontrivial linear characters into the multiplicative
group of a field of characteristic `p`.
-/

noncomputable section

namespace Representation
namespace DadeAlgebra
namespace FiniteFieldModel

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [Finite k] [CharP k p]
variable [Group P] [Finite P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

noncomputable local instance : Fintype P :=
  Fintype.ofFinite P

/-- The transported algebra action of a finite-field Dade model has a
unique honest linear lift. -/
theorem existsUnique_linearAction
    (M : FiniteFieldModel k A)
    (S : DadeAlgebra p k P A) :
    ∃! rho : P →* (M.ModuleSpace ≃ₗ[k] M.ModuleSpace),
      ∀ g : P,
        M.transportedAlgebraAction g =
          (rho g).conjAlgEquiv k :=
  McKayConjecture.CharacterTriple.EndomorphismAction.existsUnique_linearAction_lift
    M.transportedAlgebraAction S.isPGroup

/-- Any honest linear lift of the transported algebra action is the
chosen lift used by the finite-field Dade model. -/
theorem linearAction_eq_liftedLinearAction
    (M : FiniteFieldModel k A)
    (S : DadeAlgebra p k P A)
    (rho : P →* (M.ModuleSpace ≃ₗ[k] M.ModuleSpace))
    (hrho :
      ∀ g : P,
        M.transportedAlgebraAction g =
          (rho g).conjAlgEquiv k) :
    rho = M.liftedLinearAction S.isPGroup := by
  apply Representation.linearAction_eq_of_conjAlgEquiv_eq
    S.isPGroup
  intro g
  exact
    (hrho g).symm.trans
      (M.transportedAlgebraAction_eq_conjAlgEquiv
        S.isPGroup g)

end FiniteFieldModel
end DadeAlgebra
end Representation
