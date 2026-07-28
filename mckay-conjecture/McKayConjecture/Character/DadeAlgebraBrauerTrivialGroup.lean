/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraBrauerDimensionCriterion

/-!
# Dade-algebra Brauer quotients for a trivial acting group

For a subsingleton group, every index of a pointed permutation basis
is globally fixed and there are no proper-subgroup traces.  The
fixed-index basis theorem therefore identifies the dimension of the
Brauer quotient with the dimension of the original algebra.

This is the basic obstruction to a general theorem asserting that
every Dade-algebra Brauer quotient is one-dimensional: central simple
algebras of dimension greater than one remain possible when the action
is trivial.  Consequently, one-dimensionality requires a genuine
primitivity or cap-multiplicity-one input.
-/

noncomputable section

namespace Representation
namespace DadeAlgebra

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P] [Subsingleton P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

noncomputable local instance : Fintype P :=
  Fintype.ofFinite P

/-- When the acting group is trivial, every basis index is globally
fixed. -/
def fixedIndexEquivIndexOfSubsingletonGroup
    (S : DadeAlgebra p k P A) :
    S.FixedIndex ≃ S.permutationBasis.index where
  toFun i := i
  invFun i :=
    ⟨i, fun g ↦ by
      change
        S.permutationBasis.indexAction g i = i
      rw [Subsingleton.elim g 1, map_one]
      rfl⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv _ := rfl

/-- For a trivial acting group, the Brauer quotient has the same
dimension as the original Dade algebra. -/
theorem finrank_brauerQuotientAlgebra_eq_finrank_of_subsingleton_group
    (S : DadeAlgebra p k P A) :
    Module.finrank k
        (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
      Module.finrank k A := by
  rw [S.finrank_brauerQuotientAlgebra_eq_natCard_fixedIndex]
  calc
    Nat.card S.FixedIndex =
        Nat.card S.permutationBasis.index :=
      Nat.card_congr S.fixedIndexEquivIndexOfSubsingletonGroup
    _ = Module.finrank k A := by
      letI : FiniteDimensional k A :=
        S.finiteDimensional
      letI : Finite S.permutationBasis.index :=
        Module.Finite.finite_basis S.permutationBasis.basis
      letI : Fintype S.permutationBasis.index :=
        Fintype.ofFinite S.permutationBasis.index
      simpa only [Nat.card_eq_fintype_card] using
        (Module.finrank_eq_card_basis
          S.permutationBasis.basis).symm

/-- For a trivial acting group, Brauer-primitivity is equivalent to
the original central simple algebra itself being one-dimensional. -/
theorem isBrauerPrimitive_iff_finrank_algebra_eq_one_of_subsingleton_group
    (S : DadeAlgebra p k P A) :
    S.IsBrauerPrimitive ↔
      Module.finrank k A = 1 := by
  rw [← S.finrank_brauerQuotientAlgebra_eq_finrank_of_subsingleton_group]
  exact
    S.finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive.symm

/-- Any higher-dimensional Dade algebra with a trivial group action
is a counterexample to automatic Brauer-primitivity. -/
theorem not_isBrauerPrimitive_of_subsingleton_group
    (S : DadeAlgebra p k P A)
    (hdim : Module.finrank k A ≠ 1) :
    ¬ S.IsBrauerPrimitive := by
  rw [
    S.isBrauerPrimitive_iff_finrank_algebra_eq_one_of_subsingleton_group]
  exact hdim

/-- Equivalently, a higher-dimensional Dade algebra with trivial
acting group does not have a one-dimensional Brauer quotient. -/
theorem finrank_brauerQuotientAlgebra_ne_one_of_subsingleton_group
    (S : DadeAlgebra p k P A)
    (hdim : Module.finrank k A ≠ 1) :
    Module.finrank k
        (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) ≠
      1 := by
  rw [S.finrank_brauerQuotientAlgebra_eq_finrank_of_subsingleton_group]
  exact hdim

end DadeAlgebra
end Representation
