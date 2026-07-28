/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraBrauerQuotientBasis

/-!
# The dimension-one criterion for Dade-algebra Brauer quotients

A Dade algebra is only required to have a nonzero Brauer quotient.
One-dimensionality is an additional primitivity condition: the
distinguished unit index must be the only globally fixed index in the
chosen pointed permutation basis.

This file packages that condition without installing a
`Subsingleton` instance and proves that it is *equivalent* to the
Brauer quotient having dimension one.  Thus any theorem claiming
one-dimensionality for a particular Dade algebra must supply exactly
this extra input (usually through a cap or multiplicity-one theorem
from endopermutation-module theory).
-/

noncomputable section

namespace Representation
namespace DadeAlgebra

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [CharP k p]
variable [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- A Dade algebra is Brauer-primitive relative to its chosen pointed
permutation basis when every globally fixed basis index is the
distinguished unit index.

This is deliberately a proposition rather than a typeclass.  It is
the precise additional input needed for a scalar Brauer quotient. -/
def IsBrauerPrimitive
    (S : DadeAlgebra p k P A) : Prop :=
  ∀ i : S.FixedIndex,
    (i : S.permutationBasis.index) =
      S.permutationBasis.oneIndex

omit [Fact p.Prime] [CharP k p] [Fintype P]
  [SMulCommClass P k A] in
/-- Brauer-primitivity is equivalent to the fixed-index type being a
subsingleton. -/
theorem isBrauerPrimitive_iff_subsingleton_fixedIndex
    (S : DadeAlgebra p k P A) :
    S.IsBrauerPrimitive ↔
      Subsingleton S.FixedIndex := by
  constructor
  · intro h
    refine ⟨fun i j ↦ ?_⟩
    apply Subtype.ext
    exact (h i).trans (h j).symm
  · intro h i
    exact congrArg Subtype.val
      (h.elim i S.permutationBasis.oneFixedIndex)

/-- The Brauer quotient is one-dimensional exactly when the Dade
algebra is Brauer-primitive.  No `Subsingleton` assumption or instance
is hidden in this statement. -/
theorem finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive
    (S : DadeAlgebra p k P A) :
    Module.finrank k
        (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
      1 ↔
    S.IsBrauerPrimitive := by
  rw [S.finrank_brauerQuotientAlgebra_eq_natCard_fixedIndex]
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · rintro ⟨hsub, _⟩
    exact
      (S.isBrauerPrimitive_iff_subsingleton_fixedIndex).2
        hsub
  · intro hprimitive
    exact
      ⟨(S.isBrauerPrimitive_iff_subsingleton_fixedIndex).1
          hprimitive,
        ⟨S.permutationBasis.oneFixedIndex⟩⟩

/-- Instance-free fixed-index formulation of the dimension-one
criterion. -/
theorem finrank_brauerQuotientAlgebra_eq_one_iff_subsingleton_fixedIndex
    (S : DadeAlgebra p k P A) :
    Module.finrank k
        (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
      1 ↔
    Subsingleton S.FixedIndex := by
  rw [S.finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive]
  exact S.isBrauerPrimitive_iff_subsingleton_fixedIndex

end DadeAlgebra
end Representation
