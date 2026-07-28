/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebra
import McKayConjecture.Character.PermutationAlgebraBrauerScalar

/-!
# Brauer quotient bases of Dade algebras

A `DadeAlgebra` carries finite-dimensionality as data rather than as a
global typeclass.  This file installs that data locally, derives
finiteness of the pointed permutation-basis index, and specializes the
permutation-algebra Brauer quotient basis without exposing either
object-dependent instance to callers.

If the distinguished unit index is the unique globally fixed basis
index, the Brauer quotient is one-dimensional and hence has the
canonical scalar identification used in the normalizer-extension
construction.
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

/-- The fixed basis-index type attached to the pointed permutation
basis of a Dade algebra. -/
abbrev FixedIndex
    (S : DadeAlgebra p k P A) :=
  S.permutationBasis.FixedIndex

/-- The Brauer quotient basis supplied by the pointed permutation
basis of a Dade algebra.  The finite-dimensional and finite-index
instances are installed only while constructing the basis. -/
def brauerQuotientFixedBasis
    (S : DadeAlgebra p k P A) :
    Module.Basis S.FixedIndex k
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) := by
  letI : FiniteDimensional k A :=
    S.finiteDimensional
  letI : Finite S.permutationBasis.index :=
    Module.Finite.finite_basis S.permutationBasis.basis
  exact
    S.permutationBasis.brauerQuotientAlgebraFixedBasis
      S.isPGroup

/-- Dimension of the Dade-algebra Brauer quotient, expressed without
requiring a caller-visible finiteness instance on the basis index. -/
theorem finrank_brauerQuotientAlgebra_eq_natCard_fixedIndex
    (S : DadeAlgebra p k P A) :
    Module.finrank k
        (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
      Nat.card S.FixedIndex := by
  letI : FiniteDimensional k A :=
    S.finiteDimensional
  letI : Finite S.permutationBasis.index :=
    Module.Finite.finite_basis S.permutationBasis.basis
  letI : Fintype S.FixedIndex :=
    Fintype.ofFinite S.FixedIndex
  rw [Module.finrank_eq_card_basis S.brauerQuotientFixedBasis]
  simp only [Nat.card_eq_fintype_card]

/-- If the unit is the unique fixed permutation-basis vector, the
Brauer quotient of a Dade algebra is one-dimensional. -/
theorem finrank_brauerQuotientAlgebra_eq_one
    (S : DadeAlgebra p k P A)
    [Subsingleton S.FixedIndex] :
    Module.finrank k
        (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
      1 := by
  letI : FiniteDimensional k A :=
    S.finiteDimensional
  letI : Finite S.permutationBasis.index :=
    Module.Finite.finite_basis S.permutationBasis.basis
  exact
    S.permutationBasis.finrank_brauerQuotientAlgebra_eq_one
      S.isPGroup

/-- Canonical scalar identification of a Dade-algebra Brauer quotient
whose unit is the unique fixed permutation-basis vector. -/
def brauerScalarIdentification
    (S : DadeAlgebra p k P A)
    [Subsingleton S.FixedIndex] :
    BrauerScalarIdentification (k := k) (P := P) (A := A) := by
  letI : FiniteDimensional k A :=
    S.finiteDimensional
  letI : Finite S.permutationBasis.index :=
    Module.Finite.finite_basis S.permutationBasis.basis
  exact brauerScalarIdentificationOfFinrankOne
    S.finrank_brauerQuotientAlgebra_eq_one

end DadeAlgebra
end Representation
