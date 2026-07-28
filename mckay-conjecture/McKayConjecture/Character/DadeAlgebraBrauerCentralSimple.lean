/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerQuotientOpposite
import McKayConjecture.Character.DadeAlgebraBrauerLeftRight
import McKayConjecture.Character.DadeAlgebraBrauerQuotientBasis
import McKayConjecture.Character.EndomorphismCentralSimple
import McKayConjecture.Character.TensorProductSimpleFactor

/-!
# Brauer quotients of split Dade algebras are central simple

Let `A` be a Dade algebra over a finite field.  The preceding
left-right calculation and the opposite-quotient identification give

`A(P) ⊗[k] A(P)ᵐᵒᵖ ≃ₐ[k] Endₖ(A(P))`.

The right-hand side is central simple.  Centrality and simplicity
descend to the nonzero left tensor factor, so `A(P)` is itself
finite-dimensional central simple.  It is therefore Azumaya and,
over the finite field, a full matrix algebra.

This is the elementary content of Ladisch, Lemma 11.4(c).  The proof
does not require the acting `p`-group to be abelian.
-/

noncomputable section

open scoped TensorProduct

namespace Representation
namespace DadeAlgebra

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [Finite k] [CharP k p]
variable [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

omit [Finite k] in
/-- A Dade-algebra Brauer quotient is finite-dimensional. -/
theorem brauerQuotientAlgebra_finiteDimensional
    (S : DadeAlgebra p k P A) :
    FiniteDimensional k
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) := by
  letI : FiniteDimensional k A :=
    S.finiteDimensional
  letI : Finite S.permutationBasis.index :=
    Module.Finite.finite_basis S.permutationBasis.basis
  letI : Finite S.FixedIndex :=
    inferInstance
  exact Module.Finite.of_basis S.brauerQuotientFixedBasis

/-- The enveloping algebra of the Brauer quotient is canonically a
full endomorphism algebra. -/
def brauerEnvelopingAlgEquiv
    (S : DadeAlgebra p k P A) :
    let BQ :=
      BrauerQuotientAlgebra (k := k) (P := P) (A := A)
    BQ ⊗[k] BQᵐᵒᵖ ≃ₐ[k] Module.End k BQ := by
  let BQ :=
    BrauerQuotientAlgebra (k := k) (P := P) (A := A)
  exact
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : BQ ≃ₐ[k] BQ)
      (brauerQuotientOppositeAlgEquiv
        (k := k) (P := P) (A := A)).symm).trans
      S.brauerTensorOppositeEquivEndomorphism

/-- The Brauer quotient of a Dade algebra over a finite field is
central over that field. -/
theorem brauerQuotientAlgebra_isCentral
    (S : DadeAlgebra p k P A) :
    Algebra.IsCentral k
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) := by
  let BQ :=
    BrauerQuotientAlgebra (k := k) (P := P) (A := A)
  letI : Nontrivial BQ :=
    S.brauerQuotientAlgebra_nontrivial
  letI : FiniteDimensional k BQ :=
    S.brauerQuotientAlgebra_finiteDimensional
  letI : Algebra.IsCentral k (BQ ⊗[k] BQᵐᵒᵖ) :=
    Algebra.IsCentral.of_algEquiv k
      (Module.End k BQ) (BQ ⊗[k] BQᵐᵒᵖ)
      S.brauerEnvelopingAlgEquiv.symm
  exact
    Algebra.IsCentral.left_of_tensor_of_field
      k BQ BQᵐᵒᵖ

/-- The Brauer quotient of a Dade algebra over a finite field is
simple. -/
theorem brauerQuotientAlgebra_isSimpleRing
    (S : DadeAlgebra p k P A) :
    IsSimpleRing
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) := by
  let BQ :=
    BrauerQuotientAlgebra (k := k) (P := P) (A := A)
  letI : Nontrivial BQ :=
    S.brauerQuotientAlgebra_nontrivial
  letI : FiniteDimensional k BQ :=
    S.brauerQuotientAlgebra_finiteDimensional
  letI : IsSimpleRing (BQ ⊗[k] BQᵐᵒᵖ) :=
    IsSimpleRing.of_ringEquiv
      S.brauerEnvelopingAlgEquiv.symm.toRingEquiv
      (endomorphism_isSimpleRing (k := k) (V := BQ))
  exact
    isSimpleRing_left_of_tensorProduct k BQ BQᵐᵒᵖ

/-- The Brauer quotient of a Dade algebra over a finite field is
Azumaya. -/
theorem brauerQuotientAlgebra_isAzumaya
    (S : DadeAlgebra p k P A) :
    IsAzumaya k
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) := by
  let BQ :=
    BrauerQuotientAlgebra (k := k) (P := P) (A := A)
  letI : Nontrivial BQ :=
    S.brauerQuotientAlgebra_nontrivial
  letI : FiniteDimensional k BQ :=
    S.brauerQuotientAlgebra_finiteDimensional
  letI : Algebra.IsCentral k BQ :=
    S.brauerQuotientAlgebra_isCentral
  letI : IsSimpleRing BQ :=
    S.brauerQuotientAlgebra_isSimpleRing
  exact isAzumaya_of_finiteField k BQ

/-- Full-matrix-algebra form of the split-Dade Brauer quotient
theorem. -/
theorem exists_brauerQuotientAlgebra_algEquiv_matrix
    (S : DadeAlgebra p k P A) :
    ∃ (n : ℕ) (_ : NeZero n),
      Nonempty
        (BrauerQuotientAlgebra
            (k := k) (P := P) (A := A) ≃ₐ[k]
          Matrix (Fin n) (Fin n) k) := by
  let BQ :=
    BrauerQuotientAlgebra (k := k) (P := P) (A := A)
  letI : Nontrivial BQ :=
    S.brauerQuotientAlgebra_nontrivial
  letI : FiniteDimensional k BQ :=
    S.brauerQuotientAlgebra_finiteDimensional
  letI : Algebra.IsCentral k BQ :=
    S.brauerQuotientAlgebra_isCentral
  letI : IsSimpleRing BQ :=
    S.brauerQuotientAlgebra_isSimpleRing
  exact exists_algEquiv_matrix_of_finiteField k BQ

end DadeAlgebra
end Representation
