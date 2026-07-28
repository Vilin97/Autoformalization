/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerQuotientOpposite
import McKayConjecture.Character.DadeAlgebraBrauerDimensionCriterion
import McKayConjecture.Character.DadeAlgebraBrauerTensorProduct
import McKayConjecture.Character.FiniteFieldDadeTensorProduct

/-!
# Brauer-primitivity under Dade-algebra operations

Brauer quotients commute with opposites and with tensor products of
pointed permutation algebras.  Consequently Brauer-primitivity is
preserved by opposites, while a tensor product is Brauer-primitive
exactly when both factors are.

The tensor-product statement is made over a finite field because that
is the setting in which the tensor product has already been packaged
as a Dade algebra.
-/

noncomputable section

open scoped TensorProduct

namespace Representation
namespace DadeAlgebra

variable {p : ℕ} [Fact p.Prime]
variable {k P A D : Type}
variable [Field k] [CharP k p]
variable [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [Ring D] [Algebra k D]
variable [MulSemiringAction P A] [SMulCommClass P k A]
variable [MulSemiringAction P D] [SMulCommClass P k D]

omit [Fact p.Prime] [CharP k p] [Fintype P]
    [SMulCommClass P k A] in
/-- Passage to the opposite algebra preserves the chosen
Brauer-primitivity condition. -/
@[simp]
theorem opposite_isBrauerPrimitive_iff
    (S : DadeAlgebra p k P A) :
    S.opposite.IsBrauerPrimitive ↔ S.IsBrauerPrimitive := by
  rfl

/-- The Brauer quotient dimension of a diagonal tensor product is the
product of the two factor dimensions. -/
theorem finrank_brauerQuotientAlgebra_tensorProduct
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    Module.finrank k
        (BrauerQuotientAlgebra
          (k := k) (P := P) (A := A ⊗[k] D)) =
      Module.finrank k
          (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) *
        Module.finrank k
          (BrauerQuotientAlgebra (k := k) (P := P) (A := D)) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    S.permutationBasis.tensorProductMulSemiringAction
      T.permutationBasis
  letI : SMulCommClass P k (A ⊗[k] D) :=
    S.permutationBasis.tensorProductSMulCommClass
      T.permutationBasis
  calc
    Module.finrank k
        (BrauerQuotientAlgebra
          (k := k) (P := P) (A := A ⊗[k] D)) =
        Module.finrank k
          (BrauerQuotientAlgebra
              (k := k) (P := P) (A := A) ⊗[k]
            BrauerQuotientAlgebra
              (k := k) (P := P) (A := D)) :=
      (S.brauerQuotientTensorEquiv T).toLinearEquiv.finrank_eq.symm
    _ =
        Module.finrank k
            (BrauerQuotientAlgebra
              (k := k) (P := P) (A := A)) *
          Module.finrank k
            (BrauerQuotientAlgebra
              (k := k) (P := P) (A := D)) :=
      Module.finrank_tensorProduct

variable [Finite k]

omit [Fintype P] in
/-- A tensor product of finite-field Dade algebras is
Brauer-primitive exactly when both tensor factors are
Brauer-primitive. -/
theorem tensorProduct_isBrauerPrimitive_iff
    [Finite P] :
    letI : Fintype P := Fintype.ofFinite P
    ∀ (S : DadeAlgebra p k P A)
      (T : DadeAlgebra p k P D),
      letI : MulSemiringAction P (A ⊗[k] D) :=
        S.permutationBasis.tensorProductMulSemiringAction
          T.permutationBasis
      letI : SMulCommClass P k (A ⊗[k] D) :=
        S.permutationBasis.tensorProductSMulCommClass
          T.permutationBasis
      (S.tensorProduct T).IsBrauerPrimitive ↔
        S.IsBrauerPrimitive ∧ T.IsBrauerPrimitive := by
  letI : Fintype P := Fintype.ofFinite P
  intro S T
  letI : MulSemiringAction P (A ⊗[k] D) :=
    S.permutationBasis.tensorProductMulSemiringAction
      T.permutationBasis
  letI : SMulCommClass P k (A ⊗[k] D) :=
    S.permutationBasis.tensorProductSMulCommClass
      T.permutationBasis
  rw [
    ← (S.tensorProduct T
      ).finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive,
    ← S.finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive,
    ← T.finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive,
    S.finrank_brauerQuotientAlgebra_tensorProduct T]
  constructor
  · intro h
    exact
      ⟨Nat.eq_one_of_mul_eq_one_right h,
        Nat.eq_one_of_mul_eq_one_left h⟩
  · rintro ⟨hS, hT⟩
    rw [hS, hT, one_mul]

omit [Fintype P] in
/-- The left-right tensor product `A ⊗ Aᵐᵒᵖ` is
Brauer-primitive exactly when `A` is. -/
theorem tensorProduct_opposite_isBrauerPrimitive_iff
    [Finite P] :
    letI : Fintype P := Fintype.ofFinite P
    ∀ S : DadeAlgebra p k P A,
      letI : MulSemiringAction P (A ⊗[k] Aᵐᵒᵖ) :=
        S.permutationBasis.tensorProductMulSemiringAction
          S.permutationBasis.opposite
      letI : SMulCommClass P k (A ⊗[k] Aᵐᵒᵖ) :=
        S.permutationBasis.tensorProductSMulCommClass
          S.permutationBasis.opposite
      (S.tensorProduct S.opposite).IsBrauerPrimitive ↔
        S.IsBrauerPrimitive := by
  letI : Fintype P := Fintype.ofFinite P
  intro S
  letI : MulSemiringAction P (A ⊗[k] Aᵐᵒᵖ) :=
    S.permutationBasis.tensorProductMulSemiringAction
      S.permutationBasis.opposite
  letI : SMulCommClass P k (A ⊗[k] Aᵐᵒᵖ) :=
    S.permutationBasis.tensorProductSMulCommClass
      S.permutationBasis.opposite
  rw [S.tensorProduct_isBrauerPrimitive_iff S.opposite]
  simp only [S.opposite_isBrauerPrimitive_iff, and_self]

end DadeAlgebra
end Representation
