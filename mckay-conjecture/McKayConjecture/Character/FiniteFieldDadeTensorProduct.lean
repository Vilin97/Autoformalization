/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebra
import McKayConjecture.Character.FiniteFieldCentralSimpleTensorProduct
import McKayConjecture.Character.PermutationAlgebraTensorProduct

/-!
# Tensor products of Dade algebras over finite fields

The tensor product of the pointed permutation bases gives the
permutation-algebra structure.  Finite-field splitting supplies the
central-simple structure of the tensor-product algebra.
-/

noncomputable section

open scoped TensorProduct

namespace Representation
namespace DadeAlgebra

variable {p : ℕ} [Fact p.Prime]
variable {k P A D : Type}
variable [Field k] [Finite k] [CharP k p]
variable [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [Ring D] [Algebra k D]
variable [MulSemiringAction P A] [SMulCommClass P k A]
variable [MulSemiringAction P D] [SMulCommClass P k D]

/-- Tensor closure of Dade algebras over a finite coefficient field. -/
def tensorProduct
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    DadeAlgebra p k P (A ⊗[k] D) := by
  letI : FiniteDimensional k A :=
    S.finiteDimensional
  letI : FiniteDimensional k D :=
    T.finiteDimensional
  letI : Algebra.IsCentral k A :=
    S.isCentral
  letI : IsSimpleRing A :=
    S.isSimple
  letI : Algebra.IsCentral k D :=
    T.isCentral
  letI : IsSimpleRing D :=
    T.isSimple
  letI : MulSemiringAction P (A ⊗[k] D) :=
    S.permutationBasis.tensorProductMulSemiringAction
      T.permutationBasis
  letI : SMulCommClass P k (A ⊗[k] D) :=
    S.permutationBasis.tensorProductSMulCommClass
      T.permutationBasis
  exact
    { isCentral :=
        tensorProduct_isCentral_of_finiteField k A D
      isSimple :=
        tensorProduct_isSimpleRing_of_finiteField k A D
      finiteDimensional := inferInstance
      isPGroup := S.isPGroup
      permutationBasis :=
        S.permutationBasis.tensorProduct
          T.permutationBasis }

end DadeAlgebra
end Representation
