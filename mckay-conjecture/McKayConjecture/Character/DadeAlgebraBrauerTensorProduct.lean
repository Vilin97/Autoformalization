/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebra
import McKayConjecture.Character.PermutationAlgebraBrauerTensorEquiv

/-!
# Tensor products of Brauer quotients of Dade algebras

The permutation-algebra tensor theorem specializes to the pointed
permutation bases carried by two Dade algebras.  Their
finite-dimensionality data supplies the finite basis-index instances
locally, so callers do not need to expose object-dependent instances.
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

/-- The tensor product of the algebra Brauer quotients of two Dade
algebras is canonically equivalent to the Brauer quotient of their
diagonal tensor-product algebra. -/
def brauerQuotientTensorEquiv
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    (BrauerQuotientAlgebra (k := k) (P := P) (A := A) ⊗[k]
      BrauerQuotientAlgebra (k := k) (P := P) (A := D)) ≃ₐ[k]
        BrauerQuotientAlgebra
          (k := k) (P := P) (A := A ⊗[k] D) := by
  letI : FiniteDimensional k A :=
    S.finiteDimensional
  letI : FiniteDimensional k D :=
    T.finiteDimensional
  letI : Finite S.permutationBasis.index :=
    Module.Finite.finite_basis S.permutationBasis.basis
  letI : Finite T.permutationBasis.index :=
    Module.Finite.finite_basis T.permutationBasis.basis
  exact
    S.permutationBasis.brauerQuotientAlgebraTensorEquiv
      T.permutationBasis S.isPGroup

/-- The Dade-algebra specialization agrees with pure tensors of
Brauer projections. -/
@[simp]
theorem brauerQuotientTensorEquiv_projection_tmul
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D)
    (x : fixedSubalgebra (k := k) (P := P) (A := A))
    (y : fixedSubalgebra (k := k) (P := P) (A := D)) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    S.brauerQuotientTensorEquiv T
        (brauerAlgebraProjection
            (k := k) (P := P) (A := A) x ⊗ₜ[k]
          brauerAlgebraProjection
            (k := k) (P := P) (A := D) y) =
      brauerAlgebraProjection
        (k := k) (P := P) (A := A ⊗[k] D)
        (S.permutationBasis.fixedTensorProduct
          T.permutationBasis x y) := by
  letI : FiniteDimensional k A :=
    S.finiteDimensional
  letI : FiniteDimensional k D :=
    T.finiteDimensional
  letI : Finite S.permutationBasis.index :=
    Module.Finite.finite_basis S.permutationBasis.basis
  letI : Finite T.permutationBasis.index :=
    Module.Finite.finite_basis T.permutationBasis.basis
  exact
    (S.permutationBasis).brauerQuotientAlgebraTensorEquiv_projection_tmul
      T.permutationBasis S.isPGroup x y

end DadeAlgebra
end Representation
