/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeNormalizerExtensionTensorProduct

/-!
# Factorwise Dade normalizer extensions

This file bundles the tensor-product maps associated to two Brauer
normalizer extensions.  The source remains the product of the two
factor normalizers: no decomposition assertion is made for arbitrary
units of the tensor-product algebra.
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
variable
  {I : InteriorAction (P := P) (A := A)}
  {J : InteriorAction (P := P) (A := D)}

/-- The part of a tensor-product Brauer normalizer extension that is
forced by extensions on the two factors.  Its source is the product
of the factor normalizers, and its fixed-unit and conjugation laws are
stated on pure tensors. -/
structure FactorwiseBrauerNormalizerExtension
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D)
    (I : InteriorAction (P := P) (A := A))
    (J : InteriorAction (P := P) (A := D)) where
  /-- Product-normalizer homomorphism into the tensor Brauer
  quotient. -/
  hom :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    I.unitNormalizer × J.unitNormalizer →*
      (BrauerQuotientAlgebra
        (k := k) (P := P) (A := A ⊗[k] D))ˣ
  /-- The product-normalizer homomorphism extends the Brauer
  projection on tensor products of factor fixed units. -/
  extends_fixedUnitPair :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    ∀ u :
        (fixedSubalgebra (k := k) (P := P) (A := A))ˣ ×
          (fixedSubalgebra (k := k) (P := P) (A := D))ˣ,
      hom (fixedUnitPairToNormalizers (k := k) I J u) =
        fixedUnitBrauerProjection
          (k := k) (P := P) (A := A ⊗[k] D)
          (S.fixedTensorProductUnits T u)
  /-- Conjugation compatibility on tensors of fixed elements. -/
  conjugation_compatible :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    ∀ (s : I.unitNormalizer × J.unitNormalizer)
      (c : fixedSubalgebra (k := k) (P := P) (A := A))
      (d : fixedSubalgebra (k := k) (P := P) (A := D)),
      ∃ (c' : fixedSubalgebra (k := k) (P := P) (A := A))
          (d' : fixedSubalgebra (k := k) (P := P) (A := D)),
        ((S.permutationBasis.fixedTensorProduct
            T.permutationBasis c' d' :
          fixedSubalgebra
            (k := k) (P := P) (A := A ⊗[k] D)) :
          A ⊗[k] D) =
            (↑((tensorProductUnits (k := k)
                ((s.1 : Aˣ), (s.2 : Dˣ)))⁻¹) :
                A ⊗[k] D) *
              ((c : A) ⊗ₜ[k] (d : D)) *
              (tensorProductUnits (k := k)
                ((s.1 : Aˣ), (s.2 : Dˣ)) :
                A ⊗[k] D) ∧
          (↑((hom s)⁻¹) :
              BrauerQuotientAlgebra
                (k := k) (P := P) (A := A ⊗[k] D)) *
                brauerAlgebraProjection
                  (k := k) (P := P) (A := A ⊗[k] D)
                  (S.permutationBasis.fixedTensorProduct
                    T.permutationBasis c d) *
              (hom s :
                BrauerQuotientAlgebra
                  (k := k) (P := P) (A := A ⊗[k] D)) =
            brauerAlgebraProjection
              (k := k) (P := P) (A := A ⊗[k] D)
              (S.permutationBasis.fixedTensorProduct
                T.permutationBasis c' d')

/-- Two Brauer normalizer extensions canonically produce their
factorwise tensor-product extension. -/
def factorwiseBrauerNormalizerExtension
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D)
    (E : BrauerNormalizerExtension (k := k) I)
    (F : BrauerNormalizerExtension (k := k) J) :
    FactorwiseBrauerNormalizerExtension S T I J where
  hom :=
    brauerNormalizerExtensionTensorProductHom S T E F
  extends_fixedUnitPair :=
    brauerNormalizerExtensionTensorProductHom_fixedUnitPair
      S T E F
  conjugation_compatible :=
    brauerNormalizerExtensionTensorProductHom_conjugation
      S T E F

/-- Existence of the factorwise part of a tensor-product extension. -/
def HasFactorwiseBrauerNormalizerExtension
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D)
    (I : InteriorAction (P := P) (A := A))
    (J : InteriorAction (P := P) (A := D)) : Prop :=
  Nonempty (FactorwiseBrauerNormalizerExtension S T I J)

/-- Factorwise tensor closure of the Puig--Turull extension
property. -/
theorem hasFactorwiseBrauerNormalizerExtension_of_factors
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D)
    (hI : HasBrauerNormalizerExtension (k := k) I)
    (hJ : HasBrauerNormalizerExtension (k := k) J) :
    HasFactorwiseBrauerNormalizerExtension S T I J := by
  rcases hI with ⟨E⟩
  rcases hJ with ⟨F⟩
  exact ⟨factorwiseBrauerNormalizerExtension S T E F⟩

end DadeAlgebra
end Representation
