/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationAlgebraBrauerTensorHom

/-!
# The Brauer algebra of a tensor product of permutation algebras

For finite permutation algebras over a field of characteristic `p`
and a finite `p`-group `P`, the natural homomorphism

`A(P) ⊗ B(P) → (A ⊗ B)(P)`

is an algebra equivalence.  Bijectivity is proved by comparing the
fixed-index bases on both sides.
-/

noncomputable section

open scoped TensorProduct

namespace Representation
namespace PointedPermutationAlgebraBasis

variable {p : ℕ} [Fact p.Prime]
variable {k P A D : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [Ring A] [Algebra k A]
variable [Ring D] [Algebra k D]
variable [MulSemiringAction P A] [SMulCommClass P k A]
variable [MulSemiringAction P D] [SMulCommClass P k D]

variable
  (B : PointedPermutationAlgebraBasis
    (k := k) (P := P) (A := A))
  (C : PointedPermutationAlgebraBasis
    (k := k) (P := P) (A := D))

variable [Finite B.index] [Finite C.index]

noncomputable local instance tensorBrauerEquivGroupFintype :
    Fintype P :=
  Fintype.ofFinite P

noncomputable local instance tensorBrauerEquivTensorIndexFinite :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    Finite (B.tensorProduct C).index := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  change Finite (B.index × C.index)
  infer_instance

noncomputable local instance tensorBrauerEquivLeftFixedIndexFintype :
    Fintype B.FixedIndex :=
  Fintype.ofFinite B.FixedIndex

noncomputable local instance tensorBrauerEquivRightFixedIndexFintype :
    Fintype C.FixedIndex :=
  Fintype.ofFinite C.FixedIndex

noncomputable local instance tensorBrauerEquivTensorFixedIndexFintype :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    Fintype (B.tensorProduct C).FixedIndex := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  exact Fintype.ofFinite (B.tensorProduct C).FixedIndex

/-- A fixed index of the tensor-product permutation basis is the same
as a pair of fixed indices of the two factors. -/
def fixedIndexTensorProductEquiv :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    (B.tensorProduct C).FixedIndex ≃
      B.FixedIndex × C.FixedIndex := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  exact
    { toFun := fun x =>
        (⟨x.1.1, fun g =>
            congrArg Prod.fst (x.property g)⟩,
          ⟨x.1.2, fun g =>
            congrArg Prod.snd (x.property g)⟩)
      invFun := fun x =>
        ⟨(x.1.1, x.2.1), fun g =>
          Prod.ext (x.1.property g) (x.2.property g)⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact Prod.ext rfl rfl
      right_inv := fun x => by
        apply Prod.ext
        · exact Subtype.ext rfl
        · exact Subtype.ext rfl }

/-- The fixed tensor-product basis index associated with a pair of
fixed factor indices. -/
def fixedTensorBasisIndex
    (i : B.FixedIndex) (j : C.FixedIndex) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    (B.tensorProduct C).FixedIndex :=
  (B.fixedIndexTensorProductEquiv C).symm (i, j)

omit [Finite P] [Finite B.index] [Finite C.index] in
@[simp]
theorem fixedTensorBasisIndex_fst
    (i : B.FixedIndex) (j : C.FixedIndex) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    ((B.fixedTensorBasisIndex C i j :
        (B.tensorProduct C).index).1) = i :=
  rfl

omit [Finite P] [Finite B.index] [Finite C.index] in
@[simp]
theorem fixedTensorBasisIndex_snd
    (i : B.FixedIndex) (j : C.FixedIndex) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    ((B.fixedTensorBasisIndex C i j :
        (B.tensorProduct C).index).2) = j :=
  rfl

omit [Finite P] [Finite B.index] [Finite C.index] in
/-- The target fixed basis element at a product index is the tensor of
the corresponding fixed basis elements. -/
theorem fixedBasisElement_fixedTensorBasisIndex
    (i : B.FixedIndex) (j : C.FixedIndex) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    ((B.tensorProduct C).fixedBasisElement
        (B.fixedTensorBasisIndex C i j) :
      A ⊗[k] D) =
        (B.fixedBasisElement i : A) ⊗ₜ[k]
          (C.fixedBasisElement j : D) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  change
    (B.tensorProduct C).basis
        (B.fixedTensorBasisIndex C i j) =
      B.basis i ⊗ₜ[k] C.basis j
  have hindex :
      ((B.fixedTensorBasisIndex C i j :
          (B.tensorProduct C).index)) =
        ((i : B.index), (j : C.index)) :=
    rfl
  rw [hindex]
  exact B.tensorProduct_basis_apply C (i, j)

/-- The natural algebra homomorphism maps the tensor product of two
fixed-index quotient basis vectors to the corresponding target basis
vector. -/
@[simp]
theorem brauerQuotientAlgebraTensorHom_basis_tmul
    (hP : IsPGroup p P)
    (i : B.FixedIndex) (j : C.FixedIndex) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    B.brauerQuotientAlgebraTensorHom C
        (B.brauerQuotientAlgebraFixedBasis hP i ⊗ₜ[k]
          C.brauerQuotientAlgebraFixedBasis hP j) =
      (B.tensorProduct C).brauerQuotientAlgebraFixedBasis hP
        (B.fixedTensorBasisIndex C i j) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  rw [B.brauerQuotientAlgebraFixedBasis_apply hP i]
  rw [C.brauerQuotientAlgebraFixedBasis_apply hP j]
  rw [B.brauerQuotientAlgebraTensorHom_projection_tmul C]
  rw [(B.tensorProduct C).brauerQuotientAlgebraFixedBasis_apply]
  congr 1
  apply Subtype.ext
  exact
    (B.fixedBasisElement_fixedTensorBasisIndex C i j).symm

/-- The natural tensor-product Brauer homomorphism is surjective. -/
theorem brauerQuotientAlgebraTensorHom_surjective
    (hP : IsPGroup p P) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    Function.Surjective
      (B.brauerQuotientAlgebraTensorHom C) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  change
    Function.Surjective
      (B.brauerQuotientAlgebraTensorHom C).toLinearMap
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [←
    ((B.tensorProduct C).brauerQuotientAlgebraFixedBasis hP).span_eq]
  apply Submodule.span_le.2
  rw [Set.range_subset_iff]
  intro t
  let ij := B.fixedIndexTensorProductEquiv C t
  refine
    ⟨B.brauerQuotientAlgebraFixedBasis hP ij.1 ⊗ₜ[k]
        C.brauerQuotientAlgebraFixedBasis hP ij.2, ?_⟩
  change
    B.brauerQuotientAlgebraTensorHom C
        (B.brauerQuotientAlgebraFixedBasis hP ij.1 ⊗ₜ[k]
          C.brauerQuotientAlgebraFixedBasis hP ij.2) =
      (B.tensorProduct C).brauerQuotientAlgebraFixedBasis hP t
  rw [B.brauerQuotientAlgebraTensorHom_basis_tmul C hP]
  congr 1

/-- Source and target of the natural tensor-product Brauer
homomorphism have the same dimension. -/
theorem finrank_brauerQuotientAlgebra_tensorProduct
    (hP : IsPGroup p P) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    Module.finrank k
        (BrauerQuotientAlgebra (k := k) (P := P) (A := A) ⊗[k]
          BrauerQuotientAlgebra (k := k) (P := P) (A := D)) =
      Module.finrank k
        (BrauerQuotientAlgebra
          (k := k) (P := P) (A := A ⊗[k] D)) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  rw [Module.finrank_tensorProduct]
  rw [B.finrank_brauerQuotientAlgebra_eq_card_fixedIndex hP]
  rw [C.finrank_brauerQuotientAlgebra_eq_card_fixedIndex hP]
  rw [(B.tensorProduct C).finrank_brauerQuotientAlgebra_eq_card_fixedIndex hP]
  rw [Fintype.card_congr (B.fixedIndexTensorProductEquiv C)]
  exact
    (Fintype.card_prod B.FixedIndex C.FixedIndex).symm

/-- The natural tensor-product Brauer homomorphism is bijective. -/
theorem brauerQuotientAlgebraTensorHom_bijective
    (hP : IsPGroup p P) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    Function.Bijective
      (B.brauerQuotientAlgebraTensorHom C) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  let sourceBasis :=
    (B.brauerQuotientAlgebraFixedBasis hP).tensorProduct
      (C.brauerQuotientAlgebraFixedBasis hP)
  let targetBasis :=
    (B.tensorProduct C).brauerQuotientAlgebraFixedBasis hP
  letI : FiniteDimensional k
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A) ⊗[k]
        BrauerQuotientAlgebra (k := k) (P := P) (A := D)) :=
    Module.Finite.of_basis sourceBasis
  letI : FiniteDimensional k
      (BrauerQuotientAlgebra
        (k := k) (P := P) (A := A ⊗[k] D)) :=
    Module.Finite.of_basis targetBasis
  have hsurj :=
    B.brauerQuotientAlgebraTensorHom_surjective C hP
  have hinj :
      Function.Injective
        (B.brauerQuotientAlgebraTensorHom C).toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (B.finrank_brauerQuotientAlgebra_tensorProduct C hP)).2
        hsurj
  exact ⟨hinj, hsurj⟩

/-- Canonical algebra equivalence between the tensor product of the
two algebra Brauer quotients and the Brauer quotient of the diagonal
tensor-product algebra. -/
def brauerQuotientAlgebraTensorEquiv
    (hP : IsPGroup p P) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    (BrauerQuotientAlgebra (k := k) (P := P) (A := A) ⊗[k]
      BrauerQuotientAlgebra (k := k) (P := P) (A := D)) ≃ₐ[k]
        BrauerQuotientAlgebra
          (k := k) (P := P) (A := A ⊗[k] D) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  exact
    AlgEquiv.ofBijective
      (B.brauerQuotientAlgebraTensorHom C)
      (B.brauerQuotientAlgebraTensorHom_bijective C hP)

/-- The algebra equivalence agrees with pure tensors of Brauer
projections. -/
@[simp]
theorem brauerQuotientAlgebraTensorEquiv_projection_tmul
    (hP : IsPGroup p P)
    (x : fixedSubalgebra (k := k) (P := P) (A := A))
    (y : fixedSubalgebra (k := k) (P := P) (A := D)) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    B.brauerQuotientAlgebraTensorEquiv C hP
        (brauerAlgebraProjection
            (k := k) (P := P) (A := A) x ⊗ₜ[k]
          brauerAlgebraProjection
            (k := k) (P := P) (A := D) y) =
      brauerAlgebraProjection
        (k := k) (P := P) (A := A ⊗[k] D)
        (B.fixedTensorProduct C x y) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  exact B.brauerQuotientAlgebraTensorHom_projection_tmul C x y

end PointedPermutationAlgebraBasis
end Representation
