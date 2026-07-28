/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraBrauerTensorProduct
import McKayConjecture.Character.DadeNormalizerExtension

/-!
# Tensor-product maps for Dade normalizer extensions

Two Brauer normalizer extensions can be multiplied on the product of
their normalizer groups.  The target is identified with the Brauer
quotient of the diagonal tensor-product algebra by the canonical
Brauer tensor equivalence.

This is the factorwise tensor construction needed when a common
normalizer acts through several Dade factors.  It does **not** produce
an extension on the full unit normalizer of the tensor-product
algebra: a general unit of `A ⊗ D` need not be a tensor of units of
`A` and `D`, and a pair of factor normalizers need not normalize the
diagonal interior image unless their induced automorphisms of `P`
agree.  The theorems below therefore state exactly the homomorphism,
fixed pure-unit law, and conjugation law that follow without an
additional factorization or synchronization hypothesis.  The bundled
factorwise extension assembled from these maps is defined separately
in `DadeNormalizerExtensionFactorwise`.
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

/-- Tensor two units.  This is a homomorphism on the product of the
two unit groups, since the two tensor factors commute. -/
def tensorProductUnits :
    Aˣ × Dˣ →* (A ⊗[k] D)ˣ where
  toFun u :=
    { val := (u.1 : A) ⊗ₜ[k] (u.2 : D)
      inv := (↑(u.1⁻¹) : A) ⊗ₜ[k] (↑(u.2⁻¹) : D)
      val_inv := by
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        simp only [Units.mul_inv]
        exact Algebra.TensorProduct.one_def
      inv_val := by
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        simp only [Units.inv_mul]
        exact Algebra.TensorProduct.one_def }
  map_one' := by
    apply Units.ext
    exact Algebra.TensorProduct.one_def.symm
  map_mul' := fun u v => by
    apply Units.ext
    change
      (↑(u.1 * v.1) : A) ⊗ₜ[k] (↑(u.2 * v.2) : D) =
        ((u.1 : A) ⊗ₜ[k] (u.2 : D)) *
          ((v.1 : A) ⊗ₜ[k] (v.2 : D))
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    rfl

@[simp]
theorem coe_tensorProductUnits (u : Aˣ × Dˣ) :
    (tensorProductUnits (k := k) u : A ⊗[k] D) =
      (u.1 : A) ⊗ₜ[k] (u.2 : D) :=
  rfl

@[simp]
theorem coe_inv_tensorProductUnits (u : Aˣ × Dˣ) :
    (↑((tensorProductUnits (k := k) u)⁻¹) : A ⊗[k] D) =
      (↑(u.1⁻¹) : A) ⊗ₜ[k] (↑(u.2⁻¹) : D) :=
  rfl

/-- Tensor two units of the factor fixed algebras. -/
def fixedTensorProductUnits
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    (fixedSubalgebra (k := k) (P := P) (A := A))ˣ ×
        (fixedSubalgebra (k := k) (P := P) (A := D))ˣ →*
      (fixedSubalgebra
        (k := k) (P := P) (A := A ⊗[k] D))ˣ := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    S.permutationBasis.tensorProductMulSemiringAction
      T.permutationBasis
  letI : SMulCommClass P k (A ⊗[k] D) :=
    S.permutationBasis.tensorProductSMulCommClass
      T.permutationBasis
  exact
    { toFun := fun u =>
        { val :=
            S.permutationBasis.fixedTensorProduct
              T.permutationBasis u.1 u.2
          inv :=
            S.permutationBasis.fixedTensorProduct
              T.permutationBasis
              (((Prod.fst u)⁻¹ :
                  (fixedSubalgebra
                    (k := k) (P := P) (A := A))ˣ) :
                fixedSubalgebra (k := k) (P := P) (A := A))
              (((Prod.snd u)⁻¹ :
                  (fixedSubalgebra
                    (k := k) (P := P) (A := D))ˣ) :
                fixedSubalgebra (k := k) (P := P) (A := D))
          val_inv := by
            have hu :
                (u.1 : A) * (↑(u.1⁻¹) : A) = 1 :=
              congrArg
                (fun x :
                  fixedSubalgebra
                    (k := k) (P := P) (A := A) => (x : A))
                (Prod.fst u).val_inv
            have hv :
                (u.2 : D) * (↑(u.2⁻¹) : D) = 1 :=
              congrArg
                (fun x :
                  fixedSubalgebra
                    (k := k) (P := P) (A := D) => (x : D))
                (Prod.snd u).val_inv
            apply Subtype.ext
            change
              ((u.1 : A) ⊗ₜ[k] (u.2 : D)) *
                  ((↑(u.1⁻¹) : A) ⊗ₜ[k] (↑(u.2⁻¹) : D)) =
                1
            rw [Algebra.TensorProduct.tmul_mul_tmul]
            rw [hu, hv]
            exact Algebra.TensorProduct.one_def.symm
          inv_val := by
            have hu :
                (↑(u.1⁻¹) : A) * (u.1 : A) = 1 :=
              congrArg
                (fun x :
                  fixedSubalgebra
                    (k := k) (P := P) (A := A) => (x : A))
                (Prod.fst u).inv_val
            have hv :
                (↑(u.2⁻¹) : D) * (u.2 : D) = 1 :=
              congrArg
                (fun x :
                  fixedSubalgebra
                    (k := k) (P := P) (A := D) => (x : D))
                (Prod.snd u).inv_val
            apply Subtype.ext
            change
              ((↑(u.1⁻¹) : A) ⊗ₜ[k] (↑(u.2⁻¹) : D)) *
                  ((u.1 : A) ⊗ₜ[k] (u.2 : D)) =
                1
            rw [Algebra.TensorProduct.tmul_mul_tmul]
            rw [hu, hv]
            exact Algebra.TensorProduct.one_def.symm }
      map_one' := by
        apply Units.ext
        apply Subtype.ext
        exact Algebra.TensorProduct.one_def.symm
      map_mul' := fun u v => by
        apply Units.ext
        apply Subtype.ext
        change
          (↑(u.1 * v.1) : A) ⊗ₜ[k] (↑(u.2 * v.2) : D) =
            ((u.1 : A) ⊗ₜ[k] (u.2 : D)) *
              ((v.1 : A) ⊗ₜ[k] (v.2 : D))
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        rfl }

omit [Fact p.Prime] [CharP k p] [Fintype P] in
@[simp]
theorem coe_fixedTensorProductUnits
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D)
    (u :
      (fixedSubalgebra (k := k) (P := P) (A := A))ˣ ×
        (fixedSubalgebra (k := k) (P := P) (A := D))ˣ) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    ((S.fixedTensorProductUnits T u :
        (fixedSubalgebra
          (k := k) (P := P) (A := A ⊗[k] D))ˣ) :
      A ⊗[k] D) =
        (u.1 : A) ⊗ₜ[k] (u.2 : D) :=
  rfl

/-- Tensor two units in the factor Brauer quotients and transport the
result through the Brauer tensor equivalence. -/
def brauerTensorProductUnits
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    (BrauerQuotientAlgebra (k := k) (P := P) (A := A))ˣ ×
        (BrauerQuotientAlgebra (k := k) (P := P) (A := D))ˣ →*
      (BrauerQuotientAlgebra
        (k := k) (P := P) (A := A ⊗[k] D))ˣ := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    S.permutationBasis.tensorProductMulSemiringAction
      T.permutationBasis
  letI : SMulCommClass P k (A ⊗[k] D) :=
    S.permutationBasis.tensorProductSMulCommClass
      T.permutationBasis
  exact
    (Units.map
      (S.brauerQuotientTensorEquiv T).toAlgHom.toMonoidHom).comp
        (tensorProductUnits (k := k))

@[simp]
theorem coe_brauerTensorProductUnits
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D)
    (u :
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A))ˣ ×
        (BrauerQuotientAlgebra (k := k) (P := P) (A := D))ˣ) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    (S.brauerTensorProductUnits T u :
        BrauerQuotientAlgebra
          (k := k) (P := P) (A := A ⊗[k] D)) =
      S.brauerQuotientTensorEquiv T
        ((u.1 :
            BrauerQuotientAlgebra
              (k := k) (P := P) (A := A)) ⊗ₜ[k]
          (u.2 :
            BrauerQuotientAlgebra
              (k := k) (P := P) (A := D))) :=
  rfl

@[simp]
theorem coe_inv_brauerTensorProductUnits
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D)
    (u :
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A))ˣ ×
        (BrauerQuotientAlgebra (k := k) (P := P) (A := D))ˣ) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    (↑((S.brauerTensorProductUnits T u)⁻¹) :
        BrauerQuotientAlgebra
          (k := k) (P := P) (A := A ⊗[k] D)) =
      S.brauerQuotientTensorEquiv T
        ((↑(u.1⁻¹) :
            BrauerQuotientAlgebra
              (k := k) (P := P) (A := A)) ⊗ₜ[k]
          (↑(u.2⁻¹) :
            BrauerQuotientAlgebra
              (k := k) (P := P) (A := D))) :=
  rfl

variable
  {I : InteriorAction (P := P) (A := A)}
  {J : InteriorAction (P := P) (A := D)}

/-- The factorwise tensor product of two Brauer normalizer
extensions. -/
def brauerNormalizerExtensionTensorProductHom
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D)
    (E : BrauerNormalizerExtension (k := k) I)
    (F : BrauerNormalizerExtension (k := k) J) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    I.unitNormalizer × J.unitNormalizer →*
      (BrauerQuotientAlgebra
        (k := k) (P := P) (A := A ⊗[k] D))ˣ := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    S.permutationBasis.tensorProductMulSemiringAction
      T.permutationBasis
  letI : SMulCommClass P k (A ⊗[k] D) :=
    S.permutationBasis.tensorProductSMulCommClass
      T.permutationBasis
  exact
    (S.brauerTensorProductUnits T).comp
      (E.hom.prodMap F.hom)

@[simp]
theorem coe_brauerNormalizerExtensionTensorProductHom
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D)
    (E : BrauerNormalizerExtension (k := k) I)
    (F : BrauerNormalizerExtension (k := k) J)
    (s : I.unitNormalizer × J.unitNormalizer) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    (brauerNormalizerExtensionTensorProductHom S T E F s :
        BrauerQuotientAlgebra
          (k := k) (P := P) (A := A ⊗[k] D)) =
      S.brauerQuotientTensorEquiv T
        ((E.hom s.1 :
            BrauerQuotientAlgebra
              (k := k) (P := P) (A := A)) ⊗ₜ[k]
          (F.hom s.2 :
            BrauerQuotientAlgebra
              (k := k) (P := P) (A := D))) :=
  rfl

@[simp]
theorem coe_inv_brauerNormalizerExtensionTensorProductHom
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D)
    (E : BrauerNormalizerExtension (k := k) I)
    (F : BrauerNormalizerExtension (k := k) J)
    (s : I.unitNormalizer × J.unitNormalizer) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    (↑((brauerNormalizerExtensionTensorProductHom S T E F s)⁻¹) :
        BrauerQuotientAlgebra
          (k := k) (P := P) (A := A ⊗[k] D)) =
      S.brauerQuotientTensorEquiv T
        ((↑((E.hom s.1)⁻¹) :
            BrauerQuotientAlgebra
              (k := k) (P := P) (A := A)) ⊗ₜ[k]
          (↑((F.hom s.2)⁻¹) :
            BrauerQuotientAlgebra
              (k := k) (P := P) (A := D))) :=
  rfl

/-- Pair the canonical inclusions of factor fixed units into their
respective unit normalizers. -/
def fixedUnitPairToNormalizers
    (I : InteriorAction (P := P) (A := A))
    (J : InteriorAction (P := P) (A := D)) :
    (fixedSubalgebra (k := k) (P := P) (A := A))ˣ ×
        (fixedSubalgebra (k := k) (P := P) (A := D))ˣ →*
      I.unitNormalizer × J.unitNormalizer :=
  (I.fixedUnitToNormalizer (k := k)).prodMap
    (J.fixedUnitToNormalizer (k := k))

/-- The factorwise tensor extension agrees with the Brauer projection
on every tensor product of factor fixed units. -/
theorem brauerNormalizerExtensionTensorProductHom_fixedUnitPair
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D)
    (E : BrauerNormalizerExtension (k := k) I)
    (F : BrauerNormalizerExtension (k := k) J)
    (u :
      (fixedSubalgebra (k := k) (P := P) (A := A))ˣ ×
        (fixedSubalgebra (k := k) (P := P) (A := D))ˣ) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
    brauerNormalizerExtensionTensorProductHom S T E F
        (fixedUnitPairToNormalizers (k := k) I J u) =
      fixedUnitBrauerProjection
        (k := k) (P := P) (A := A ⊗[k] D)
        (S.fixedTensorProductUnits T u) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    S.permutationBasis.tensorProductMulSemiringAction
      T.permutationBasis
  letI : SMulCommClass P k (A ⊗[k] D) :=
    S.permutationBasis.tensorProductSMulCommClass
      T.permutationBasis
  apply Units.ext
  change
    S.brauerQuotientTensorEquiv T
        ((E.hom
              (I.fixedUnitToNormalizer (k := k) u.1) :
            BrauerQuotientAlgebra
              (k := k) (P := P) (A := A)) ⊗ₜ[k]
          (F.hom
              (J.fixedUnitToNormalizer (k := k) u.2) :
            BrauerQuotientAlgebra
              (k := k) (P := P) (A := D))) =
      brauerAlgebraProjection
        (k := k) (P := P) (A := A ⊗[k] D)
        (S.permutationBasis.fixedTensorProduct
          T.permutationBasis u.1 u.2)
  rw [E.hom_fixedUnitToNormalizer, F.hom_fixedUnitToNormalizer]
  exact S.brauerQuotientTensorEquiv_projection_tmul T u.1 u.2

/-- Factorwise conjugation compatibility on pure tensors.  Both the
ambient conjugate and its Brauer projection are the tensor products
of the conjugates supplied by the two factor extensions. -/
theorem brauerNormalizerExtensionTensorProductHom_conjugation
    (S : DadeAlgebra p k P A)
    (T : DadeAlgebra p k P D)
    (E : BrauerNormalizerExtension (k := k) I)
    (F : BrauerNormalizerExtension (k := k) J)
    (s : I.unitNormalizer × J.unitNormalizer)
    (c : fixedSubalgebra (k := k) (P := P) (A := A))
    (d : fixedSubalgebra (k := k) (P := P) (A := D)) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      S.permutationBasis.tensorProductMulSemiringAction
        T.permutationBasis
    letI : SMulCommClass P k (A ⊗[k] D) :=
      S.permutationBasis.tensorProductSMulCommClass
        T.permutationBasis
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
        (↑((brauerNormalizerExtensionTensorProductHom
              S T E F s)⁻¹) :
            BrauerQuotientAlgebra
              (k := k) (P := P) (A := A ⊗[k] D)) *
              brauerAlgebraProjection
                (k := k) (P := P) (A := A ⊗[k] D)
                (S.permutationBasis.fixedTensorProduct
                  T.permutationBasis c d) *
            (brauerNormalizerExtensionTensorProductHom
              S T E F s :
              BrauerQuotientAlgebra
                (k := k) (P := P) (A := A ⊗[k] D)) =
          brauerAlgebraProjection
            (k := k) (P := P) (A := A ⊗[k] D)
            (S.permutationBasis.fixedTensorProduct
              T.permutationBasis c' d') := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    S.permutationBasis.tensorProductMulSemiringAction
      T.permutationBasis
  letI : SMulCommClass P k (A ⊗[k] D) :=
    S.permutationBasis.tensorProductSMulCommClass
      T.permutationBasis
  rcases E.exists_fixedConjugate s.1 c with
    ⟨c', hcAmbient, hcBrauer⟩
  rcases F.exists_fixedConjugate s.2 d with
    ⟨d', hdAmbient, hdBrauer⟩
  refine ⟨c', d', ?_, ?_⟩
  · change
      (c' : A) ⊗ₜ[k] (d' : D) =
        (((↑(((s.1 : Aˣ)⁻¹)) : A) ⊗ₜ[k]
            (↑(((s.2 : Dˣ)⁻¹)) : D)) *
          ((c : A) ⊗ₜ[k] (d : D))) *
          ((s.1 : Aˣ) : A) ⊗ₜ[k] ((s.2 : Dˣ) : D)
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    rw [← hcAmbient, ← hdAmbient]
  · rw [← S.brauerQuotientTensorEquiv_projection_tmul T c d]
    rw [← S.brauerQuotientTensorEquiv_projection_tmul T c' d']
    rw [coe_inv_brauerNormalizerExtensionTensorProductHom]
    rw [coe_brauerNormalizerExtensionTensorProductHom]
    rw [← map_mul, ← map_mul]
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    rw [hcBrauer, hdBrauer]

end DadeAlgebra
end Representation
