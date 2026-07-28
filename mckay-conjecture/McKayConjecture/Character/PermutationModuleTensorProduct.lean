/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationModuleBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RepresentationTheory.Basic

/-!
# Tensor products of permutation modules

The diagonal tensor product of two permutation modules is again a
permutation module.  Its permutation basis is indexed by the product
of the two original index types.
-/

noncomputable section

open scoped TensorProduct

namespace Representation
namespace PermutationModuleBasis

variable {k P V W ι κ : Type}
variable [CommRing k] [Group P]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [DistribMulAction P W] [SMulCommClass P k W]
variable [MulAction P ι] [MulAction P κ]

variable
  (B : PermutationModuleBasis
    (k := k) (P := P) (V := V) (ι := ι))
  (C : PermutationModuleBasis
    (k := k) (P := P) (V := W) (ι := κ))

/-- The linear action underlying the diagonal tensor-product
representation. -/
def tensorProductLinearAction :
    P →* ((V ⊗[k] W) ≃ₗ[k] (V ⊗[k] W)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv
      k (V ⊗[k] W)).toMonoidHom.comp
    (B.representation.tprod C.representation).toHomUnits

/-- The diagonal action on a tensor product, obtained from the tensor
product representation. -/
@[instance_reducible]
def tensorProductDistribMulAction :
    DistribMulAction P (V ⊗[k] W) :=
  DistribMulAction.compHom
    (V ⊗[k] W) (B.tensorProductLinearAction C)

/-- The diagonal tensor-product action commutes with scalar
multiplication. -/
theorem tensorProductSMulCommClass :
    letI : DistribMulAction P (V ⊗[k] W) :=
      B.tensorProductDistribMulAction C
    SMulCommClass P k (V ⊗[k] W) := by
  letI : DistribMulAction P (V ⊗[k] W) :=
    B.tensorProductDistribMulAction C
  constructor
  intro g a x
  change
    (B.tensorProductLinearAction C g) (a • x) =
      a • (B.tensorProductLinearAction C g) x
  exact LinearEquiv.map_smul _ _ _

@[simp]
theorem tensorProduct_smul_tmul
    (g : P) (v : V) (w : W) :
    letI := B.tensorProductDistribMulAction C
    g • (v ⊗ₜ[k] w) = (g • v) ⊗ₜ[k] (g • w) := by
  change
    (B.representation.tprod C.representation) g
        (v ⊗ₜ[k] w) =
      (g • v) ⊗ₜ[k] (g • w)
  simp only [Representation.tprod_apply,
    TensorProduct.map_tmul, representation_apply]

/-- The tensor product of two permutation bases, for the diagonal
action on the tensor product. -/
def tensorProduct :
    letI : DistribMulAction P (V ⊗[k] W) :=
      B.tensorProductDistribMulAction C
    letI : SMulCommClass P k (V ⊗[k] W) :=
      B.tensorProductSMulCommClass C
    PermutationModuleBasis
      (k := k) (P := P) (V := V ⊗[k] W)
      (ι := ι × κ) := by
  letI : DistribMulAction P (V ⊗[k] W) :=
    B.tensorProductDistribMulAction C
  letI : SMulCommClass P k (V ⊗[k] W) :=
    B.tensorProductSMulCommClass C
  exact
    { basis := B.basis.tensorProduct C.basis
      smul_basis := fun g ij => by
        rw [Module.Basis.tensorProduct_apply']
        rw [B.tensorProduct_smul_tmul C]
        rw [B.smul_basis, C.smul_basis]
        rw [Module.Basis.tensorProduct_apply']
        rfl }

@[simp]
theorem tensorProduct_basis_apply
    (ij : ι × κ) :
    letI : DistribMulAction P (V ⊗[k] W) :=
      B.tensorProductDistribMulAction C
    letI : SMulCommClass P k (V ⊗[k] W) :=
      B.tensorProductSMulCommClass C
    (B.tensorProduct C).basis ij =
      B.basis ij.1 ⊗ₜ[k] C.basis ij.2 := by
  letI : DistribMulAction P (V ⊗[k] W) :=
    B.tensorProductDistribMulAction C
  letI : SMulCommClass P k (V ⊗[k] W) :=
    B.tensorProductSMulCommClass C
  simpa only [tensorProduct] using
    Module.Basis.tensorProduct_apply'
      (R := k) B.basis C.basis ij

/-- The representation attached to the tensor-product permutation
basis is the usual tensor-product representation. -/
theorem tensorProduct_representation_eq_tprod :
    letI : DistribMulAction P (V ⊗[k] W) :=
      B.tensorProductDistribMulAction C
    letI : SMulCommClass P k (V ⊗[k] W) :=
      B.tensorProductSMulCommClass C
    (B.tensorProduct C).representation =
      B.representation.tprod C.representation := by
  letI : DistribMulAction P (V ⊗[k] W) :=
    B.tensorProductDistribMulAction C
  letI : SMulCommClass P k (V ⊗[k] W) :=
    B.tensorProductSMulCommClass C
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  rfl

end PermutationModuleBasis
end Representation
