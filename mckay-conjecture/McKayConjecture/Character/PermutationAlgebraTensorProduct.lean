/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationAlgebraBrauerQuotientBasis
import McKayConjecture.Character.PermutationModuleTensorProduct
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor products of permutation algebras

The diagonal tensor product of two permutation algebras is again a
permutation algebra.  If the two bases contain their algebra units,
the tensor-product basis contains the tensor-product unit.
-/

noncomputable section

open scoped TensorProduct

namespace Representation
namespace PointedPermutationAlgebraBasis

variable {k P A D : Type}
variable [Field k] [Group P]
variable [Ring A] [Algebra k A]
variable [Ring D] [Algebra k D]
variable [MulSemiringAction P A] [SMulCommClass P k A]
variable [MulSemiringAction P D] [SMulCommClass P k D]

variable
  (B : PointedPermutationAlgebraBasis
    (k := k) (P := P) (A := A))
  (C : PointedPermutationAlgebraBasis
    (k := k) (P := P) (A := D))

/-- The diagonal permutation action on the product of the two basis
index types. -/
def tensorProductIndexAction :
    P →* Equiv.Perm (B.index × C.index) where
  toFun g := Equiv.prodCongr (B.indexAction g) (C.indexAction g)
  map_one' := by
    apply _root_.Equiv.ext
    intro i
    simp
  map_mul' g h := by
    apply _root_.Equiv.ext
    intro i
    simp
    rfl

/-- The diagonal tensor-product action preserves multiplication and
the algebra unit. -/
@[instance_reducible]
def tensorProductMulSemiringAction :
    MulSemiringAction P (A ⊗[k] D) := by
  letI : MulAction P B.index :=
    indexMulAction (B := B)
  letI : MulAction P C.index :=
    indexMulAction (B := C)
  let U := toPermutationModuleBasis (B := B)
  let W := toPermutationModuleBasis (B := C)
  letI : DistribMulAction P (A ⊗[k] D) :=
    U.tensorProductDistribMulAction W
  refine
    { toDistribMulAction :=
        U.tensorProductDistribMulAction W
      smul_one := ?_
      smul_mul := ?_ }
  · intro g
    rw [Algebra.TensorProduct.one_def]
    rw [U.tensorProduct_smul_tmul W]
    rw [smul_one, smul_one]
  · intro g x y
    induction x using TensorProduct.induction_on with
    | zero =>
        simp
    | tmul a d =>
        induction y using TensorProduct.induction_on with
        | zero =>
            simp
        | tmul a' d' =>
            rw [Algebra.TensorProduct.tmul_mul_tmul]
            rw [U.tensorProduct_smul_tmul W]
            rw [U.tensorProduct_smul_tmul W]
            rw [U.tensorProduct_smul_tmul W]
            rw [Algebra.TensorProduct.tmul_mul_tmul]
            rw [MulSemiringAction.smul_mul,
              MulSemiringAction.smul_mul]
        | add y z hy hz =>
            simp only [mul_add, smul_add, hy, hz]
    | add x z hx hz =>
        simp only [add_mul, smul_add, hx, hz]

/-- Scalar multiplication commutes with the diagonal tensor-product
action. -/
theorem tensorProductSMulCommClass :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    SMulCommClass P k (A ⊗[k] D) := by
  letI : MulAction P B.index :=
    indexMulAction (B := B)
  letI : MulAction P C.index :=
    indexMulAction (B := C)
  let U := toPermutationModuleBasis (B := B)
  let W := toPermutationModuleBasis (B := C)
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  exact U.tensorProductSMulCommClass W

@[simp]
theorem tensorProduct_smul_tmul
    (g : P) (a : A) (d : D) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    g • (a ⊗ₜ[k] d) = (g • a) ⊗ₜ[k] (g • d) := by
  letI : MulAction P B.index :=
    indexMulAction (B := B)
  letI : MulAction P C.index :=
    indexMulAction (B := C)
  let U := toPermutationModuleBasis (B := B)
  let W := toPermutationModuleBasis (B := C)
  exact U.tensorProduct_smul_tmul W g a d

/-- The pointed permutation basis on the diagonal tensor-product
algebra. -/
def tensorProduct :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    PointedPermutationAlgebraBasis
      (k := k) (P := P) (A := A ⊗[k] D) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  exact
    { index := B.index × C.index
      indexAction := B.tensorProductIndexAction C
      basis := B.basis.tensorProduct C.basis
      smul_basis := fun g i => by
        rw [Module.Basis.tensorProduct_apply']
        rw [B.tensorProduct_smul_tmul C]
        rw [B.smul_basis, C.smul_basis]
        rw [Module.Basis.tensorProduct_apply']
        rfl
      oneIndex := (B.oneIndex, C.oneIndex)
      basis_oneIndex := by
        rw [Module.Basis.tensorProduct_apply']
        rw [B.basis_oneIndex, C.basis_oneIndex]
        exact Algebra.TensorProduct.one_def.symm }

@[simp]
theorem tensorProduct_basis_apply
    (i : B.index × C.index) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    (B.tensorProduct C).basis i =
      B.basis i.1 ⊗ₜ[k] C.basis i.2 := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  change
    (B.basis.tensorProduct C.basis) i =
      B.basis i.1 ⊗ₜ[k] C.basis i.2
  exact
    Module.Basis.tensorProduct_apply'
      (R := k) B.basis C.basis i

end PointedPermutationAlgebraBasis
end Representation
