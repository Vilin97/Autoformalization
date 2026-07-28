/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteTensorPermutation

/-!
# Covariance of finite tensor-permutation operators

Coordinatewise intertwining identities tensor to the corresponding
covariance identity for a finite tensor-permutation operator.  Keeping this
calculation independent of the layer coordinates makes the geometric part
of tensor-permutation constructions local.
-/

noncomputable section

open scoped TensorProduct

universe u v w

namespace McKayConjecture
namespace CharacterTriple
namespace FiniteTensorPermutationCocycle

variable {K : Type u} [Field K]
variable {A : Type v} [Group A]
variable {ι : Type w} [Fintype ι] [MulAction A ι]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {X : Type*} [Group X]

/-- A coordinatewise covariance identity tensors to covariance of the
finite tensor-permutation operator. -/
theorem operator_mul_piTensorCongr_eq_of_coordinate_covariance
    (C :
      FiniteTensorPermutationCocycle
        (K := K) (A := A) (ι := ι) V)
    (D : X →* (V ≃ₗ[K] V))
    (a : A)
    (x y : ι → X)
    (hcoordinate :
      ∀ i : ι,
        C.transport a i * D (x (a⁻¹ • i)) =
          D (y i) * C.transport a i) :
    C.operator a *
        PiTensorProduct.congr (fun i ↦ D (x i)) =
      PiTensorProduct.congr (fun i ↦ D (y i)) *
        C.operator a := by
  apply LinearEquiv.toLinearMap_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change
    C.operator a
        (PiTensorProduct.congr
          (fun i ↦ D (x i))
          (PiTensorProduct.tprod K v)) =
      PiTensorProduct.congr
          (fun i ↦ D (y i))
          (C.operator a
            (PiTensorProduct.tprod K v))
  rw [PiTensorProduct.congr_tprod,
    C.operator_tprod, C.operator_tprod,
    PiTensorProduct.congr_tprod]
  congr 1
  funext i
  exact
    DFunLike.congr_fun
      (hcoordinate i)
      (v (a⁻¹ • i))

end FiniteTensorPermutationCocycle
end CharacterTriple
end McKayConjecture
