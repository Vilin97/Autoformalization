/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveRepresentation
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Finite tensor-permutation projective representations

Let a group `A` permute a finite set `ι`.  Suppose that for every `a : A`
and coordinate `i` we have an invertible linear transport

`V (a⁻¹ • i) ≃ₗ V i`.

If two successive transports differ from the transport for the product by
a coordinate scalar, then reindexing a dependent tensor product and applying
all coordinate transports gives a projective representation of `A`.  Its
factor set is the product of the coordinate factors.

This is the algebraic tensor-permutation construction needed in the layer
reduction.  In particular, it handles elements which permute every component;
it does not require such an element to lie in a chart stabilizing one chosen
coordinate.
-/

noncomputable section

open scoped BigOperators TensorProduct

universe u v w

namespace McKayConjecture
namespace CharacterTriple

variable {K : Type u} [Field K]
variable {A : Type v} [Group A]
variable {ι : Type w} [Fintype ι] [MulAction A ι]
variable (V : Type*)
variable [AddCommGroup V] [Module K V]

/-- Coordinate transports, together with their projective multiplication
law, for a group permuting a finite family of vector spaces. -/
structure FiniteTensorPermutationCocycle where
  /-- Transport from the coordinate moved into `i` to coordinate `i`. -/
  transport :
    A → ι → V ≃ₗ[K] V
  /-- Scalar discrepancy in the coordinate transport law. -/
  factor : A → A → ι → Kˣ
  /-- Successive coordinate transports multiply projectively. -/
  transport_mul :
    ∀ (a b : A) (i : ι),
      transport a i * transport b (a⁻¹ • i) =
        scalarLinearEquiv K V (factor a b i) *
          transport (a * b) i

namespace FiniteTensorPermutationCocycle

variable {V}

/-- The permutation of coordinates induced by a group element, presented
with inverse action as a definition so dependent tensor reindexing has the
expected coordinate family without casts. -/
def coordinatePermutation (a : A) : ι ≃ ι where
  toFun i := a • i
  invFun i := a⁻¹ • i
  left_inv i := inv_smul_smul a i
  right_inv i := smul_inv_smul a i

@[simp]
theorem coordinatePermutation_apply (a : A) (i : ι) :
    coordinatePermutation (A := A) a i = a • i :=
  rfl

@[simp]
theorem coordinatePermutation_symm_apply (a : A) (i : ι) :
    (coordinatePermutation (A := A) a).symm i = a⁻¹ • i :=
  rfl

/-- Reindex the tensor factors and then apply all coordinate transports. -/
def operator
    (C : FiniteTensorPermutationCocycle (K := K) (A := A) (ι := ι) V)
    (a : A) :
    (⨂[K] _i : ι, V) ≃ₗ[K] (⨂[K] _i : ι, V) :=
  (PiTensorProduct.reindex K (fun _i : ι ↦ V)
      (coordinatePermutation (A := A) a)).trans
    (PiTensorProduct.congr (C.transport a))

@[simp]
theorem operator_tprod
    (C : FiniteTensorPermutationCocycle (K := K) (A := A) (ι := ι) V)
    (a : A) (x : ι → V) :
    C.operator a (PiTensorProduct.tprod K x) =
      PiTensorProduct.tprod K
        (fun i ↦ C.transport a i (x (a⁻¹ • i))) := by
  rw [operator, LinearEquiv.trans_apply,
    PiTensorProduct.reindex_tprod]
  simp only [coordinatePermutation_symm_apply,
    PiTensorProduct.congr_tprod]

/-- The global factor is the product of all coordinate factors. -/
def globalFactor
    (C : FiniteTensorPermutationCocycle (K := K) (A := A) (ι := ι) V)
    (a b : A) : Kˣ :=
  ∏ i, C.factor a b i

@[simp]
theorem globalFactor_coe
    (C : FiniteTensorPermutationCocycle (K := K) (A := A) (ι := ι) V)
    (a b : A) :
    ((C.globalFactor a b : Kˣ) : K) =
      ∏ i, ((C.factor a b i : Kˣ) : K) := by
  simp [globalFactor]

/-- Tensor-permutation operators satisfy the projective multiplication law. -/
theorem operator_mul
    (C : FiniteTensorPermutationCocycle (K := K) (A := A) (ι := ι) V)
    (a b : A) :
    C.operator a * C.operator b =
      scalarLinearEquiv K (⨂[K] _i : ι, V)
          (C.globalFactor a b) *
        C.operator (a * b) := by
  apply LinearEquiv.toLinearMap_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change
    C.operator a
        (C.operator b (PiTensorProduct.tprod K x)) =
      scalarLinearEquiv K (⨂[K] _i : ι, V)
          (C.globalFactor a b)
        (C.operator (a * b) (PiTensorProduct.tprod K x))
  rw [C.operator_tprod, C.operator_tprod,
    C.operator_tprod, scalarLinearEquiv_apply]
  have hindex :
      ∀ i : ι,
        b⁻¹ • (a⁻¹ • i) = (a * b)⁻¹ • i := by
    intro i
    rw [mul_inv_rev, mul_smul]
  have hcoordinate :
      ∀ i : ι,
        C.transport a i
            (C.transport b (a⁻¹ • i)
              (x (b⁻¹ • (a⁻¹ • i)))) =
          ((C.factor a b i : Kˣ) : K) •
            C.transport (a * b) i
              (x ((a * b)⁻¹ • i)) := by
    intro i
    have h :=
      DFunLike.congr_fun (C.transport_mul a b i)
        (x (b⁻¹ • (a⁻¹ • i)))
    rw [← hindex i]
    simpa only [LinearEquiv.mul_apply,
      scalarLinearEquiv_apply] using h
  simp_rw [hcoordinate]
  rw [(PiTensorProduct.tprod K).map_smul_univ]
  simp only [globalFactor_coe]

/-- The projective representation obtained from a finite coordinate
cocycle. -/
def projectiveRepresentation
    (C : FiniteTensorPermutationCocycle (K := K) (A := A) (ι := ι) V) :
    ProjectiveRepresentation K A (⨂[K] _i : ι, V) where
  operator := C.operator
  factor := C.globalFactor
  map_mul := C.operator_mul

@[simp]
theorem projectiveRepresentation_operator
    (C : FiniteTensorPermutationCocycle (K := K) (A := A) (ι := ι) V)
    (a : A) :
    C.projectiveRepresentation.operator a = C.operator a :=
  rfl

@[simp]
theorem projectiveRepresentation_factor
    (C : FiniteTensorPermutationCocycle (K := K) (A := A) (ι := ι) V)
    (a b : A) :
    C.projectiveRepresentation.factor a b =
      ∏ i, C.factor a b i :=
  rfl

end FiniteTensorPermutationCocycle

end CharacterTriple
end McKayConjecture
