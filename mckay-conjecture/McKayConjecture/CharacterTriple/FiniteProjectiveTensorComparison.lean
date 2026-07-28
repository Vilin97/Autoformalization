/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteProjectiveTensor

/-!
# Comparison of finite tensors of projective representations

Coordinatewise factor agreement gives exact factor agreement after tensoring
a finite family of projective representations.  Coordinatewise common scalar
actions likewise multiply to a common scalar action on the two full tensor
products.
-/

noncomputable section

open scoped BigOperators TensorProduct

universe u v w z z'

namespace McKayConjecture
namespace CharacterTriple

variable {K : Type u} [Field K]
variable {A : Type v} [Group A]
variable {ι : Type w} [Fintype ι]
variable {V : ι → Type z} {W : ι → Type z'}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

namespace ProjectiveRepresentation

/-- Coordinatewise equality of factor sets for two finite projective
families. -/
structure PiTensorAgreement
    (P : ∀ i, ProjectiveRepresentation K A (V i))
    (Q : ∀ i, ProjectiveRepresentation K A (W i)) : Prop where
  /-- Equality of the two factors in each coordinate. -/
  factor_eq :
    ∀ (i : ι) (a b : A),
      (P i).factor a b = (Q i).factor a b

namespace PiTensorAgreement

variable
  {P : ∀ i, ProjectiveRepresentation K A (V i)}
  {Q : ∀ i, ProjectiveRepresentation K A (W i)}

/-- Coordinatewise factor equality gives equality of the product factors. -/
theorem piTensor_factor_eq
    (E : PiTensorAgreement P Q)
    (a b : A) :
    (piTensor P).factor a b =
      (piTensor Q).factor a b := by
  simp only [piTensor_factor]
  apply Finset.prod_congr rfl
  intro i _
  exact E.factor_eq i a b

end PiTensorAgreement

/-- Coordinatewise scalar action for a finite family of projective
representations. -/
def PiTensorHasCoordinateScalarAction
    (P : ∀ i, ProjectiveRepresentation K A (V i))
    (a : A) (c : ι → Kˣ) : Prop :=
  ∀ i,
    (P i).operator a =
      scalarLinearEquiv K (V i) (c i)

/-- Coordinate scalars multiply to the scalar of the full tensor operator. -/
theorem piTensorOperator_eq_scalar
    (P : ∀ i, ProjectiveRepresentation K A (V i))
    {a : A} {c : ι → Kˣ}
    (h : PiTensorHasCoordinateScalarAction P a c) :
    (piTensor P).operator a =
      scalarLinearEquiv K (⨂[K] i, V i) (∏ i, c i) := by
  apply LinearEquiv.toLinearMap_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change
    piTensorOperator P a (PiTensorProduct.tprod K x) =
      scalarLinearEquiv K (⨂[K] i, V i)
        (∏ i, c i) (PiTensorProduct.tprod K x)
  rw [piTensorOperator_tprod, scalarLinearEquiv_apply]
  have hfamily :
      (fun i ↦ (P i).operator a (x i)) =
        (fun i ↦ (c i : K) • x i) := by
    funext i
    rw [h i, scalarLinearEquiv_apply]
  rw [hfamily, (PiTensorProduct.tprod K).map_smul_univ]
  simp

/-- Common coordinate scalar data for two finite projective families. -/
structure PiTensorCommonScalar
    (P : ∀ i, ProjectiveRepresentation K A (V i))
    (Q : ∀ i, ProjectiveRepresentation K A (W i))
    (a : A) where
  /-- The common scalar in every coordinate. -/
  scalar : ι → Kˣ
  /-- Scalar action in the first family. -/
  left :
    PiTensorHasCoordinateScalarAction P a scalar
  /-- Scalar action in the second family. -/
  right :
    PiTensorHasCoordinateScalarAction Q a scalar

namespace PiTensorCommonScalar

variable
  {P : ∀ i, ProjectiveRepresentation K A (V i)}
  {Q : ∀ i, ProjectiveRepresentation K A (W i)}
  {a : A}

/-- Common coordinate scalars give one common product scalar for the two
finite tensor operators. -/
theorem operator_agreement
    (h : PiTensorCommonScalar P Q a) :
    ∃ z : Kˣ,
      (piTensor P).operator a =
          scalarLinearEquiv K (⨂[K] i, V i) z ∧
        (piTensor Q).operator a =
          scalarLinearEquiv K (⨂[K] i, W i) z := by
  refine ⟨∏ i, h.scalar i, ?_, ?_⟩
  · exact piTensorOperator_eq_scalar P h.left
  · exact piTensorOperator_eq_scalar Q h.right

end PiTensorCommonScalar

end ProjectiveRepresentation

end CharacterTriple
end McKayConjecture
