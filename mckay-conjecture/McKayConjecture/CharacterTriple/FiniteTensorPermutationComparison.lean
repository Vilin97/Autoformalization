/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteTensorPermutation

/-!
# Comparison of finite tensor-permutation projective representations

Coordinatewise equality of the projective transport factors implies equality
of the factor sets of the assembled tensor-permutation representations.

For an element acting trivially on the coordinate set, coordinatewise common
scalar actions imply a common scalar action on the two full tensor products.
The global scalar is the product of the coordinate scalars.  This is the
sound centralizer calculation for the layer construction: an element
centralizing the layer fixes every component, whereas a general inertia
element may permute all components and must be handled by the full
tensor-permutation operator.
-/

noncomputable section

open scoped BigOperators TensorProduct

universe u v w

namespace McKayConjecture
namespace CharacterTriple

variable {K : Type u} [Field K]
variable {A : Type v} [Group A]
variable {ι : Type w} [Fintype ι] [MulAction A ι]
variable {V W : Type*}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- Coordinatewise comparison data for two tensor-permutation cocycles on
the same permuted coordinate set. -/
structure FiniteTensorPermutationCocycleAgreement
    (C : FiniteTensorPermutationCocycle
      (K := K) (A := A) (ι := ι) V)
    (D : FiniteTensorPermutationCocycle
      (K := K) (A := A) (ι := ι) W) : Prop where
  /-- The local projective factors agree in every coordinate. -/
  factor_eq :
    ∀ (a b : A) (i : ι),
      C.factor a b i = D.factor a b i

namespace FiniteTensorPermutationCocycleAgreement

variable
  {C : FiniteTensorPermutationCocycle
    (K := K) (A := A) (ι := ι) V}
  {D : FiniteTensorPermutationCocycle
    (K := K) (A := A) (ι := ι) W}

/-- Equality of all coordinate factors gives equality of the assembled
factor sets. -/
theorem globalFactor_eq
    (E : FiniteTensorPermutationCocycleAgreement C D)
    (a b : A) :
    C.globalFactor a b = D.globalFactor a b := by
  simp only [FiniteTensorPermutationCocycle.globalFactor]
  apply Finset.prod_congr rfl
  intro i _
  exact E.factor_eq a b i

/-- The two assembled projective representations have exactly equal factor
sets. -/
theorem projective_factor_eq
    (E : FiniteTensorPermutationCocycleAgreement C D)
    (a b : A) :
    C.projectiveRepresentation.factor a b =
      D.projectiveRepresentation.factor a b :=
  E.globalFactor_eq a b

end FiniteTensorPermutationCocycleAgreement

namespace FiniteTensorPermutationCocycle

variable
  (C : FiniteTensorPermutationCocycle
    (K := K) (A := A) (ι := ι) V)

/-- An element has a coordinatewise scalar action if it fixes every
coordinate and each coordinate transport is scalar. -/
def HasCoordinateScalarAction (a : A) (c : ι → Kˣ) : Prop :=
  (∀ i : ι, a • i = i) ∧
    ∀ i : ι,
      C.transport a i = scalarLinearEquiv K V (c i)

/-- Coordinatewise scalar action assembles to the product scalar on the
full tensor product. -/
theorem operator_eq_scalar_of_hasCoordinateScalarAction
    {a : A} {c : ι → Kˣ}
    (h : C.HasCoordinateScalarAction a c) :
    C.operator a =
      scalarLinearEquiv K (⨂[K] _i : ι, V) (∏ i, c i) := by
  obtain ⟨hfixed, hscalar⟩ := h
  apply LinearEquiv.toLinearMap_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change
    C.operator a (PiTensorProduct.tprod K x) =
      scalarLinearEquiv K (⨂[K] _i : ι, V)
        (∏ i, c i) (PiTensorProduct.tprod K x)
  rw [C.operator_tprod, scalarLinearEquiv_apply]
  have hinv : ∀ i : ι, a⁻¹ • i = i := by
    intro i
    calc
      a⁻¹ • i = a⁻¹ • (a • i) := by rw [hfixed i]
      _ = i := inv_smul_smul a i
  have hfamily :
      (fun i => C.transport a i (x (a⁻¹ • i))) =
        (fun i => (c i : K) • x i) := by
    funext i
    rw [hinv i, hscalar i, scalarLinearEquiv_apply]
  rw [hfamily]
  rw [(PiTensorProduct.tprod K).map_smul_univ]
  simp

end FiniteTensorPermutationCocycle

/-- Common coordinate scalar data for a pair of tensor-permutation
cocycles. -/
structure FiniteTensorPermutationCommonScalar
    (C : FiniteTensorPermutationCocycle
      (K := K) (A := A) (ι := ι) V)
    (D : FiniteTensorPermutationCocycle
      (K := K) (A := A) (ι := ι) W)
    (a : A) where
  /-- The common coordinate scalar family. -/
  scalar : ι → Kˣ
  /-- Scalar action of the source coordinate transports. -/
  source :
    C.HasCoordinateScalarAction a scalar
  /-- Scalar action of the target coordinate transports. -/
  target :
    D.HasCoordinateScalarAction a scalar

namespace FiniteTensorPermutationCommonScalar

variable
  {C : FiniteTensorPermutationCocycle
    (K := K) (A := A) (ι := ι) V}
  {D : FiniteTensorPermutationCocycle
    (K := K) (A := A) (ι := ι) W}
  {a : A}

/-- A common scalar on every coordinate gives the same product scalar on
the two assembled tensor-permutation operators. -/
theorem operator_agreement
    (h : FiniteTensorPermutationCommonScalar C D a) :
    ∃ z : Kˣ,
      C.operator a =
          scalarLinearEquiv K (⨂[K] _i : ι, V) z ∧
        D.operator a =
          scalarLinearEquiv K (⨂[K] _i : ι, W) z := by
  refine ⟨∏ i, h.scalar i, ?_, ?_⟩
  · exact C.operator_eq_scalar_of_hasCoordinateScalarAction h.source
  · exact D.operator_eq_scalar_of_hasCoordinateScalarAction h.target

end FiniteTensorPermutationCommonScalar

end CharacterTriple
end McKayConjecture
