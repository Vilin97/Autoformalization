/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveRepresentation
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Trace

/-!
# Finite tensors of projective representations

A finite family of projective representations of the same group has a
projective action on its dependent tensor product.  The operator is the
tensor of the coordinate operators and its factor set is the product of the
coordinate factor sets.

This construction complements `FiniteTensorPermutation`: the latter handles
the permutation action inside one component orbit, while this file tensors
the resulting orbitwise representations together.
-/

noncomputable section

open scoped BigOperators TensorProduct

universe u v w z

namespace McKayConjecture
namespace CharacterTriple

variable {K : Type u} [Field K]
variable {A : Type v} [Group A]
variable {ι : Type w} [Fintype ι]
variable {V : ι → Type z}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

namespace ProjectiveRepresentation

/-- Tensor of the coordinate operators in a finite family of projective
representations. -/
def piTensorOperator
    (P : ∀ i, ProjectiveRepresentation K A (V i))
    (a : A) :
    (⨂[K] i, V i) ≃ₗ[K] (⨂[K] i, V i) :=
  PiTensorProduct.congr (fun i ↦ (P i).operator a)

@[simp]
theorem piTensorOperator_tprod
    (P : ∀ i, ProjectiveRepresentation K A (V i))
    (a : A) (x : ∀ i, V i) :
    piTensorOperator P a (PiTensorProduct.tprod K x) =
      PiTensorProduct.tprod K
        (fun i ↦ (P i).operator a (x i)) :=
  PiTensorProduct.congr_tprod _ _

/-- Product of the coordinate factor sets. -/
def piTensorFactor
    (P : ∀ i, ProjectiveRepresentation K A (V i))
    (a b : A) : Kˣ :=
  ∏ i, (P i).factor a b

@[simp]
theorem piTensorFactor_coe
    (P : ∀ i, ProjectiveRepresentation K A (V i))
    (a b : A) :
    ((piTensorFactor P a b : Kˣ) : K) =
      ∏ i, (((P i).factor a b : Kˣ) : K) := by
  simp [piTensorFactor]

/-- The tensor operators satisfy the projective multiplication law with
factor equal to the product of the coordinate factors. -/
theorem piTensorOperator_mul
    (P : ∀ i, ProjectiveRepresentation K A (V i))
    (a b : A) :
    piTensorOperator P a * piTensorOperator P b =
      scalarLinearEquiv K (⨂[K] i, V i)
          (piTensorFactor P a b) *
        piTensorOperator P (a * b) := by
  apply LinearEquiv.toLinearMap_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change
    piTensorOperator P a
        (piTensorOperator P b (PiTensorProduct.tprod K x)) =
      scalarLinearEquiv K (⨂[K] i, V i)
          (piTensorFactor P a b)
        (piTensorOperator P (a * b)
          (PiTensorProduct.tprod K x))
  rw [piTensorOperator_tprod, piTensorOperator_tprod,
    piTensorOperator_tprod, scalarLinearEquiv_apply]
  have hcoordinate :
      ∀ i,
        (P i).operator a ((P i).operator b (x i)) =
          (((P i).factor a b : Kˣ) : K) •
            (P i).operator (a * b) (x i) := by
    intro i
    have h :=
      DFunLike.congr_fun ((P i).map_mul a b) (x i)
    simpa only [LinearEquiv.mul_apply,
      scalarLinearEquiv_apply] using h
  simp_rw [hcoordinate]
  rw [(PiTensorProduct.tprod K).map_smul_univ]
  simp only [piTensorFactor_coe]

/-- The projective representation on the finite dependent tensor product. -/
def piTensor
    (P : ∀ i, ProjectiveRepresentation K A (V i)) :
    ProjectiveRepresentation K A (⨂[K] i, V i) where
  operator := piTensorOperator P
  factor := piTensorFactor P
  map_mul := piTensorOperator_mul P

@[simp]
theorem piTensor_operator
    (P : ∀ i, ProjectiveRepresentation K A (V i))
    (a : A) :
    (piTensor P).operator a = piTensorOperator P a :=
  rfl

@[simp]
theorem piTensor_factor
    (P : ∀ i, ProjectiveRepresentation K A (V i))
    (a b : A) :
    (piTensor P).factor a b =
      ∏ i, (P i).factor a b :=
  rfl

/-- Finite dimensionality of a finite dependent tensor product, bundled in a
form convenient for constructing complete projective lifts. -/
theorem piTensorModuleFinite
    [∀ i, Module.Finite K (V i)] :
    Module.Finite K (⨂[K] i, V i) := by
  let b :=
    fun i ↦ Module.Free.chooseBasis K (V i)
  letI : ∀ i, Finite (Module.Free.ChooseBasisIndex K (V i)) :=
    fun i ↦ Module.Finite.finite_basis (b i)
  exact Module.Finite.of_basis (Basis.piTensorProduct b)

/-- The dimension of a finite dependent tensor product is the product of
the dimensions of its factors. -/
theorem piTensor_finrank
    [∀ i, Module.Finite K (V i)] :
    Module.finrank K (⨂[K] i, V i) =
      ∏ i, Module.finrank K (V i) := by
  classical
  let b :=
    fun i ↦ Module.Free.chooseBasis K (V i)
  letI : ∀ i, Fintype (Module.Free.ChooseBasisIndex K (V i)) :=
    fun i ↦ Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis (Basis.piTensorProduct b),
    Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact (Module.finrank_eq_card_basis (b i)).symm

/-- The trace of a finite dependent tensor of endomorphisms is the product
of the coordinate traces. -/
theorem trace_piTensorMap
    [∀ i, Module.Finite K (V i)]
    (f : ∀ i, V i →ₗ[K] V i) :
    LinearMap.trace K (⨂[K] i, V i) (PiTensorProduct.map f) =
      ∏ i, LinearMap.trace K (V i) (f i) := by
  classical
  let b :=
    fun i ↦ Module.Free.chooseBasis K (V i)
  letI : ∀ i, Fintype (Module.Free.ChooseBasisIndex K (V i)) :=
    fun i ↦ Fintype.ofFinite _
  rw [LinearMap.trace_eq_matrix_trace K
    (Basis.piTensorProduct b)]
  simp only [Matrix.trace, Matrix.diag_apply,
    LinearMap.toMatrix_apply]
  simp_rw [Basis.piTensorProduct_apply,
    PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  simp_rw [LinearMap.trace_eq_matrix_trace K (b _),
    Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  exact
    (Fintype.prod_sum
      (fun i j ↦ (b i).repr (f i (b i j)) j)).symm

/-- The trace formula specialized to a dependent tensor of linear
equivalences. -/
theorem trace_piTensorCongr
    [∀ i, Module.Finite K (V i)]
    (f : ∀ i, V i ≃ₗ[K] V i) :
    LinearMap.trace K (⨂[K] i, V i)
        (PiTensorProduct.congr f) =
      ∏ i, LinearMap.trace K (V i) (f i) := by
  exact trace_piTensorMap (fun i ↦ (f i : V i →ₗ[K] V i))

/-- Character formula for a finite tensor of projective operators. -/
theorem trace_piTensorOperator
    [∀ i, Module.Finite K (V i)]
    (P : ∀ i, ProjectiveRepresentation K A (V i))
    (a : A) :
    LinearMap.trace K (⨂[K] i, V i)
        (piTensorOperator P a) =
      ∏ i, LinearMap.trace K (V i) ((P i).operator a) := by
  exact trace_piTensorCongr (fun i ↦ (P i).operator a)

/-- The ordinary action on a dependent tensor product obtained from
independent coordinate actions of a dependent product of groups. -/
def piTensorLinearAction
    {X : ι → Type*} [∀ i, Group (X i)]
    (D : ∀ i, X i →* (V i ≃ₗ[K] V i)) :
    (∀ i, X i) →* ((⨂[K] i, V i) ≃ₗ[K] (⨂[K] i, V i)) where
  toFun x :=
    PiTensorProduct.congr (fun i ↦ D i (x i))
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp
  map_mul' := by
    intro x y
    apply LinearEquiv.toLinearMap_injective
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp

omit [Fintype ι] in
@[simp]
theorem piTensorLinearAction_tprod
    {X : ι → Type*} [∀ i, Group (X i)]
    (D : ∀ i, X i →* (V i ≃ₗ[K] V i))
    (x : ∀ i, X i) (v : ∀ i, V i) :
    piTensorLinearAction D x (PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K (fun i ↦ D i (x i) (v i)) :=
  PiTensorProduct.congr_tprod _ _

/-- Character formula for the ordinary dependent tensor action. -/
theorem trace_piTensorLinearAction
    [∀ i, Module.Finite K (V i)]
    {X : ι → Type*} [∀ i, Group (X i)]
    (D : ∀ i, X i →* (V i ≃ₗ[K] V i))
    (x : ∀ i, X i) :
    LinearMap.trace K (⨂[K] i, V i)
        (piTensorLinearAction D x) =
      ∏ i, LinearMap.trace K (V i) (D i (x i)) := by
  exact trace_piTensorMap
    (fun i ↦ (D i (x i) : V i →ₗ[K] V i))

/-- A finite dependent tensor product of nonzero vector spaces is nonzero. -/
theorem piTensorNontrivial
    [∀ i, Nontrivial (V i)] :
    Nontrivial (⨂[K] i, V i) := by
  let b :=
    fun i ↦ Module.Free.chooseBasis K (V i)
  let j : ∀ i, Module.Free.ChooseBasisIndex K (V i) :=
    fun i ↦ Classical.choice inferInstance
  let B := Basis.piTensorProduct b
  exact ⟨B j, 0, B.ne_zero j⟩

end ProjectiveRepresentation

end CharacterTriple
end McKayConjecture
