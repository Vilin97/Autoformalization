/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.SpherePolarProduct
public import SplittingSpheres.Handlebody.SphereHandleDecomposition

/-!
# Aligning the direct sphere-handle decomposition with the standard unlink

The direct decomposition of `SphereHandleDecomposition.lean` splits ambient coordinates as
`(x₀,x₁) ⊕ (x₂,x₃,x₄)`.  The standard unlink instead uses `(x₃,x₄)` as its
normal plane.  This file applies the orthogonal coordinate permutation

`(x₀,x₁,x₂,x₃,x₄) ↦ (x₂,x₃,x₄,x₀,x₁)`

to the direct decomposition.  The aligned cap disk is then literally the last-two-coordinate
normal disk, while its sphere factor occupies the first three coordinates.

Everything here remains topological.  No smooth gluing or handlebody identification is asserted.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped Topology

namespace SplittingSpheres

/-- The explicit cyclic permutation of ambient Euclidean coordinates. -/
def unlinkAlignedAmbientMap (x : SphereHandleAmbient) : SphereHandleAmbient :=
  WithLp.toLp 2 ![x 2, x 3, x 4, x 0, x 1]

/-- The explicit inverse coordinate permutation. -/
def unlinkAlignedAmbientInverseMap (x : SphereHandleAmbient) : SphereHandleAmbient :=
  WithLp.toLp 2 ![x 3, x 4, x 0, x 1, x 2]

theorem norm_unlinkAlignedAmbientMap (x : SphereHandleAmbient) :
    ‖unlinkAlignedAmbientMap x‖ = ‖x‖ := by
  have hsq : ‖unlinkAlignedAmbientMap x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp [unlinkAlignedAmbientMap, Fin.sum_univ_succ]
    ring
  nlinarith [norm_nonneg (unlinkAlignedAmbientMap x), norm_nonneg x]

/-- The coordinate permutation as an orthogonal linear equivalence. -/
def unlinkAlignedAmbientEquiv :
    SphereHandleAmbient ≃ₗᵢ[ℝ] SphereHandleAmbient where
  toFun := unlinkAlignedAmbientMap
  invFun := unlinkAlignedAmbientInverseMap
  left_inv x := by
    ext i
    fin_cases i <;> rfl
  right_inv x := by
    ext i
    fin_cases i <;> rfl
  map_add' x y := by
    ext i
    fin_cases i <;> simp [unlinkAlignedAmbientMap]
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [unlinkAlignedAmbientMap]
  norm_map' := norm_unlinkAlignedAmbientMap

@[simp] theorem unlinkAlignedAmbientEquiv_apply_zero (x : SphereHandleAmbient) :
    unlinkAlignedAmbientEquiv x 0 = x 2 := rfl

@[simp] theorem unlinkAlignedAmbientEquiv_apply_one (x : SphereHandleAmbient) :
    unlinkAlignedAmbientEquiv x 1 = x 3 := rfl

@[simp] theorem unlinkAlignedAmbientEquiv_apply_two (x : SphereHandleAmbient) :
    unlinkAlignedAmbientEquiv x 2 = x 4 := rfl

@[simp] theorem unlinkAlignedAmbientEquiv_apply_three (x : SphereHandleAmbient) :
    unlinkAlignedAmbientEquiv x 3 = x 0 := rfl

@[simp] theorem unlinkAlignedAmbientEquiv_apply_four (x : SphereHandleAmbient) :
    unlinkAlignedAmbientEquiv x 4 = x 1 := rfl

@[simp] theorem unlinkAlignedAmbientEquiv_symm_apply_zero (x : SphereHandleAmbient) :
    unlinkAlignedAmbientEquiv.symm x 0 = x 3 := rfl

@[simp] theorem unlinkAlignedAmbientEquiv_symm_apply_one (x : SphereHandleAmbient) :
    unlinkAlignedAmbientEquiv.symm x 1 = x 4 := rfl

@[simp] theorem unlinkAlignedAmbientEquiv_symm_apply_two (x : SphereHandleAmbient) :
    unlinkAlignedAmbientEquiv.symm x 2 = x 0 := rfl

@[simp] theorem unlinkAlignedAmbientEquiv_symm_apply_three (x : SphereHandleAmbient) :
    unlinkAlignedAmbientEquiv.symm x 3 = x 1 := rfl

@[simp] theorem unlinkAlignedAmbientEquiv_symm_apply_four (x : SphereHandleAmbient) :
    unlinkAlignedAmbientEquiv.symm x 4 = x 2 := rfl

/-- Restriction of the coordinate permutation to the ambient unit four-sphere. -/
def unlinkAlignedSphereHomeomorph : Sphere 4 ≃ₜ Sphere 4 where
  toFun q := ⟨unlinkAlignedAmbientEquiv q.1, by
    rw [mem_sphere_zero_iff_norm, unlinkAlignedAmbientEquiv.norm_map]
    exact mem_sphere_zero_iff_norm.mp q.2⟩
  invFun q := ⟨unlinkAlignedAmbientEquiv.symm q.1, by
    rw [mem_sphere_zero_iff_norm, unlinkAlignedAmbientEquiv.symm.norm_map]
    exact mem_sphere_zero_iff_norm.mp q.2⟩
  left_inv q := by
    apply Subtype.ext
    exact unlinkAlignedAmbientEquiv.symm_apply_apply q.1
  right_inv q := by
    apply Subtype.ext
    exact unlinkAlignedAmbientEquiv.apply_symm_apply q.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact unlinkAlignedAmbientEquiv.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact unlinkAlignedAmbientEquiv.symm.continuous.comp continuous_subtype_val

@[simp] theorem unlinkAlignedSphereHomeomorph_coe (q : Sphere 4) :
    (unlinkAlignedSphereHomeomorph q : SphereHandleAmbient) =
      unlinkAlignedAmbientEquiv q.1 := by
  change unlinkAlignedAmbientEquiv q.1 = _
  rfl

@[simp] theorem unlinkAlignedSphereHomeomorph_symm_coe (q : Sphere 4) :
    (unlinkAlignedSphereHomeomorph.symm q : SphereHandleAmbient) =
      unlinkAlignedAmbientEquiv.symm q.1 := by
  change unlinkAlignedAmbientEquiv.symm q.1 = _
  rfl

/-- The aligned coordinate splitting.  Its first block is `(x₃,x₄)` and its second block
is `(x₀,x₁,x₂)`. -/
def unlinkAlignedSplitEquiv :
    SphereHandleAmbient ≃L[ℝ] SphereHandleFirst × SphereHandleSecond :=
  unlinkAlignedAmbientEquiv.symm.toContinuousLinearEquiv.trans sphereHandleSplitEquiv

@[simp] theorem unlinkAlignedSplitEquiv_apply_fst_zero (x : SphereHandleAmbient) :
    (unlinkAlignedSplitEquiv x).1 0 = x 3 := rfl

@[simp] theorem unlinkAlignedSplitEquiv_apply_fst_one (x : SphereHandleAmbient) :
    (unlinkAlignedSplitEquiv x).1 1 = x 4 := rfl

@[simp] theorem unlinkAlignedSplitEquiv_apply_snd_zero (x : SphereHandleAmbient) :
    (unlinkAlignedSplitEquiv x).2 0 = x 0 := rfl

@[simp] theorem unlinkAlignedSplitEquiv_apply_snd_one (x : SphereHandleAmbient) :
    (unlinkAlignedSplitEquiv x).2 1 = x 1 := rfl

@[simp] theorem unlinkAlignedSplitEquiv_apply_snd_two (x : SphereHandleAmbient) :
    (unlinkAlignedSplitEquiv x).2 2 = x 2 := rfl

@[simp] theorem unlinkAlignedSplitEquiv_unlinkAlignedAmbientEquiv
    (x : SphereHandleAmbient) :
    unlinkAlignedSplitEquiv (unlinkAlignedAmbientEquiv x) = sphereHandleSplitEquiv x := by
  change sphereHandleSplitEquiv
      (unlinkAlignedAmbientEquiv.symm (unlinkAlignedAmbientEquiv x)) = _
  rw [unlinkAlignedAmbientEquiv.symm_apply_apply]

/-- Projection to the first three, tangential coordinates of the standard unlink. -/
def standardUnlinkTangentialProjection (q : Sphere 4) : SphereHandleSecond :=
  WithLp.toLp 2 ![q.1 0, q.1 1, q.1 2]

@[simp] theorem standardUnlinkTangentialProjection_apply_zero (q : Sphere 4) :
    standardUnlinkTangentialProjection q 0 = q.1 0 := rfl

@[simp] theorem standardUnlinkTangentialProjection_apply_one (q : Sphere 4) :
    standardUnlinkTangentialProjection q 1 = q.1 1 := rfl

@[simp] theorem standardUnlinkTangentialProjection_apply_two (q : Sphere 4) :
    standardUnlinkTangentialProjection q 2 = q.1 2 := rfl

/-- The first aligned block is exactly the unlink's normal projection. -/
theorem unlinkAlignedSplitEquiv_fst (q : Sphere 4) :
    (unlinkAlignedSplitEquiv q.1).1 = standardUnlinkNormalProjection q := by
  ext j
  fin_cases j <;> rfl

/-- The second aligned block is exactly the first-three-coordinate tangential projection. -/
theorem unlinkAlignedSplitEquiv_snd (q : Sphere 4) :
    (unlinkAlignedSplitEquiv q.1).2 = standardUnlinkTangentialProjection q := by
  ext j
  fin_cases j <;> rfl

/-- The direct one-handle face after aligning its coordinate blocks with the standard unlink. -/
def unlinkAlignedOneHandleSphereMap : C(OneHandlePiece, Sphere 4) :=
  ⟨fun x ↦ unlinkAlignedSphereHomeomorph (oneHandleSphereMap x),
    unlinkAlignedSphereHomeomorph.continuous.comp oneHandleSphereMap.continuous⟩

/-- The direct cap face after aligning its disk factor with the unlink normal plane. -/
def unlinkAlignedCapSphereMap : C(CapPiece, Sphere 4) :=
  ⟨fun x ↦ unlinkAlignedSphereHomeomorph (sphereHandleCapMap x),
    unlinkAlignedSphereHomeomorph.continuous.comp sphereHandleCapMap.continuous⟩

@[simp] theorem unlinkAlignedOneHandleSphereMap_apply (x : OneHandlePiece) :
    unlinkAlignedOneHandleSphereMap x =
      unlinkAlignedSphereHomeomorph (oneHandleSphereMap x) :=
  rfl

@[simp] theorem unlinkAlignedCapSphereMap_apply (x : CapPiece) :
    unlinkAlignedCapSphereMap x =
      unlinkAlignedSphereHomeomorph (sphereHandleCapMap x) :=
  rfl

@[simp] theorem unlinkAlignedSplitEquiv_oneHandleSphereMap (x : OneHandlePiece) :
    unlinkAlignedSplitEquiv (unlinkAlignedOneHandleSphereMap x).1 =
      (sphereHandleScale ‖x.2.1‖ • x.1.1, sphereHandleRadius • x.2.1) := by
  change unlinkAlignedSplitEquiv
      (unlinkAlignedAmbientEquiv (oneHandleSphereMap x).1) = _
  rw [unlinkAlignedSplitEquiv_unlinkAlignedAmbientEquiv,
    sphereHandleSplitEquiv_oneHandleSphereMap]

@[simp] theorem unlinkAlignedSplitEquiv_capSphereMap (x : CapPiece) :
    unlinkAlignedSplitEquiv (unlinkAlignedCapSphereMap x).1 =
      (sphereHandleRadius • x.1.1, sphereHandleScale ‖x.1.1‖ • x.2.1) := by
  change unlinkAlignedSplitEquiv
      (unlinkAlignedAmbientEquiv (sphereHandleCapMap x).1) = _
  rw [unlinkAlignedSplitEquiv_unlinkAlignedAmbientEquiv,
    sphereHandleSplitEquiv_sphereHandleCapMap]

/-- On the aligned one-handle face the normal projection is the scaled circle factor. -/
theorem standardUnlinkNormalProjection_unlinkAlignedOneHandleSphereMap
    (x : OneHandlePiece) :
    standardUnlinkNormalProjection (unlinkAlignedOneHandleSphereMap x) =
      sphereHandleScale ‖x.2.1‖ • x.1.1 := by
  rw [← unlinkAlignedSplitEquiv_fst, unlinkAlignedSplitEquiv_oneHandleSphereMap]

/-- On the aligned cap face the normal projection is exactly the disk coordinate scaled by the
seam radius. -/
theorem standardUnlinkNormalProjection_unlinkAlignedCapSphereMap (x : CapPiece) :
    standardUnlinkNormalProjection (unlinkAlignedCapSphereMap x) =
      sphereHandleRadius • x.1.1 := by
  rw [← unlinkAlignedSplitEquiv_fst, unlinkAlignedSplitEquiv_capSphereMap]

/-- The aligned face maps retain the exact common-boundary agreement. -/
theorem unlinkAlignedSphereMap_boundary_agreement (y : OneHandleCapBoundary) :
    unlinkAlignedOneHandleSphereMap (oneHandleBoundaryInclusion y) =
      unlinkAlignedCapSphereMap (capBoundaryInclusion y) := by
  exact congrArg unlinkAlignedSphereHomeomorph
    (oneHandleSphereMap_boundary_agreement y)

/-- The aligned one-handle face map remains injective. -/
theorem unlinkAlignedOneHandleSphereMap_injective :
    Injective unlinkAlignedOneHandleSphereMap :=
  unlinkAlignedSphereHomeomorph.injective.comp oneHandleSphereMap_injective

/-- The aligned cap face map remains injective. -/
theorem unlinkAlignedCapSphereMap_injective :
    Injective unlinkAlignedCapSphereMap :=
  unlinkAlignedSphereHomeomorph.injective.comp sphereHandleCapMap_injective

/-- Equality between the two aligned face images occurs exactly at their common attaching
boundary. -/
theorem unlinkAlignedOneHandleSphereMap_eq_capSphereMap_iff
    (x : OneHandlePiece) (y : CapPiece) :
    unlinkAlignedOneHandleSphereMap x = unlinkAlignedCapSphereMap y ↔
      ∃ z : OneHandleCapBoundary,
        oneHandleBoundaryInclusion z = x ∧ capBoundaryInclusion z = y := by
  change unlinkAlignedSphereHomeomorph (oneHandleSphereMap x) =
      unlinkAlignedSphereHomeomorph (sphereHandleCapMap y) ↔ _
  rw [unlinkAlignedSphereHomeomorph.injective.eq_iff,
    oneHandleSphereMap_eq_sphereHandleCapMap_iff]

/-- Every point of the four-sphere lies in one of the two aligned face images. -/
theorem exists_unlinkAlignedOneHandleSphereMap_or_capSphereMap (q : Sphere 4) :
    (∃ x : OneHandlePiece, unlinkAlignedOneHandleSphereMap x = q) ∨
      ∃ y : CapPiece, unlinkAlignedCapSphereMap y = q := by
  obtain ⟨q', rfl⟩ := unlinkAlignedSphereHomeomorph.surjective q
  rcases exists_oneHandleSphereMap_or_sphereHandleCapMap q' with ⟨x, hx⟩ | ⟨y, hy⟩
  · exact Or.inl ⟨x, by simpa using congrArg unlinkAlignedSphereHomeomorph hx⟩
  · exact Or.inr ⟨y, by simpa using congrArg unlinkAlignedSphereHomeomorph hy⟩

/-- The ranges of the aligned face maps cover the literal four-sphere. -/
theorem range_unlinkAlignedOneHandleSphereMap_union_range_capSphereMap :
    range unlinkAlignedOneHandleSphereMap ∪ range unlinkAlignedCapSphereMap = univ := by
  ext q
  constructor
  · exact fun _ ↦ mem_univ q
  · intro _
    rcases exists_unlinkAlignedOneHandleSphereMap_or_capSphereMap q with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨y, hy⟩

/-- The entire direct capped-one-handle pushout, postcomposed by the coordinate permutation. -/
def unlinkAlignedCappedOneHandleHomeomorphSphere : CappedOneHandle ≃ₜ Sphere 4 :=
  directCappedOneHandleHomeomorphSphere.trans unlinkAlignedSphereHomeomorph

@[simp] theorem unlinkAlignedCappedOneHandleHomeomorphSphere_inl (x : OneHandlePiece) :
    unlinkAlignedCappedOneHandleHomeomorphSphere (cappedOneHandleInl x) =
      unlinkAlignedOneHandleSphereMap x := by
  simp [unlinkAlignedCappedOneHandleHomeomorphSphere,
    unlinkAlignedOneHandleSphereMap]

@[simp] theorem unlinkAlignedCappedOneHandleHomeomorphSphere_inr (x : CapPiece) :
    unlinkAlignedCappedOneHandleHomeomorphSphere (cappedOneHandleInr x) =
      unlinkAlignedCapSphereMap x := by
  simp [unlinkAlignedCappedOneHandleHomeomorphSphere,
    unlinkAlignedCapSphereMap]

/-- The disk coordinate in the aligned cap lying over the center of unlink component `i`. -/
def unlinkCapCoordinateCenter (i : Fin 2) : SphereHandleFirst :=
  sphereHandleRadius⁻¹ • standardUnlinkNormalCenter i

@[simp] theorem sphereHandleRadius_smul_unlinkCapCoordinateCenter (i : Fin 2) :
    sphereHandleRadius • unlinkCapCoordinateCenter i = standardUnlinkNormalCenter i := by
  rw [unlinkCapCoordinateCenter, smul_smul,
    mul_inv_cancel₀ sphereHandleRadius_ne_zero, one_smul]

@[simp] theorem norm_unlinkCapCoordinateCenter (i : Fin 2) :
    ‖unlinkCapCoordinateCenter i‖ = sphereHandleRadius := by
  rw [unlinkCapCoordinateCenter, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr sphereHandleRadius_pos), norm_standardUnlinkNormalCenter]
  have hr := sphereHandleRadius_sq
  field_simp [sphereHandleRadius_ne_zero]
  nlinarith

/-- The preimage of an unlink component in the aligned cap is the corresponding disk center
crossed with the entire sphere factor. -/
theorem unlinkAlignedCapSphereMap_mem_standardUnlinkComponent_iff
    (i : Fin 2) (x : CapPiece) :
    unlinkAlignedCapSphereMap x ∈ standardUnlinkComponent i ↔
      x.1.1 = unlinkCapCoordinateCenter i := by
  rw [← preimage_singleton_standardUnlinkNormalCenter i]
  change standardUnlinkNormalProjection (unlinkAlignedCapSphereMap x) =
      standardUnlinkNormalCenter i ↔ _
  rw [standardUnlinkNormalProjection_unlinkAlignedCapSphereMap,
    ← sphereHandleRadius_smul_unlinkCapCoordinateCenter]
  exact (smul_right_injective SphereHandleFirst sphereHandleRadius_ne_zero).eq_iff

/-- Set-level form of the aligned cap component preimage. -/
theorem preimage_standardUnlinkComponent_unlinkAlignedCapSphereMap (i : Fin 2) :
    unlinkAlignedCapSphereMap ⁻¹' standardUnlinkComponent i =
      {x : CapPiece | x.1.1 = unlinkCapCoordinateCenter i} := by
  ext x
  exact unlinkAlignedCapSphereMap_mem_standardUnlinkComponent_iff i x

end SplittingSpheres
