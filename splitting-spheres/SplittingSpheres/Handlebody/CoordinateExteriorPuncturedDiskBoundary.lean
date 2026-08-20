/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPowerTrivializedPushout

/-!
# Boundary circles of the punctured normal disk

This file gives literal parameterizations of the two inner boundary circles of the planar
punctured-disk factor in the radius-`1/8` coordinate unlink exterior.  The parameterizations
are affine circles about the aligned cap-coordinate centers, at the exactly rescaled radius
`(1 / 8) / sphereHandleRadius`.

Everything here is elementary point-set geometry in the closed Euclidean two-ball.  In
particular, no lifted boundary classification or smooth-boundary assertion is made.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-- The inner-boundary radius in aligned cap coordinates. -/
def coordinateUnlinkExteriorPuncturedDiskInnerRadius : ℝ :=
  (1 / 8 : ℝ) / sphereHandleRadius

theorem coordinateUnlinkExteriorPuncturedDiskInnerRadius_pos :
    0 < coordinateUnlinkExteriorPuncturedDiskInnerRadius :=
  div_pos (by norm_num) sphereHandleRadius_pos

theorem coordinateUnlinkExteriorPuncturedDiskInnerRadius_ne_zero :
    coordinateUnlinkExteriorPuncturedDiskInnerRadius ≠ 0 :=
  coordinateUnlinkExteriorPuncturedDiskInnerRadius_pos.ne'

/-- A convenient exact expression for the rescaled radius. -/
theorem coordinateUnlinkExteriorPuncturedDiskInnerRadius_eq :
    coordinateUnlinkExteriorPuncturedDiskInnerRadius = sphereHandleRadius / 4 := by
  rw [coordinateUnlinkExteriorPuncturedDiskInnerRadius]
  field_simp [sphereHandleRadius_ne_zero]
  nlinarith [sphereHandleRadius_sq]

theorem sphereHandleRadius_mul_coordinateUnlinkExteriorPuncturedDiskInnerRadius :
    sphereHandleRadius * coordinateUnlinkExteriorPuncturedDiskInnerRadius = (1 / 8 : ℝ) := by
  rw [coordinateUnlinkExteriorPuncturedDiskInnerRadius]
  field_simp [sphereHandleRadius_ne_zero]

/-- The inner circles lie strictly inside the outer unit circle. -/
theorem sphereHandleRadius_add_coordinateUnlinkExteriorPuncturedDiskInnerRadius_lt_one :
    sphereHandleRadius + coordinateUnlinkExteriorPuncturedDiskInnerRadius < 1 := by
  rw [coordinateUnlinkExteriorPuncturedDiskInnerRadius_eq]
  have hR : sphereHandleRadius < (4 / 5 : ℝ) := by
    rw [← sq_lt_sq₀ sphereHandleRadius_pos.le (by norm_num), sphereHandleRadius_sq]
    norm_num
  linarith

/-- The underlying affine circle about cap-coordinate center `i`. -/
def coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw
    (i : Fin 2) (u : Sphere 1) : SphereHandleFirst :=
  unlinkCapCoordinateCenter i +
    coordinateUnlinkExteriorPuncturedDiskInnerRadius • u.1

theorem norm_coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw_lt_one
    (i : Fin 2) (u : Sphere 1) :
    ‖coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw i u‖ < 1 := by
  calc
    ‖coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw i u‖ ≤
        ‖unlinkCapCoordinateCenter i‖ +
          ‖coordinateUnlinkExteriorPuncturedDiskInnerRadius • u.1‖ :=
      norm_add_le _ _
    _ = sphereHandleRadius + coordinateUnlinkExteriorPuncturedDiskInnerRadius := by
      rw [norm_unlinkCapCoordinateCenter, norm_smul, Real.norm_eq_abs,
        abs_of_pos coordinateUnlinkExteriorPuncturedDiskInnerRadius_pos,
        mem_sphere_zero_iff_norm.mp u.2, mul_one]
    _ < 1 :=
      sphereHandleRadius_add_coordinateUnlinkExteriorPuncturedDiskInnerRadius_lt_one

@[simp]
theorem dist_coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw_self
    (i : Fin 2) (u : Sphere 1) :
    dist (coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw i u)
        (unlinkCapCoordinateCenter i) =
      coordinateUnlinkExteriorPuncturedDiskInnerRadius := by
  rw [coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw, dist_eq_norm,
    add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos coordinateUnlinkExteriorPuncturedDiskInnerRadius_pos,
    mem_sphere_zero_iff_norm.mp u.2, mul_one]

/-- The two aligned cap-coordinate centers are exactly `2 * sphereHandleRadius` apart. -/
theorem dist_unlinkCapCoordinateCenter_zero_one :
    dist (unlinkCapCoordinateCenter 0) (unlinkCapCoordinateCenter 1) =
      2 * sphereHandleRadius := by
  have hdist :=
    dist_sphereHandleRadius_smul_unlinkCapCoordinateCenter
      (1 : Fin 2) (unlinkCapCoordinateCenter 0)
  rw [sphereHandleRadius_smul_unlinkCapCoordinateCenter,
    dist_standardUnlinkNormalCenter_zero_one] at hdist
  apply (mul_left_cancel₀ sphereHandleRadius_ne_zero)
  rw [← hdist]
  nlinarith [sphereHandleRadius_sq]

theorem coordinateUnlinkExteriorPuncturedDiskInnerRadius_le_dist_zero_other
    (u : Sphere 1) :
    coordinateUnlinkExteriorPuncturedDiskInnerRadius ≤
      dist (coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw 0 u)
        (unlinkCapCoordinateCenter 1) := by
  have htri := dist_triangle (unlinkCapCoordinateCenter 0)
    (coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw 0 u)
    (unlinkCapCoordinateCenter 1)
  rw [dist_unlinkCapCoordinateCenter_zero_one,
    dist_comm (unlinkCapCoordinateCenter 0),
    dist_coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw_self] at htri
  rw [coordinateUnlinkExteriorPuncturedDiskInnerRadius_eq] at htri ⊢
  linarith [sphereHandleRadius_pos]

theorem coordinateUnlinkExteriorPuncturedDiskInnerRadius_le_dist_one_other
    (u : Sphere 1) :
    coordinateUnlinkExteriorPuncturedDiskInnerRadius ≤
      dist (coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw 1 u)
        (unlinkCapCoordinateCenter 0) := by
  have htri := dist_triangle (unlinkCapCoordinateCenter 1)
    (coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw 1 u)
    (unlinkCapCoordinateCenter 0)
  rw [dist_comm (unlinkCapCoordinateCenter 1) (unlinkCapCoordinateCenter 0),
    dist_unlinkCapCoordinateCenter_zero_one,
    dist_comm (unlinkCapCoordinateCenter 1),
    dist_coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw_self] at htri
  rw [coordinateUnlinkExteriorPuncturedDiskInnerRadius_eq] at htri ⊢
  linarith [sphereHandleRadius_pos]

/-- The literal inner boundary circle around component `i`, bundled in the punctured normal
disk. -/
def coordinateUnlinkExteriorPuncturedDiskInnerBoundary
    (i : Fin 2) (u : Sphere 1) : CoordinateUnlinkExteriorPuncturedNormalDisk := by
  refine ⟨⟨coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw i u,
    mem_closedBall_zero_iff.mpr
      (norm_coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw_lt_one i u).le⟩, ?_⟩
  change coordinateUnlinkExteriorPuncturedDiskInnerRadius ≤
        dist (coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw i u)
          (unlinkCapCoordinateCenter 0) ∧
      coordinateUnlinkExteriorPuncturedDiskInnerRadius ≤
        dist (coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw i u)
          (unlinkCapCoordinateCenter 1)
  fin_cases i
  · exact ⟨le_of_eq (dist_coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw_self 0 u).symm,
      coordinateUnlinkExteriorPuncturedDiskInnerRadius_le_dist_zero_other u⟩
  · exact ⟨coordinateUnlinkExteriorPuncturedDiskInnerRadius_le_dist_one_other u,
      le_of_eq (dist_coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw_self 1 u).symm⟩

@[simp]
theorem coordinateUnlinkExteriorPuncturedDiskInnerBoundary_val
    (i : Fin 2) (u : Sphere 1) :
    (coordinateUnlinkExteriorPuncturedDiskInnerBoundary i u).1.1 =
      unlinkCapCoordinateCenter i +
        coordinateUnlinkExteriorPuncturedDiskInnerRadius • u.1 :=
  rfl

@[simp]
theorem dist_coordinateUnlinkExteriorPuncturedDiskInnerBoundary_self
    (i : Fin 2) (u : Sphere 1) :
    dist (coordinateUnlinkExteriorPuncturedDiskInnerBoundary i u).1.1
        (unlinkCapCoordinateCenter i) =
      coordinateUnlinkExteriorPuncturedDiskInnerRadius :=
  dist_coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw_self i u

/-- Exact distance from the component-`0` inner circle to the other cap-coordinate center. -/
theorem dist_coordinateUnlinkExteriorPuncturedDiskInnerBoundary_zero_other
    (u : Sphere 1) :
    dist (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0 u).1.1
        (unlinkCapCoordinateCenter 1) =
      ‖unlinkCapCoordinateCenter 0 - unlinkCapCoordinateCenter 1 +
        coordinateUnlinkExteriorPuncturedDiskInnerRadius • u.1‖ := by
  rw [coordinateUnlinkExteriorPuncturedDiskInnerBoundary_val, dist_eq_norm]
  congr 1
  abel

/-- Exact distance from the component-`1` inner circle to the other cap-coordinate center. -/
theorem dist_coordinateUnlinkExteriorPuncturedDiskInnerBoundary_one_other
    (u : Sphere 1) :
    dist (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 1 u).1.1
        (unlinkCapCoordinateCenter 0) =
      ‖unlinkCapCoordinateCenter 1 - unlinkCapCoordinateCenter 0 +
        coordinateUnlinkExteriorPuncturedDiskInnerRadius • u.1‖ := by
  rw [coordinateUnlinkExteriorPuncturedDiskInnerBoundary_val, dist_eq_norm]
  congr 1
  abel

theorem coordinateUnlinkExteriorPuncturedDiskInnerRadius_le_dist_innerBoundary_zero_other
    (u : Sphere 1) :
    coordinateUnlinkExteriorPuncturedDiskInnerRadius ≤
      dist (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0 u).1.1
        (unlinkCapCoordinateCenter 1) :=
  coordinateUnlinkExteriorPuncturedDiskInnerRadius_le_dist_zero_other u

theorem coordinateUnlinkExteriorPuncturedDiskInnerRadius_le_dist_innerBoundary_one_other
    (u : Sphere 1) :
    coordinateUnlinkExteriorPuncturedDiskInnerRadius ≤
      dist (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 1 u).1.1
        (unlinkCapCoordinateCenter 0) :=
  coordinateUnlinkExteriorPuncturedDiskInnerRadius_le_dist_one_other u

theorem continuous_coordinateUnlinkExteriorPuncturedDiskInnerBoundary (i : Fin 2) :
    Continuous (coordinateUnlinkExteriorPuncturedDiskInnerBoundary i) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  unfold coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw
  fun_prop

theorem injective_coordinateUnlinkExteriorPuncturedDiskInnerBoundary (i : Fin 2) :
    Injective (coordinateUnlinkExteriorPuncturedDiskInnerBoundary i) := by
  intro u v huv
  apply Subtype.ext
  have h := congrArg
    (fun a : CoordinateUnlinkExteriorPuncturedNormalDisk ↦ a.1.1) huv
  change unlinkCapCoordinateCenter i +
      coordinateUnlinkExteriorPuncturedDiskInnerRadius • u.1 =
    unlinkCapCoordinateCenter i +
      coordinateUnlinkExteriorPuncturedDiskInnerRadius • v.1 at h
  have hsmul : coordinateUnlinkExteriorPuncturedDiskInnerRadius • u.1 =
      coordinateUnlinkExteriorPuncturedDiskInnerRadius • v.1 :=
    add_left_cancel h
  exact smul_right_injective SphereHandleFirst
    coordinateUnlinkExteriorPuncturedDiskInnerRadius_ne_zero hsmul

/-- Each inner circle is a topological embedding. -/
theorem isEmbedding_coordinateUnlinkExteriorPuncturedDiskInnerBoundary (i : Fin 2) :
    IsEmbedding (coordinateUnlinkExteriorPuncturedDiskInnerBoundary i) :=
  (continuous_coordinateUnlinkExteriorPuncturedDiskInnerBoundary i).isClosedEmbedding
    (injective_coordinateUnlinkExteriorPuncturedDiskInnerBoundary i) |>.isEmbedding

/-- An inner boundary circle cannot meet the outer unit-circle boundary. -/
theorem disjoint_range_coordinateUnlinkExteriorPuncturedDiskInnerBoundary_outerBoundary
    (i : Fin 2) :
    Disjoint (range (coordinateUnlinkExteriorPuncturedDiskInnerBoundary i))
      (range coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary) := by
  rw [Set.disjoint_left]
  rintro a ⟨u, rfl⟩ ⟨v, h⟩
  have hnorm := congrArg
    (fun z : CoordinateUnlinkExteriorPuncturedNormalDisk ↦ ‖z.1.1‖) h
  have hinner := norm_coordinateUnlinkExteriorPuncturedDiskInnerBoundaryRaw_lt_one i u
  change ‖(coordinateUnlinkExteriorPuncturedDiskInnerBoundary i u).1.1‖ < 1 at hinner
  have houter :
      ‖(coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary v).1.1‖ = 1 := by
    rw [coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary_val,
      mem_sphere_zero_iff_norm.mp v.2]
  rw [houter] at hnorm
  linarith

/-- After restoring the ambient scale, the component-`1` inner circle is exactly the radius
`1/8` normal circle about the right component. -/
theorem sphereHandleRadius_smul_innerBoundary_one_sub_center (u : Sphere 1) :
    sphereHandleRadius •
        (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 1 u).1.1 -
      standardUnlinkNormalCenter 1 = (1 / 8 : ℝ) • u.1 := by
  rw [coordinateUnlinkExteriorPuncturedDiskInnerBoundary_val, smul_add,
    sphereHandleRadius_smul_unlinkCapCoordinateCenter, smul_smul,
    sphereHandleRadius_mul_coordinateUnlinkExteriorPuncturedDiskInnerRadius,
    add_sub_cancel_left]

/-- After restoring the ambient scale, the component-`0` inner circle is the radius-`1/8`
circle about the left center, expressed relative to the right center. -/
theorem sphereHandleRadius_smul_innerBoundary_zero_sub_center (u : Sphere 1) :
    sphereHandleRadius •
        (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0 u).1.1 -
      standardUnlinkNormalCenter 1 =
      standardUnlinkNormalCenter 0 - standardUnlinkNormalCenter 1 +
        (1 / 8 : ℝ) • u.1 := by
  rw [coordinateUnlinkExteriorPuncturedDiskInnerBoundary_val, smul_add,
    sphereHandleRadius_smul_unlinkCapCoordinateCenter, smul_smul,
    sphereHandleRadius_mul_coordinateUnlinkExteriorPuncturedDiskInnerRadius]
  abel

/-- Exact planar-character formula on the right (`i = 1`) inner boundary. -/
@[simp]
theorem coordinateUnlinkExteriorPuncturedNormalDiskCharacter_innerBoundary_one
    (u : Sphere 1) :
    (coordinateUnlinkExteriorPuncturedNormalDiskCharacter
        (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 1 u) : ℂ) =
      (1 / 8 : ℂ) * unlinkUnitCircleComplex u := by
  rw [coordinateUnlinkExteriorPuncturedNormalDiskCharacter_coe]
  have h := sphereHandleRadius_smul_innerBoundary_one_sub_center u
  rw [h]
  simp [unlinkUnitCircleComplex, unlinkNormalPlaneToComplex,
    Complex.equivRealProdCLM_symm_apply]
  ring

/-- Exact planar-character formula on the left (`i = 0`) inner boundary. -/
@[simp]
theorem coordinateUnlinkExteriorPuncturedNormalDiskCharacter_innerBoundary_zero
    (u : Sphere 1) :
    (coordinateUnlinkExteriorPuncturedNormalDiskCharacter
        (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0 u) : ℂ) =
      (-1 : ℂ) + (1 / 8 : ℂ) * unlinkUnitCircleComplex u := by
  rw [coordinateUnlinkExteriorPuncturedNormalDiskCharacter_coe]
  have h := sphereHandleRadius_smul_innerBoundary_zero_sub_center u
  rw [h]
  simp [unlinkUnitCircleComplex, unlinkNormalPlaneToComplex,
    standardUnlinkNormalCenter, standardUnlinkHeight,
    Complex.equivRealProdCLM_symm_apply]
  ring

end SplittingSpheres
