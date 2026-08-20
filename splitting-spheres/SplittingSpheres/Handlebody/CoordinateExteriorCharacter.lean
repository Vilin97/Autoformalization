/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPowerCover
public import SplittingSpheres.Geometry.UnlinkMeridianCharacter

/-!
# The cyclic character on the two pieces of the coordinate exterior

The exterior pushout has a whole `S¹ × B³` face and a punctured-cap face.  This file records the
right-normal complex character on each coprojection in the exact piece coordinates.  These
formulas are the point-set input for decomposing the power pullback piecewise.

No fundamental-group, deformation-retract, or graph-thickening assertion is made.
-/

@[expose] public section

noncomputable section

open Function

namespace SplittingSpheres

/-- Coprojection of the whole one-handle piece into the concrete radius-`1/8` exterior
pushout. -/
abbrev coordinateUnlinkExteriorPushoutOneHandleInclusion :
    C(OneHandlePiece,
      CoordinateUnlinkExteriorPushout oneEighth_lt_sphereHandleRadius_sub_half) :=
  topologicalPushoutInl oneHandleBoundaryInclusion
    (unlinkPuncturedCapBoundaryInclusion oneEighth_lt_sphereHandleRadius_sub_half)

/-- Coprojection of the punctured-cap piece into the concrete radius-`1/8` exterior pushout. -/
abbrev coordinateUnlinkExteriorPushoutPuncturedCapInclusion :
    C(UnlinkPuncturedCap (1 / 8 : ℝ),
      CoordinateUnlinkExteriorPushout oneEighth_lt_sphereHandleRadius_sub_half) :=
  topologicalPushoutInr oneHandleBoundaryInclusion
    (unlinkPuncturedCapBoundaryInclusion oneEighth_lt_sphereHandleRadius_sub_half)

/-- On the one-handle piece, the cyclic character is displacement of the scaled circle factor
from the right unlink center. -/
@[simp]
theorem coordinateUnlinkExteriorPushoutRightNormalMap_oneHandle
    (x : OneHandlePiece) :
    (coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorPushoutOneHandleInclusion x) : ℂ) =
      unlinkNormalPlaneToComplex
        (sphereHandleScale ‖x.2.1‖ • x.1.1 - standardUnlinkNormalCenter 1) := by
  rw [coordinateUnlinkExteriorPushoutRightNormalMap, Function.comp_apply,
    coordinateUnlinkExteriorOneEighthHomeomorph,
    coordinateUnlinkExteriorPushoutHomeomorph_inl]
  change standardUnlinkRightDisplacementComplex
      (unlinkAlignedOneHandleSphereMap x) = _
  rw [standardUnlinkRightDisplacementComplex,
    standardUnlinkNormalProjection_unlinkAlignedOneHandleSphereMap]

/-- On the punctured cap, the cyclic character is displacement of the seam-scaled disk
coordinate from the right unlink center. -/
@[simp]
theorem coordinateUnlinkExteriorPushoutRightNormalMap_puncturedCap
    (x : UnlinkPuncturedCap (1 / 8 : ℝ)) :
    (coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorPushoutPuncturedCapInclusion x) : ℂ) =
      unlinkNormalPlaneToComplex
        (sphereHandleRadius • x.1.1.1 - standardUnlinkNormalCenter 1) := by
  rw [coordinateUnlinkExteriorPushoutRightNormalMap, Function.comp_apply,
    coordinateUnlinkExteriorOneEighthHomeomorph,
    coordinateUnlinkExteriorPushoutHomeomorph_inr]
  change standardUnlinkRightDisplacementComplex
      (unlinkAlignedCapSphereMap x.1) = _
  rw [standardUnlinkRightDisplacementComplex,
    standardUnlinkNormalProjection_unlinkAlignedCapSphereMap]

/-! ## The core circle of the one-handle piece -/

/-- The zero point of the closed three-ball factor. -/
def oneHandleClosedBallZero : EuclideanClosedBall 3 :=
  ⟨0, by simp⟩

/-- The central `S¹` of the whole one-handle face. -/
def coordinateUnlinkExteriorOneHandleCoreCircle (u : Sphere 1) : OneHandlePiece :=
  (u, oneHandleClosedBallZero)

@[simp]
theorem coordinateUnlinkExteriorOneHandleCoreCircle_fst (u : Sphere 1) :
    (coordinateUnlinkExteriorOneHandleCoreCircle u).1 = u :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorOneHandleCoreCircle_snd_val (u : Sphere 1) :
    (coordinateUnlinkExteriorOneHandleCoreCircle u).2.1 = 0 :=
  rfl

/-- On the one-handle core circle, the right-normal character is the unit circle translated by
`-1/2`. -/
@[simp]
theorem coordinateUnlinkExteriorPushoutRightNormalMap_oneHandleCoreCircle
    (u : Sphere 1) :
    (coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorPushoutOneHandleInclusion
          (coordinateUnlinkExteriorOneHandleCoreCircle u)) : ℂ) =
      unlinkUnitCircleComplex u - (1 / 2 : ℂ) := by
  rw [coordinateUnlinkExteriorPushoutRightNormalMap_oneHandle]
  simp only [coordinateUnlinkExteriorOneHandleCoreCircle_snd_val, norm_zero]
  have hscale : sphereHandleScale 0 = 1 := by
    simp [sphereHandleScale]
  rw [hscale, one_smul]
  simp [unlinkUnitCircleComplex, unlinkNormalPlaneToComplex,
    standardUnlinkNormalCenter, standardUnlinkHeight,
    Complex.equivRealProdCLM_symm_apply]
  ring

end SplittingSpheres
