/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph
public import SplittingSpheres.Handlebody.CoordinateExteriorRightTubeStandardOneHandleDiffeomorph

/-!
# Direct recognition of the right smooth capping as a one-handle

This file composes the smooth comparison from the direct right capping to the standard-atlas
right-tube power pullback with its direct recognition as the natural one-handle.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

/-- Recognize the direct right smooth capping as the natural one-handle. -/
noncomputable def coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
    CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, oneHandlePieceModel⟯
        OneHandlePiece := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullbackStandard m
  exact (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph m).trans
    (coordinateExteriorRightTubePowerPullbackStandardOneHandleDiffeomorph m)

/-- The direct recognition has the expected composite forward map. -/
@[simp] theorem coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph_apply
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping m) :
    letI := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
    coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph m z =
      (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m).symm
        (coordinateExteriorRightTubePowerPullbackHomeomorph m
          (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m z)) := by
  unfold coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph
  change coordinateExteriorRightTubePowerPullbackStandardOneHandleDiffeomorph m
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph m z) = _
  rw [coordinateExteriorRightTubePowerPullbackStandardOneHandleDiffeomorph_apply]
  rw [coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph_apply]
  rw [coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph_symm_apply]

/-- Forgetting smoothness gives the composite of the three point-set identifications. -/
@[simp] theorem
    coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph_toHomeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
    (coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph m).toHomeomorph =
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m).trans
        ((coordinateExteriorRightTubePowerPullbackHomeomorph m).trans
          (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m).symm) := by
  apply Homeomorph.ext
  intro z
  exact coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph_apply m z

/-- On the compact-cut generator, the direct recognition is the transported body map. -/
theorem coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph_inl
    (m : ℕ) [NeZero m] (x : CompactNeckRightCut m) :
    letI := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
    coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x) =
      (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m).symm
        (coordinateExteriorRightTubePowerPullbackHomeomorph m
          (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap m x)) := by
  rw [coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph_apply]
  rw [coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph_inl]

/-- On the rounded-cap generator, the direct recognition is the transported cap map. -/
theorem coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph_inr
    (m : ℕ) [NeZero m] (y : ZMod m × EuclideanFourBall) :
    letI := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
    coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) y) =
      (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m).symm
        (coordinateExteriorRightTubePowerPullbackHomeomorph m
          (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap m y)) := by
  rw [coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph_apply]
  rw [coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph_inr]

end SplittingSpheres
