/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CollaredTopologicalPushoutBoundary
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckSmoothCapping

/-!
# Boundaries of the direct smooth planar neck cappings

This file applies the generic boundary theorem for a collared topological pushout to the direct
left and right smooth cappings.  The formulas retain exactly the old boundary points away from
the two attaching ranges.  They use the direct compact-cut, Euclidean-ball, and signed-seam
atlases; no transported atlas or comparison homeomorphism is involved.
-/

@[expose] public section

noncomputable section

open Function Set
open scoped ContDiff Manifold

namespace SplittingSpheres

/-- The boundary of the direct left smooth capping consists of the two component boundaries
away from their attaching ranges. -/
theorem boundary_coordinateUnlinkExteriorPlanarNeckLeftSmoothCapping
    (m : ℕ) [NeZero m] :
    letI := compactNeckLeftCutChartedSpace m
    letI :=
      coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    coordinateUnlinkExteriorModel.boundary
        (CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m) =
      topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) ''
        (coordinateUnlinkExteriorModel.boundary (CompactNeckLeftCut m) \
          range (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)) ∪
      topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) ''
        (coordinateUnlinkExteriorModel.boundary
            (ZMod m × EuclideanFourBall) \
          range
            (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)) := by
  let _ := compactNeckLeftCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckLeftCut m) :=
    isManifold_compactNeckLeftCut m
  let _ :=
    coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBall) :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily m
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    isManifold_signedSeamFamilyCommonModel m
  exact boundary_topologicalPushoutChartedSpace_of_isManifold
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m)
    (coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap_attaching_coverage m)
    (isManifold_coordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m)
    (by simp)
    (signedSeamFamilyCommonModel_boundary m)

/-- The boundary of the direct right smooth capping consists of the two component boundaries
away from their attaching ranges. -/
theorem boundary_coordinateUnlinkExteriorPlanarNeckRightSmoothCapping
    (m : ℕ) [NeZero m] :
    letI := compactNeckRightCutChartedSpace m
    letI :=
      coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    letI := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
    coordinateUnlinkExteriorModel.boundary
        (CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping m) =
      topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) ''
        (coordinateUnlinkExteriorModel.boundary (CompactNeckRightCut m) \
          range (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)) ∪
      topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) ''
        (coordinateUnlinkExteriorModel.boundary
            (ZMod m × EuclideanFourBall) \
          range
            (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)) := by
  let _ := compactNeckRightCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckRightCut m) :=
    isManifold_compactNeckRightCut m
  let _ :=
    coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBall) :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily m
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    isManifold_signedSeamFamilyCommonModel m
  exact boundary_topologicalPushoutChartedSpace_of_isManifold
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m)
    (coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap_attaching_coverage m)
    (isManifold_coordinateUnlinkExteriorPlanarNeckRightSmoothCapping m)
    (by simp)
    (signedSeamFamilyCommonModel_boundary m)

end SplittingSpheres
