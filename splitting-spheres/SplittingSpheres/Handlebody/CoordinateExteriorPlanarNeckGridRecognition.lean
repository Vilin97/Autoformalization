/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarGridBridge
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckGrid

/-!
# Recognizing the row-first planar neck grid

The concrete neck grid has three horizontal pushouts.  The middle row is the retained
`S¹ × S²` attaching boundary, the top row is the retained one-handle `S¹ × B³`, and the
bottom row is the normalized planar flower crossed with `S²`.  This file proves those three
identifications with exact leg formulas and then recognizes the row-first iterated pushout as
the original partial `S²`-spin.

The endpoint relabelling retains the canonical, unevaluated upper-endpoint offset.  Nothing in
this construction identifies that offset with `1`, and no cutting, separation, manifold, or
connected-sum assertion is made.
-/

@[expose] public section

noncomputable section

open Function Topology

namespace SplittingSpheres

/-! ## Simultaneous carrier normalization -/

/-- Replace the labelled left/right outer sectors by the literal closed carrier subtypes,
while relabelling each common endpoint by its incident neck arc. -/
def coordinateUnlinkExteriorPlanarNeckGridOuterSplitCongr
    (m : ℕ) [NeZero m] (Z : Type) [TopologicalSpace Z] :
    TopologicalPushout
        ((coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m).prodMap
          (ContinuousMap.id Z))
        ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
          (ContinuousMap.id Z)) ≃ₜ
      TopologicalPushout
        ((coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m).prodMap
          (ContinuousMap.id Z))
        ((coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m).prodMap
          (ContinuousMap.id Z)) :=
  topologicalPushoutCongr
    ((coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m).prodMap
      (ContinuousMap.id Z))
    ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
      (ContinuousMap.id Z))
    ((coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m).prodMap
      (ContinuousMap.id Z))
    ((coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m).prodMap
      (ContinuousMap.id Z))
    ((coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m).prodCongr
      (Homeomorph.refl Z))
    ((coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierHomeomorph m).prodCongr
      (Homeomorph.refl Z))
    ((coordinateUnlinkExteriorPlanarRightOuterSectorCarrierHomeomorph m).prodCongr
      (Homeomorph.refl Z))
    (by
      rintro ⟨x, z⟩
      exact Prod.ext
        (coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierHomeomorph_endpoint m x) rfl)
    (by
      rintro ⟨x, z⟩
      exact Prod.ext
        (coordinateUnlinkExteriorPlanarRightOuterSectorCarrierHomeomorph_endpoint m x) rfl)

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridOuterSplitCongr_inl
    (m : ℕ) [NeZero m] (Z : Type) [TopologicalSpace Z]
    (x : CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m) (z : Z) :
    coordinateUnlinkExteriorPlanarNeckGridOuterSplitCongr m Z
        (topologicalPushoutInl
          ((coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m).prodMap
            (ContinuousMap.id Z))
          ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
            (ContinuousMap.id Z)) (x, z)) =
      topologicalPushoutInl
        ((coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m).prodMap
          (ContinuousMap.id Z))
        ((coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m).prodMap
          (ContinuousMap.id Z))
        (coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierHomeomorph m x, z) := by
  apply topologicalPushoutCongr_inl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridOuterSplitCongr_inr
    (m : ℕ) [NeZero m] (Z : Type) [TopologicalSpace Z]
    (x : CoordinateUnlinkExteriorPlanarNeckGridRightOuter m) (z : Z) :
    coordinateUnlinkExteriorPlanarNeckGridOuterSplitCongr m Z
        (topologicalPushoutInr
          ((coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m).prodMap
            (ContinuousMap.id Z))
          ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
            (ContinuousMap.id Z)) (x, z)) =
      topologicalPushoutInr
        ((coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m).prodMap
          (ContinuousMap.id Z))
        ((coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m).prodMap
          (ContinuousMap.id Z))
        (coordinateUnlinkExteriorPlanarRightOuterSectorCarrierHomeomorph m x, z) := by
  apply topologicalPushoutCongr_inr

/-! ## Recognition of the three horizontal rows -/

/-- The middle horizontal pushout is the retained attaching boundary `S¹ × S²`. -/
def coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleHomeomorph
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).horizontalMiddle ≃ₜ
      OneHandleCapBoundary := by
  let _ : T2Space (CoordinateUnlinkExteriorPlanarOuterParameterSplitPushout m) :=
    (coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph m).symm.t2Space
  exact
    (coordinateUnlinkExteriorPlanarNeckGridOuterSplitCongr m (Sphere 2)).trans <|
      (topologicalPushoutProductHomeomorph
        (coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m)
        (coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m)
        (Sphere 2)
        (injective_coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m)
        (injective_coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m)).trans
      ((coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph m).prodCongr
        (Homeomorph.refl (Sphere 2)))

/-- The top horizontal pushout is the retained one-handle `S¹ × B³`. -/
def coordinateUnlinkExteriorPlanarNeckGridHorizontalTopHomeomorph
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).horizontalTop ≃ₜ
      OneHandlePiece :=
  (coordinateUnlinkExteriorPlanarNeckGridOuterSplitCongr m
      (EuclideanClosedBall 3)).trans
    (coordinateUnlinkExteriorPlanarOuterParameterOneHandleSplitHomeomorph m)

/-- The bottom horizontal pushout is the normalized planar flower crossed with `S²`. -/
abbrev coordinateUnlinkExteriorPlanarNeckGridHorizontalBottomHomeomorph
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).horizontalBottom ≃ₜ
      CoordinateUnlinkExteriorPlanarFlower m × Sphere 2 :=
  coordinateUnlinkExteriorPlanarNormalizedNeckSphereTwoPushoutHomeomorph m

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToLeft
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToRight (x, s)) =
      (coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m x, s) := by
  let _ : T2Space (CoordinateUnlinkExteriorPlanarOuterParameterSplitPushout m) :=
    (coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph m).symm.t2Space
  change ((coordinateUnlinkExteriorPlanarNeckGridOuterSplitCongr m (Sphere 2)).trans
      ((topologicalPushoutProductHomeomorph
          (coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m)
          (coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m)
          (Sphere 2)
          (injective_coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m)
          (injective_coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m)).trans
        ((coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph m).prodCongr
          (Homeomorph.refl (Sphere 2)))))
      (topologicalPushoutInl
        ((coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m).prodMap
          (ContinuousMap.id (Sphere 2)))
        ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
          (ContinuousMap.id (Sphere 2))) (x, s)) = _
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarNeckGridOuterSplitCongr_inl,
    topologicalPushoutProductHomeomorph_inl]
  change
    (coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m)
          (coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m)
          (coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierHomeomorph m x)), s) = _
  apply Prod.ext
  · rw [coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph_inl,
      coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierHomeomorph_apply_coe]
  · rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridRightOuter m) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToLeft
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToRight (x, s)) =
      (coordinateUnlinkExteriorPlanarRightOuterSectorParameter m x.1 x.2, s) := by
  let _ : T2Space (CoordinateUnlinkExteriorPlanarOuterParameterSplitPushout m) :=
    (coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph m).symm.t2Space
  change ((coordinateUnlinkExteriorPlanarNeckGridOuterSplitCongr m (Sphere 2)).trans
      ((topologicalPushoutProductHomeomorph
          (coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m)
          (coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m)
          (Sphere 2)
          (injective_coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m)
          (injective_coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m)).trans
        ((coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph m).prodCongr
          (Homeomorph.refl (Sphere 2)))))
      (topologicalPushoutInr
        ((coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m).prodMap
          (ContinuousMap.id (Sphere 2)))
        ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
          (ContinuousMap.id (Sphere 2))) (x, s)) = _
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarNeckGridOuterSplitCongr_inr,
    topologicalPushoutProductHomeomorph_inr]
  change
    (coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m)
          (coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m)
          (coordinateUnlinkExteriorPlanarRightOuterSectorCarrierHomeomorph m x)), s) = _
  apply Prod.ext
  · rw [coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph_inr,
      coordinateUnlinkExteriorPlanarRightOuterSectorCarrierHomeomorph_apply_coe]
  · rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridHorizontalTopHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarNeckGridHorizontalTopHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).topToTopLeft
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).topToTopRight (x, b)) =
      (coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m x, b) := by
  change ((coordinateUnlinkExteriorPlanarNeckGridOuterSplitCongr m
      (EuclideanClosedBall 3)).trans
        (coordinateUnlinkExteriorPlanarOuterParameterOneHandleSplitHomeomorph m))
      (topologicalPushoutInl
        ((coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m).prodMap
          (ContinuousMap.id (EuclideanClosedBall 3)))
        ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
          (ContinuousMap.id (EuclideanClosedBall 3))) (x, b)) = _
  rw [Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarNeckGridOuterSplitCongr_inl,
    coordinateUnlinkExteriorPlanarOuterParameterOneHandleSplitHomeomorph_inl]
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridHorizontalTopHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridRightOuter m)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarNeckGridHorizontalTopHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).topToTopLeft
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).topToTopRight (x, b)) =
      (coordinateUnlinkExteriorPlanarRightOuterSectorParameter m x.1 x.2, b) := by
  change ((coordinateUnlinkExteriorPlanarNeckGridOuterSplitCongr m
      (EuclideanClosedBall 3)).trans
        (coordinateUnlinkExteriorPlanarOuterParameterOneHandleSplitHomeomorph m))
      (topologicalPushoutInr
        ((coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m).prodMap
          (ContinuousMap.id (EuclideanClosedBall 3)))
        ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
          (ContinuousMap.id (EuclideanClosedBall 3))) (x, b)) = _
  rw [Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarNeckGridOuterSplitCongr_inr,
    coordinateUnlinkExteriorPlanarOuterParameterOneHandleSplitHomeomorph_inr]
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridHorizontalBottomHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNormalizedLeftHalf m) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckGridHorizontalBottomHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).bottomToBottomLeft
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).bottomToBottomRight (x, s)) =
      (coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion m
        (coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m x), s) := by
  change coordinateUnlinkExteriorPlanarNormalizedNeckSphereTwoPushoutHomeomorph m
      (topologicalPushoutInl
        ((coordinateUnlinkExteriorPlanarNormalizedLeftSeam m).prodMap
          (ContinuousMap.id (Sphere 2)))
        ((coordinateUnlinkExteriorPlanarNormalizedRightSeam m).prodMap
          (ContinuousMap.id (Sphere 2))) (x, s)) = _
  exact coordinateUnlinkExteriorPlanarNormalizedNeckSphereTwoPushoutHomeomorph_inl m x s

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridHorizontalBottomHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNormalizedRightHalf) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckGridHorizontalBottomHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).bottomToBottomLeft
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).bottomToBottomRight (x, s)) =
      (coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion m
        (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m x), s) := by
  change coordinateUnlinkExteriorPlanarNormalizedNeckSphereTwoPushoutHomeomorph m
      (topologicalPushoutInr
        ((coordinateUnlinkExteriorPlanarNormalizedLeftSeam m).prodMap
          (ContinuousMap.id (Sphere 2)))
        ((coordinateUnlinkExteriorPlanarNormalizedRightSeam m).prodMap
          (ContinuousMap.id (Sphere 2))) (x, s)) = _
  exact coordinateUnlinkExteriorPlanarNormalizedNeckSphereTwoPushoutHomeomorph_inr m x s

/-! ## Compatibility of the recognized rows -/

/-- The induced middle-to-top map is the literal inclusion of the attaching boundary in the
retained one-handle. -/
theorem coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleToTop_compatibility
    (m : ℕ) [NeZero m]
    (z : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).horizontalMiddle) :
    coordinateUnlinkExteriorPlanarNeckGridHorizontalTopHomeomorph m
        ((coordinateUnlinkExteriorPlanarNeckGridDiagram m).horizontalMiddleToTop z) =
      oneHandleBoundaryInclusion
        (coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleHomeomorph m z) := by
  rcases topologicalPushout_jointly_surjective
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToLeft
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToRight z with
    ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [TopologicalPushoutGridDiagram.horizontalMiddleToTop_inl,
      coordinateUnlinkExteriorPlanarNeckGridDiagram_leftToTopLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridHorizontalTopHomeomorph_inl,
      coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleHomeomorph_inl]
    rfl
  · rw [TopologicalPushoutGridDiagram.horizontalMiddleToTop_inr,
      coordinateUnlinkExteriorPlanarNeckGridDiagram_rightToTopRight_apply,
      coordinateUnlinkExteriorPlanarNeckGridHorizontalTopHomeomorph_inr,
      coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleHomeomorph_inr]
    rfl

/-- The induced middle-to-bottom map is the literal partial-spin boundary map into the planar
flower crossed with `S²`. -/
theorem coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleToBottom_compatibility
    (m : ℕ) [NeZero m]
    (z : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).horizontalMiddle) :
    coordinateUnlinkExteriorPlanarNeckGridHorizontalBottomHomeomorph m
        ((coordinateUnlinkExteriorPlanarNeckGridDiagram m).horizontalMiddleToBottom z) =
      partialSphereSpinBoundaryInclusion
        (coordinateUnlinkExteriorPlanarFlowerOuter m)
        (coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleHomeomorph m z) := by
  rcases topologicalPushout_jointly_surjective
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToLeft
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToRight z with
    ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [TopologicalPushoutGridDiagram.horizontalMiddleToBottom_inl,
      coordinateUnlinkExteriorPlanarNeckGridDiagram_leftToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridHorizontalBottomHomeomorph_inl,
      coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleHomeomorph_inl,
      coordinateUnlinkExteriorPlanarNeckGridLeftToBottomLeft_apply,
      partialSphereSpinBoundaryInclusion_apply]
    change
      (coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion m
          (coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m
            (x.1.1, partialSphereSpinAnnulusOne
              (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap x.1.2))), x.2) =
        (coordinateUnlinkExteriorPlanarFlowerOuter m
          (coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m x.1), x.2)
    apply Prod.ext
    · change coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion m
          (coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m
            (x.1.1, partialSphereSpinAnnulusOne
              (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap x.1.2))) =
        coordinateUnlinkExteriorPlanarFlowerOuter m
          (coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m x.1)
      rw [coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion_apply,
        coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap_sector,
        ← coordinateUnlinkExteriorPlanarFlowerOuter_leftOuterSectorParameter]
    · rfl
  · rw [TopologicalPushoutGridDiagram.horizontalMiddleToBottom_inr,
      coordinateUnlinkExteriorPlanarNeckGridDiagram_rightToBottomRight_apply,
      coordinateUnlinkExteriorPlanarNeckGridHorizontalBottomHomeomorph_inr,
      coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleHomeomorph_inr,
      coordinateUnlinkExteriorPlanarNeckGridRightToBottomRight_apply,
      partialSphereSpinBoundaryInclusion_apply]
    change
      (coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion m
          (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m
            (partialSphereSpinAnnulusOne
              (coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m x.1))), x.2) =
        (coordinateUnlinkExteriorPlanarFlowerOuter m
          (coordinateUnlinkExteriorPlanarRightOuterSectorParameter m x.1.1 x.1.2), x.2)
    apply Prod.ext
    · change coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion m
          (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m
            (partialSphereSpinAnnulusOne
              (coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m x.1))) =
        coordinateUnlinkExteriorPlanarFlowerOuter m
          (coordinateUnlinkExteriorPlanarRightOuterSectorParameter m x.1.1 x.1.2)
      rw [coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion_apply,
        partialSphereSpinAnnulusOne_apply,
        coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle_realize]
      exact
        (coordinateUnlinkExteriorPlanarFlowerOuter_rightOuterSectorParameter
          m x.1.1 x.1.2).symm
    · rfl

/-! ## Row-first recognition and the exact regrouping -/

/-- The row-first iterated grid is exactly the original partial `S²`-spin of the planar
flower. -/
def coordinateUnlinkExteriorPlanarNeckGridRowFirstHomeomorph
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rowFirst ≃ₜ
      CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m :=
  topologicalPushoutCongr
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).horizontalMiddleToTop
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).horizontalMiddleToBottom
    oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion
      (coordinateUnlinkExteriorPlanarFlowerOuter m))
    (coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleHomeomorph m)
    (coordinateUnlinkExteriorPlanarNeckGridHorizontalTopHomeomorph m)
    (coordinateUnlinkExteriorPlanarNeckGridHorizontalBottomHomeomorph m)
    (coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleToTop_compatibility m)
    (coordinateUnlinkExteriorPlanarNeckGridHorizontalMiddleToBottom_compatibility m)

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridRowFirstHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).horizontalTop) :
    coordinateUnlinkExteriorPlanarNeckGridRowFirstHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).horizontalMiddleToTop
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).horizontalMiddleToBottom x) =
      partialSphereSpinInl (coordinateUnlinkExteriorPlanarFlowerOuter m)
        (coordinateUnlinkExteriorPlanarNeckGridHorizontalTopHomeomorph m x) := by
  apply topologicalPushoutCongr_inl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridRowFirstHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).horizontalBottom) :
    coordinateUnlinkExteriorPlanarNeckGridRowFirstHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).horizontalMiddleToTop
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).horizontalMiddleToBottom x) =
      partialSphereSpinInr (coordinateUnlinkExteriorPlanarFlowerOuter m)
        (coordinateUnlinkExteriorPlanarNeckGridHorizontalBottomHomeomorph m x) := by
  apply topologicalPushoutCongr_inr

/-- Regroup the original partial spin by columns: the left column is the complete labelled
family of leaf pieces, the right column is the central piece, and their common vertical
pushout is the family of neck three-spheres. -/
def coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m ≃ₜ
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirst :=
  (coordinateUnlinkExteriorPlanarNeckGridRowFirstHomeomorph m).symm.trans
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).topologicalPushoutGridHomeomorph

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst_topLeft
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridHL m) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
        (partialSphereSpinInl (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarNeckGridHorizontalTopHomeomorph m
            (topologicalPushoutInl
              (coordinateUnlinkExteriorPlanarNeckGridDiagram m).topToTopLeft
              (coordinateUnlinkExteriorPlanarNeckGridDiagram m).topToTopRight x))) =
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirstTopLeft x := by
  rw [coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst,
    Homeomorph.trans_apply,
    ← coordinateUnlinkExteriorPlanarNeckGridRowFirstHomeomorph_inl]
  rw [(coordinateUnlinkExteriorPlanarNeckGridRowFirstHomeomorph m).symm_apply_apply]
  apply TopologicalPushoutGridDiagram.topologicalPushoutGridHomeomorph_apply_topLeft

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst_topRight
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridHR m) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
        (partialSphereSpinInl (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarNeckGridHorizontalTopHomeomorph m
            (topologicalPushoutInr
              (coordinateUnlinkExteriorPlanarNeckGridDiagram m).topToTopLeft
              (coordinateUnlinkExteriorPlanarNeckGridDiagram m).topToTopRight x))) =
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirstTopRight x := by
  rw [coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst,
    Homeomorph.trans_apply,
    ← coordinateUnlinkExteriorPlanarNeckGridRowFirstHomeomorph_inl]
  rw [(coordinateUnlinkExteriorPlanarNeckGridRowFirstHomeomorph m).symm_apply_apply]
  apply TopologicalPushoutGridDiagram.topologicalPushoutGridHomeomorph_apply_topRight

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridRegrouping_bottomLeft
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridFL m) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
        (partialSphereSpinInr (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarNeckGridHorizontalBottomHomeomorph m
            (topologicalPushoutInl
              (coordinateUnlinkExteriorPlanarNeckGridDiagram m).bottomToBottomLeft
              (coordinateUnlinkExteriorPlanarNeckGridDiagram m).bottomToBottomRight x))) =
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirstBottomLeft x := by
  rw [coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst,
    Homeomorph.trans_apply,
    ← coordinateUnlinkExteriorPlanarNeckGridRowFirstHomeomorph_inr]
  rw [(coordinateUnlinkExteriorPlanarNeckGridRowFirstHomeomorph m).symm_apply_apply]
  apply TopologicalPushoutGridDiagram.topologicalPushoutGridHomeomorph_apply_bottomLeft

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridRegrouping_bottomRight
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridFR) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
        (partialSphereSpinInr (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarNeckGridHorizontalBottomHomeomorph m
            (topologicalPushoutInr
              (coordinateUnlinkExteriorPlanarNeckGridDiagram m).bottomToBottomLeft
              (coordinateUnlinkExteriorPlanarNeckGridDiagram m).bottomToBottomRight x))) =
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirstBottomRight x := by
  rw [coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst,
    Homeomorph.trans_apply,
    ← coordinateUnlinkExteriorPlanarNeckGridRowFirstHomeomorph_inr]
  rw [(coordinateUnlinkExteriorPlanarNeckGridRowFirstHomeomorph m).symm_apply_apply]
  apply TopologicalPushoutGridDiagram.topologicalPushoutGridHomeomorph_apply_bottomRight

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridRegrouping_topLeft_apply
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
        (partialSphereSpinInl (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m x, b)) =
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirstTopLeft (x, b) := by
  simpa using
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst_topLeft
      m (x, b)

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridRegrouping_topRight_apply
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridRightOuter m)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
        (partialSphereSpinInl (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarRightOuterSectorParameter m x.1 x.2, b)) =
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirstTopRight (x, b) := by
  simpa using
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst_topRight
      m (x, b)

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridRegrouping_bottomLeft_apply
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNormalizedLeftHalf m) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
        (partialSphereSpinInr (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion m
            (coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m x), s)) =
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirstBottomLeft (x, s) := by
  simpa using
    coordinateUnlinkExteriorPlanarNeckGridRegrouping_bottomLeft
      m (x, s)

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridRegrouping_bottomRight_apply
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNormalizedRightHalf) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst m
        (partialSphereSpinInr (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion m
            (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m x), s)) =
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirstBottomRight (x, s) := by
  simpa using
    coordinateUnlinkExteriorPlanarNeckGridRegrouping_bottomRight
      m (x, s)

end SplittingSpheres
