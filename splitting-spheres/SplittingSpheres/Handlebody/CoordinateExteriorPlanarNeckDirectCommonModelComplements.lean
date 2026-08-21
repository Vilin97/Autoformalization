/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import
    SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckDirectMultiInteriorConnectedSum

/-!
# Direct smooth common-model complements for the planar-neck exterior

This file places direct generated smooth atlases on the literal rounded-cap complements in the
two common right-tube targets.  Each atlas is generated from the ambient off-cap charts and the
explicit compact-cut half collar.  The compact left and right cuts are then identified with these
literal complements by diffeomorphisms whose underlying homeomorphisms are the point-set
cancellation maps.

No charted space is transported through a complement homeomorphism, and the simultaneous
pushout is intentionally left to a later module.
-/

noncomputable section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace SplittingSpheres

namespace CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal

/-! ## Common-target family comparisons used by the left complement -/

noncomputable def coordinateExteriorRightTubeClosedOneHandleFamilyDiffeomorph
    (m : ℕ) :
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    (ZMod m × CoordinateExteriorRightTubeClosed)
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, oneHandlePieceModel⟯
        (ZMod m × OneHandlePiece) := by
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeClosed
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × CoordinateExteriorRightTubeClosed) :=
    isManifold_discreteProductChartedSpace coordinateUnlinkExteriorModel ∞
      (ZMod m) CoordinateExteriorRightTubeClosed
  let _ := discreteProductChartedSpace OneHandleModelSpace
    (ZMod m) OneHandlePiece
  let _ : IsManifold oneHandlePieceModel ∞ (ZMod m × OneHandlePiece) :=
    isManifold_discreteProductChartedSpace oneHandlePieceModel ∞
      (ZMod m) OneHandlePiece
  let p : ZMod m × CoordinateExteriorRightTubeClosed →
      CoordinateExteriorRightTubeClosed := Prod.snd
  let p' : ZMod m × OneHandlePiece → OneHandlePiece := Prod.snd
  have hp : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ p :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := CoordinateExteriorRightTubeClosed))
  have hp' : IsLocalDiffeomorph oneHandlePieceModel
      oneHandlePieceModel ∞ p' :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      oneHandlePieceModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := OneHandlePiece))
  let e := coordinateExteriorRightTubeOneHandleDiffeomorph
  let F := (Homeomorph.refl (ZMod m)).prodCongr
    coordinateExteriorRightTubeOneHandleHomeomorph
  exact diffeomorphOfHomeomorphOverDiffeomorph
    coordinateUnlinkExteriorModel oneHandlePieceModel p p' hp hp' e F (by
      intro z
      change coordinateExteriorRightTubeOneHandleHomeomorph z.2 =
        coordinateExteriorRightTubeOneHandleDiffeomorph z.2
      exact (coordinateExteriorRightTubeOneHandleDiffeomorph_apply z.2).symm)

@[simp] theorem coordinateExteriorRightTubeClosedOneHandleFamilyDiffeomorph_apply
    (m : ℕ)
    (z : ZMod m × CoordinateExteriorRightTubeClosed) :
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    coordinateExteriorRightTubeClosedOneHandleFamilyDiffeomorph m z =
      (z.1, coordinateExteriorRightTubeOneHandleHomeomorph z.2) :=
  rfl

noncomputable def coordinateExteriorPlanarNeckLeftSmoothCappingRightTubeClosedFamilyDiffeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, coordinateUnlinkExteriorModel⟯
        (ZMod m × CoordinateExteriorRightTubeClosed) := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ := discreteProductChartedSpace OneHandleModelSpace
    (ZMod m) OneHandlePiece
  exact (coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph m).trans
    (coordinateExteriorRightTubeClosedOneHandleFamilyDiffeomorph m).symm

@[simp] theorem coordinateExteriorPlanarNeckLeftSmoothCappingRightTubeClosedFamilyDiffeomorph_apply
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m) :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    coordinateExteriorPlanarNeckLeftSmoothCappingRightTubeClosedFamilyDiffeomorph m z =
      (CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
        m).rightTubeHomeomorph z := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ := discreteProductChartedSpace OneHandleModelSpace
    (ZMod m) OneHandlePiece
  simp only [coordinateExteriorPlanarNeckLeftSmoothCappingRightTubeClosedFamilyDiffeomorph,
    Diffeomorph.coe_trans, Function.comp_apply]
  apply (coordinateExteriorRightTubeClosedOneHandleFamilyDiffeomorph m).injective
  calc
    _ = coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph m z :=
      (coordinateExteriorRightTubeClosedOneHandleFamilyDiffeomorph m).apply_symm_apply _
    _ = coordinateExteriorRightTubeClosedOneHandleFamilyDiffeomorph m
        ((CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
          m).rightTubeHomeomorph z) := by
      rw [coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph_apply]
      rfl

variable (m : ℕ) [NeZero m]

/-! ## Right common-target literal complement -/

private abbrev rightCutAttaching :=
  coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m

private abbrev roundedCapAttaching :=
  coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m

private abbrev rightCappingToDirectCommonModel :=
  coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph m

/-- The actual rounded-cap interior in the standard right-tube power-pullback target. -/
def coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapInterior :
    Set (CoordinateExteriorRightTubePowerPullback m) := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  exact (rightCappingToDirectCommonModel m).toHomeomorph ''
    (topologicalPushoutInr (rightCutAttaching m) (roundedCapAttaching m) ''
      coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m)

/-- The actual closed rounded-cap image in the standard right-tube power-pullback target. -/
private def coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage :
    Set (CoordinateExteriorRightTubePowerPullback m) := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  exact range ((rightCappingToDirectCommonModel m).toHomeomorph ∘
    topologicalPushoutInr (rightCutAttaching m) (roundedCapAttaching m))

/-- Carrier of the literal right common-target complement. -/
def coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier :
    Set (CoordinateExteriorRightTubePowerPullback m) :=
  (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapInterior m)ᶜ

abbrev CoordinateExteriorPlanarNeckRightDirectCommonModelComplement := CollaredCutSide
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)

private theorem
    coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapInterior_subset_closedImage :
    coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapInterior m ⊆
      coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m := by
  rintro z ⟨w, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨y, rfl⟩

private theorem
    coordinateExteriorPlanarNeckRightDirectCommonModel_offBoundary_eq_compl_closedImage :
    collaredCutSideOffBoundary
      (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m) =
      (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m)ᶜ := by
  apply Set.Subset.antisymm
  · intro z hz
    exact hz.2
  · intro z hz
    exact ⟨fun hInterior ↦ hz
      (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapInterior_subset_closedImage m
      hInterior), hz⟩

private theorem isClosed_coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage :
    IsClosed (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m) := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  have hclosed : IsClosed (range
      (topologicalPushoutInr (rightCutAttaching m) (roundedCapAttaching m))) :=
    isClosed_range_topologicalPushoutInr
      (rightCutAttaching m) (roundedCapAttaching m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
  rw [coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage]
  rw [Set.range_comp]
  exact (rightCappingToDirectCommonModel m).toHomeomorph.isClosedMap _ hclosed

private theorem isOpen_coordinateExteriorPlanarNeckRightDirectCommonModel_offBoundary :
    IsOpen (collaredCutSideOffBoundary
      (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
      (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m)) := by
  rw [coordinateExteriorPlanarNeckRightDirectCommonModel_offBoundary_eq_compl_closedImage m]
  exact (isClosed_coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage
    m).isOpen_compl

/-- Compact right cut identified with the literal common-target complement. -/
def compactNeckRightCutHomeomorphDirectCommonModelComplement :
    CompactNeckRightCut m ≃ₜ CoordinateExteriorPlanarNeckRightDirectCommonModelComplement m := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let A : Set (CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping m) :=
    topologicalPushoutInr (rightCutAttaching m) (roundedCapAttaching m) ''
      coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m
  exact
    ((isEmbedding_topologicalPushoutInl
        (rightCutAttaching m) (roundedCapAttaching m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
      ).toHomeomorph.trans
        (Homeomorph.setCongr (by
          dsimp only [A]
          exact range_topologicalPushoutInl_eq_compl_image_inr_compl_range _ _
            (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap
              m).injective))).trans <|
    (((rightCappingToDirectCommonModel m).toHomeomorph.image Aᶜ).trans <|
      Homeomorph.setCongr (by
        simpa [coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier,
          coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapInterior, A] using
          (rightCappingToDirectCommonModel m).toHomeomorph.toEquiv.image_compl A))

@[simp] theorem compactNeckRightCutHomeomorphDirectCommonModelComplement_coe
    (x : CompactNeckRightCut m) :
    (compactNeckRightCutHomeomorphDirectCommonModelComplement m x :
        CoordinateExteriorRightTubePowerPullback m) =
      rightCappingToDirectCommonModel m
        (topologicalPushoutInl (rightCutAttaching m) (roundedCapAttaching m) x) := by
  rfl

/-- The compact-cut half collar transported into the literal common target. -/
private def coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient
    (p : ZMod m × EuclideanFourBallCollarDomain) :
    CoordinateExteriorRightTubePowerPullback m :=
  (compactNeckRightCutHomeomorphDirectCommonModelComplement m
    ⟨compactNeckRightBoundaryCollarMap m p,
      compactNeckRightBoundaryCollarMap_range_subset m (mem_range_self p)⟩ :
      CoordinateExteriorPlanarNeckRightDirectCommonModelComplement m)

private theorem
    range_rightComplementCollarAmbient_subset :
    range (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m) ⊆
      coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m := by
  rintro _ ⟨p, rfl⟩
  exact (compactNeckRightCutHomeomorphDirectCommonModelComplement m
    ⟨compactNeckRightBoundaryCollarMap m p,
      compactNeckRightBoundaryCollarMap_range_subset m (mem_range_self p)⟩).2

private theorem
    isOpenEmbedding_rightComplementBoundaryCollar :
    IsOpenEmbedding (collaredCutSideHalfCollarMap
      (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
      (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m)
      (range_rightComplementCollarAmbient_subset
        m)) := by
  let sourceCollar := collaredCutSideHalfCollarMap
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
    (compactNeckRightBoundaryCollarMap m)
    (compactNeckRightBoundaryCollarMap_range_subset m)
  have h := (compactNeckRightCutHomeomorphDirectCommonModelComplement m).isOpenEmbedding.comp
    (isOpenEmbedding_compactNeckRightBoundaryCollarMap_toCut m)
  have hfun : (collaredCutSideHalfCollarMap
      (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
      (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m)
      (range_rightComplementCollarAmbient_subset m)) =
      (compactNeckRightCutHomeomorphDirectCommonModelComplement m) ∘ sourceCollar := by
    funext p
    apply Subtype.ext
    rfl
  rw [hfun]
  exact h

private theorem coordinateExteriorPlanarNeckRightDirectCommonModelComplement_collarCoverage
    (z : CoordinateExteriorPlanarNeckRightDirectCommonModelComplement m) :
    z.1 ∈ collaredCutSideOffBoundary
      (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m) ∨
      z.1 ∈ range (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m)
        := by
  let x := (compactNeckRightCutHomeomorphDirectCommonModelComplement m).symm z
  rcases compactNeckRightCut_collarCoverage m x with hx | hx
  · left
    rw [coordinateExteriorPlanarNeckRightDirectCommonModel_offBoundary_eq_compl_closedImage m]
    intro hzClosed
    rcases hzClosed with ⟨y, hy⟩
    have hxz := congrArg Subtype.val
      ((compactNeckRightCutHomeomorphDirectCommonModelComplement m).apply_symm_apply z)
    have hEq : topologicalPushoutInl (rightCutAttaching m) (roundedCapAttaching m) x =
        topologicalPushoutInr (rightCutAttaching m) (roundedCapAttaching m) y := by
      apply (rightCappingToDirectCommonModel m).injective
      exact hxz.trans hy.symm
    obtain ⟨a, hfa, _⟩ :=
      (topologicalPushoutInl_eq_inr_iff
        (rightCutAttaching m) (roundedCapAttaching m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m).injective
        x y).mp hEq
    apply hx.2
    have hxRange : x ∈ range (rightCutAttaching m) := ⟨a, hfa⟩
    rw [range_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap] at hxRange
    exact hxRange
  · right
    obtain ⟨p, hp⟩ := hx
    refine ⟨p, ?_⟩
    rw [← (compactNeckRightCutHomeomorphDirectCommonModelComplement m).apply_symm_apply z]
    simp only [coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient,
      compactNeckRightCutHomeomorphDirectCommonModelComplement_coe]
    apply congrArg (fun q :
      CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping m ↦
        rightCappingToDirectCommonModel m q)
    change
        (topologicalPushoutInl (rightCutAttaching m) (roundedCapAttaching m)
          ⟨compactNeckRightBoundaryCollarMap m p,
            compactNeckRightBoundaryCollarMap_range_subset m (mem_range_self p)⟩) =
        (topologicalPushoutInl (rightCutAttaching m) (roundedCapAttaching m) x)
    congr 2

private def coordinateExteriorPlanarNeckRightDirectCommonModelSourceBoundaryCollar
    (p : ZMod m × EuclideanFourBallCollarDomain) : CompactNeckRightCut m :=
  ⟨compactNeckRightBoundaryCollarMap m p,
    compactNeckRightBoundaryCollarMap_range_subset m (mem_range_self p)⟩

private theorem
    isLocalDiffeomorph_coordinateExteriorPlanarNeckRightDirectCommonModelSourceBoundaryCollar :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
        (coordinateExteriorPlanarNeckRightDirectCommonModelSourceBoundaryCollar m) := by
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ := compactNeckRightCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckRightCut m) :=
    isManifold_compactNeckRightCut m
  have hcompat : ∀ i j : CollaredCutSideAtlasIndex
      (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
      (ZMod m × EuclideanFourBallCollarDomain),
      (collaredCutSideAtlasChart (H := CoordinateUnlinkExteriorModelSpace)
        (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
        (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
        (isOpen_compactNeckRightCut_offBoundary m)
        (compactNeckRightBoundaryCollarMap m)
        (compactNeckRightBoundaryCollarMap_range_subset m)
        (isOpenEmbedding_compactNeckRightBoundaryCollarMap_toCut m) i).symm.trans
          (collaredCutSideAtlasChart (H := CoordinateUnlinkExteriorModelSpace)
            (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
            (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
            (isOpen_compactNeckRightCut_offBoundary m)
            (compactNeckRightBoundaryCollarMap m)
            (compactNeckRightBoundaryCollarMap_range_subset m)
            (isOpenEmbedding_compactNeckRightBoundaryCollarMap_toCut m) j) ∈
        contDiffGroupoid ∞ coordinateUnlinkExteriorModel := by
    intro i j
    apply IsManifold.compatible_of_mem_maximalAtlas
    · apply IsManifold.subset_maximalAtlas
      exact ⟨i, rfl⟩
    · apply IsManifold.subset_maximalAtlas
      exact ⟨j, rfl⟩
  change IsLocalDiffeomorph coordinateUnlinkExteriorModel
    coordinateUnlinkExteriorModel ∞
    (collaredCutSideHalfCollarMap
      (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
      (compactNeckRightBoundaryCollarMap m)
      (compactNeckRightBoundaryCollarMap_range_subset m))
  exact isLocalDiffeomorph_collaredCutSideHalfCollarMap
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
      (isOpen_compactNeckRightCut_offBoundary m)
      (compactNeckRightBoundaryCollarMap m)
      (compactNeckRightBoundaryCollarMap_range_subset m)
      (isOpenEmbedding_compactNeckRightBoundaryCollarMap_toCut m)
      (compactNeckRightCut_collarCoverage m) hcompat

private def coordinateExteriorPlanarNeckRightDirectCommonModelCappingCutOffSeamOpens : Opens
    (CompactNeckRightCut m) :=
  topologicalPushoutInlOffSeamOpens (rightCutAttaching m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)

private def coordinateExteriorPlanarNeckRightDirectCommonModelPositiveCollarOpens :
    Opens (ZMod m × EuclideanFourBallCollarDomain) := by
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := compactNeckRightCutChartedSpace m
  let U := coordinateExteriorPlanarNeckRightDirectCommonModelCappingCutOffSeamOpens m
  exact ⟨(coordinateExteriorPlanarNeckRightDirectCommonModelSourceBoundaryCollar m) ⁻¹' U,
    U.2.preimage
      (isLocalDiffeomorph_coordinateExteriorPlanarNeckRightDirectCommonModelSourceBoundaryCollar
        m).contMDiff.continuous⟩

private theorem
    rightComplementCollar_mem_sourceOffBoundary_of_mem_targetOffBoundary
    (p : ZMod m × EuclideanFourBallCollarDomain)
    (hp : coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m p ∈
      collaredCutSideOffBoundary
        (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m)) :
    coordinateExteriorPlanarNeckRightDirectCommonModelSourceBoundaryCollar m p ∈
      coordinateExteriorPlanarNeckRightDirectCommonModelCappingCutOffSeamOpens m := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  change coordinateExteriorPlanarNeckRightDirectCommonModelSourceBoundaryCollar m p ∉ range
    (rightCutAttaching m)
  intro hpRange
  apply hp.2
  obtain ⟨a, ha⟩ := hpRange
  refine ⟨(roundedCapAttaching m) a, ?_⟩
  change (rightCappingToDirectCommonModel m).toHomeomorph
      (topologicalPushoutInr (rightCutAttaching m) (roundedCapAttaching m)
        ((roundedCapAttaching m) a)) =
          coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m p
  rw [← topologicalPushout_condition (rightCutAttaching m)
    (roundedCapAttaching m) a]
  simp only [coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient,
    compactNeckRightCutHomeomorphDirectCommonModelComplement_coe]
  exact congrArg (fun q ↦ rightCappingToDirectCommonModel m
    (topologicalPushoutInl (rightCutAttaching m) (roundedCapAttaching m) q)) ha

private theorem
    isLocalDiffeomorphOn_rightComplementCollarAmbient :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m)
      ((coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m) ⁻¹'
        collaredCutSideOffBoundary
          (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
          (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m)) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := compactNeckRightCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckRightCut m) :=
    isManifold_compactNeckRightCut m
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullbackStandard m
  let W := coordinateExteriorPlanarNeckRightDirectCommonModelPositiveCollarOpens m
  let U := coordinateExteriorPlanarNeckRightDirectCommonModelCappingCutOffSeamOpens m
  let c := coordinateExteriorPlanarNeckRightDirectCommonModelSourceBoundaryCollar m
  have hmem (q : W) : c q.1 ∈ U := by
    exact q.2
  let r : W → U := restrictToOpens c W U hmem
  have hr : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ r :=
    isLocalDiffeomorph_restrictToOpens coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel c W U hmem
      (isLocalDiffeomorph_coordinateExteriorPlanarNeckRightDirectCommonModelSourceBoundaryCollar m)
  let F : U → CoordinateExteriorRightTubePowerPullback m :=
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m ∘
      topologicalPushoutInlOffSeamMap'
        (rightCutAttaching m) (roundedCapAttaching m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
  have hF : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ F := by
    exact
      isLocalDiffeomorph_coordinateExteriorPlanarNeckRightSmoothCappingRightTube_cutOffSeam m
  have hcomp : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (F ∘ r) := by
    intro q
    exact (hr q).comp coordinateUnlinkExteriorModel
      (CoordinateExteriorRightTubePowerPullback m) (hF (r q))
  have hactual : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      ((coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m) ∘
        (Subtype.val : W → _)) := by
    have hfun : F ∘ r =
        (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m) ∘
          (Subtype.val : W → _) := by
      funext q
      change coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m
          (topologicalPushoutInl (rightCutAttaching m) (roundedCapAttaching m)
            (coordinateExteriorPlanarNeckRightDirectCommonModelSourceBoundaryCollar m q.1)) =
        coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m q.1
      rw [coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient,
        compactNeckRightCutHomeomorphDirectCommonModelComplement_coe]
      exact (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph_apply
        m _).symm
    rw [← hfun]
    exact hcomp
  rintro ⟨p, hp⟩
  have hpW : p ∈ W :=
    rightComplementCollar_mem_sourceOffBoundary_of_mem_targetOffBoundary m p hp
  let q : W := ⟨p, hpW⟩
  exact isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m) (Subtype.val :
      W → _)
    (isLocalDiffeomorph_opensSubtypeVal coordinateUnlinkExteriorModel W)
    hactual q

/-- The direct ambient/collar atlas on the literal right common-target complement. -/
@[instance_reducible]
def coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateExteriorPlanarNeckRightDirectCommonModelComplement m) := by
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullbackStandard m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  exact collaredCutSideChartedSpace
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m)
    (isOpen_coordinateExteriorPlanarNeckRightDirectCommonModel_offBoundary m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m)
    (range_rightComplementCollarAmbient_subset m)
    (isOpenEmbedding_rightComplementBoundaryCollar m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplement_collarCoverage m)

/-- The literal right common-target complement is a manifold for its direct atlas. -/
theorem isManifold_coordinateExteriorPlanarNeckRightDirectCommonModelComplement :
    letI := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorPlanarNeckRightDirectCommonModelComplement m) := by
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullbackStandard m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  exact isManifold_collaredCutSideChartedSpace_of_localDiffeomorphOn
    coordinateUnlinkExteriorModel ∞
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m)
    (isOpen_coordinateExteriorPlanarNeckRightDirectCommonModel_offBoundary m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m)
    (range_rightComplementCollarAmbient_subset m)
    (isOpenEmbedding_rightComplementBoundaryCollar m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplement_collarCoverage m)
    (isLocalDiffeomorphOn_rightComplementCollarAmbient m)

private theorem coordinateExteriorPlanarNeckRightDirectCommonModelComplement_atlasCompatible :
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
    ∀ i j : CollaredCutSideAtlasIndex
        (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m)
        (ZMod m × EuclideanFourBallCollarDomain),
      (collaredCutSideAtlasChart (H := CoordinateUnlinkExteriorModelSpace)
        (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m)
        (isOpen_coordinateExteriorPlanarNeckRightDirectCommonModel_offBoundary m)
        (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m)
        (range_rightComplementCollarAmbient_subset m)
        (isOpenEmbedding_rightComplementBoundaryCollar m) i).symm.trans
          (collaredCutSideAtlasChart (H := CoordinateUnlinkExteriorModelSpace)
            (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
            (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m)
            (isOpen_coordinateExteriorPlanarNeckRightDirectCommonModel_offBoundary m)
            (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m)
            (range_rightComplementCollarAmbient_subset m)
            (isOpenEmbedding_rightComplementBoundaryCollar m) j) ∈
        contDiffGroupoid ∞ coordinateUnlinkExteriorModel := by
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullbackStandard m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
  let hman : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorPlanarNeckRightDirectCommonModelComplement m) :=
        isManifold_coordinateExteriorPlanarNeckRightDirectCommonModelComplement m
  intro i j
  exact hman.compatible ⟨i, rfl⟩ ⟨j, rfl⟩

private theorem
    isLocalDiffeomorph_rightComplementBoundaryCollar :
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (collaredCutSideHalfCollarMap
        (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m)
        (range_rightComplementCollarAmbient_subset
          m)) := by
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullbackStandard m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
  exact isLocalDiffeomorph_collaredCutSideHalfCollarMap
    coordinateUnlinkExteriorModel ∞
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m)
    (isOpen_coordinateExteriorPlanarNeckRightDirectCommonModel_offBoundary m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m)
    (range_rightComplementCollarAmbient_subset m)
    (isOpenEmbedding_rightComplementBoundaryCollar m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplement_collarCoverage m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplement_atlasCompatible m)

private theorem
    isLocalDiffeomorph_coordinateExteriorPlanarNeckRightDirectCommonModelComplementOffBoundaryMap :
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (collaredCutSideOffBoundaryOpensMap
        (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m)
        (isOpen_coordinateExteriorPlanarNeckRightDirectCommonModel_offBoundary m)) := by
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullbackStandard m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
  exact isLocalDiffeomorph_collaredCutSideOffBoundaryMap
    coordinateUnlinkExteriorModel ∞
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m)
    (isOpen_coordinateExteriorPlanarNeckRightDirectCommonModel_offBoundary m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m)
    (range_rightComplementCollarAmbient_subset m)
    (isOpenEmbedding_rightComplementBoundaryCollar m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplement_collarCoverage m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplement_atlasCompatible m)

private theorem isLocalDiffeomorph_compactNeckRightCutHomeomorphDirectCommonModelComplement :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (compactNeckRightCutHomeomorphDirectCommonModelComplement m) := by
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ := compactNeckRightCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckRightCut m) :=
    isManifold_compactNeckRightCut m
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullbackStandard m
  let _ := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
    (CoordinateExteriorPlanarNeckRightDirectCommonModelComplement m) :=
    isManifold_coordinateExteriorPlanarNeckRightDirectCommonModelComplement m
  let P := ZMod m × EuclideanFourBallCollarDomain
  let c₁ : P → CompactNeckRightCut m :=
    coordinateExteriorPlanarNeckRightDirectCommonModelSourceBoundaryCollar m
  let U := coordinateExteriorPlanarNeckRightDirectCommonModelCappingCutOffSeamOpens m
  let Uall : Opens U := ⊤
  let c₂ : Uall → CompactNeckRightCut m := fun q ↦ q.1.1
  have hc₁ : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ c₁ :=
    isLocalDiffeomorph_coordinateExteriorPlanarNeckRightDirectCommonModelSourceBoundaryCollar m
  have hc₂ : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ c₂ := by
    let h₀ := isLocalDiffeomorph_opensSubtypeVal coordinateUnlinkExteriorModel Uall
    let h₁ := isLocalDiffeomorph_opensSubtypeVal coordinateUnlinkExteriorModel U
    intro q
    exact (h₀ q).comp coordinateUnlinkExteriorModel
      (CompactNeckRightCut m) (h₁ q.1)
  let targetCollar := collaredCutSideHalfCollarMap
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCollarAmbient m)
    (range_rightComplementCollarAmbient_subset m)
  have hHc₁ : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      ((compactNeckRightCutHomeomorphDirectCommonModelComplement m) ∘ c₁) := by
    have hfun : (compactNeckRightCutHomeomorphDirectCommonModelComplement m) ∘ c₁ =
        targetCollar := by
      funext p
      apply Subtype.ext
      rfl
    rw [hfun]
    exact
      isLocalDiffeomorph_rightComplementBoundaryCollar m
  let V := collaredCutSideOffBoundaryOpens
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
    (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m)
    (isOpen_coordinateExteriorPlanarNeckRightDirectCommonModel_offBoundary m)
  let F : U → CoordinateExteriorRightTubePowerPullback m :=
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m ∘
      topologicalPushoutInlOffSeamMap'
        (rightCutAttaching m) (roundedCapAttaching m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
  have hF : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ F :=
    isLocalDiffeomorph_coordinateExteriorPlanarNeckRightSmoothCappingRightTube_cutOffSeam m
  have hmem (q : Uall) : F q.1 ∈ V := by
    change F q.1 ∈ collaredCutSideOffBoundary
      (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m)
    rw [coordinateExteriorPlanarNeckRightDirectCommonModel_offBoundary_eq_compl_closedImage m]
    intro hclosed
    rcases hclosed with ⟨y, hy⟩
    have heq :
        topologicalPushoutInl (rightCutAttaching m) (roundedCapAttaching m) q.1.1 =
          topologicalPushoutInr (rightCutAttaching m) (roundedCapAttaching m) y := by
      apply (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m).injective
      exact hy.symm
    obtain ⟨a, hfa, _⟩ :=
      (topologicalPushoutInl_eq_inr_iff
        (rightCutAttaching m) (roundedCapAttaching m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m).injective
        q.1.1 y).mp heq
    exact q.1.2 ⟨a, hfa⟩
  let r : Uall → V := restrictToOpens F Uall V hmem
  have hr : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ r :=
    isLocalDiffeomorph_restrictToOpens coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel F Uall V hmem hF
  let d : V → CoordinateExteriorPlanarNeckRightDirectCommonModelComplement m :=
    collaredCutSideOffBoundaryOpensMap
      (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)
      (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapClosedImage m)
      (isOpen_coordinateExteriorPlanarNeckRightDirectCommonModel_offBoundary m)
  have hd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ d :=
    isLocalDiffeomorph_coordinateExteriorPlanarNeckRightDirectCommonModelComplementOffBoundaryMap m
  have hdr : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (d ∘ r) := by
    intro q
    exact (hr q).comp coordinateUnlinkExteriorModel
      (CoordinateExteriorPlanarNeckRightDirectCommonModelComplement m) (hd (r q))
  have hHc₂ : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      ((compactNeckRightCutHomeomorphDirectCommonModelComplement m) ∘ c₂) := by
    have hfun : (compactNeckRightCutHomeomorphDirectCommonModelComplement m) ∘ c₂ = d ∘ r := by
      funext q
      apply Subtype.ext
      change rightCappingToDirectCommonModel m
          (topologicalPushoutInl (rightCutAttaching m) (roundedCapAttaching m) q.1.1) =
        coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m
          (topologicalPushoutInl (rightCutAttaching m) (roundedCapAttaching m) q.1.1)
      exact coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph_apply m _
    rw [hfun]
    exact hdr
  have hcover : ∀ x : CompactNeckRightCut m,
      (∃ p : P, c₁ p = x) ∨ (∃ q : Uall, c₂ q = x) ∨
        (∃ p : P, c₁ p = x) := by
    intro x
    by_cases hx : x ∈ range (rightCutAttaching m)
    · rcases compactNeckRightCut_collarCoverage m x with hoff | hcollar
      · exfalso
        apply hoff.2
        have hxSeam := hx
        rw [range_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap] at hxSeam
        exact hxSeam
      · left
        obtain ⟨p, hp⟩ := hcollar
        refine ⟨p, ?_⟩
        exact Subtype.ext hp
    · right
      left
      let q : U := ⟨x, hx⟩
      refine ⟨⟨q, Set.mem_univ q⟩, rfl⟩
  exact isLocalDiffeomorph_of_three_localDiffeomorph_parametrizations
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    (compactNeckRightCutHomeomorphDirectCommonModelComplement m)
    c₁ c₂ c₁ hc₁ hc₂ hc₁ hHc₁ hHc₂ hHc₁ hcover

/-- The compact right cut is diffeomorphic to the literal common-target complement
for the direct complement atlas. -/
def compactNeckRightCutDiffeomorphDirectCommonModelComplement :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
    CompactNeckRightCut m ≃ₘ^∞⟮coordinateUnlinkExteriorModel,
      coordinateUnlinkExteriorModel⟯
        CoordinateExteriorPlanarNeckRightDirectCommonModelComplement m := by
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := compactNeckRightCutChartedSpace m
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
  exact diffeomorphOfHomeomorphIsLocalDiffeomorph
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    (compactNeckRightCutHomeomorphDirectCommonModelComplement m)
    (isLocalDiffeomorph_compactNeckRightCutHomeomorphDirectCommonModelComplement m)

@[simp] theorem compactNeckRightCutDiffeomorphDirectCommonModelComplement_apply
    (x : CompactNeckRightCut m) :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
    compactNeckRightCutDiffeomorphDirectCommonModelComplement m x =
      compactNeckRightCutHomeomorphDirectCommonModelComplement m x := by
  rfl

/-! ## Left common-target literal complement -/

private abbrev leftCutAttaching :=
  coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m

private abbrev leftCappingToDirectCommonModel :=
  coordinateExteriorPlanarNeckLeftSmoothCappingRightTubeClosedFamilyDiffeomorph m

/-- The actual rounded-cap interior in the common closed right-tube family target. -/
def coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapInterior :
    Set (ZMod m × CoordinateExteriorRightTubeClosed) := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  exact (leftCappingToDirectCommonModel m).toHomeomorph ''
    (topologicalPushoutInr (leftCutAttaching m) (roundedCapAttaching m) ''
      coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m)

/-- The actual closed rounded-cap image in the common closed right-tube family target. -/
private def coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage :
    Set (ZMod m × CoordinateExteriorRightTubeClosed) := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  exact range ((leftCappingToDirectCommonModel m).toHomeomorph ∘
    topologicalPushoutInr (leftCutAttaching m) (roundedCapAttaching m))

/-- Carrier of the literal left common-target complement. -/
def coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier :
    Set (ZMod m × CoordinateExteriorRightTubeClosed) :=
  (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapInterior m)ᶜ

abbrev CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement := CollaredCutSide
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)

private theorem
    coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapInterior_subset_closedImage :
    coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapInterior m ⊆
      coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m := by
  rintro z ⟨w, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨y, rfl⟩

private theorem coordinateExteriorPlanarNeckLeftDirectCommonModel_offBoundary_eq_compl_closedImage :
    collaredCutSideOffBoundary
      (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m) =
      (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m)ᶜ := by
  apply Set.Subset.antisymm
  · intro z hz
    exact hz.2
  · intro z hz
    exact ⟨fun hInterior ↦ hz
      (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapInterior_subset_closedImage m
        hInterior), hz⟩

private theorem isClosed_coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage :
    IsClosed (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m) := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  have hclosed : IsClosed (range
      (topologicalPushoutInr (leftCutAttaching m) (roundedCapAttaching m))) :=
    isClosed_range_topologicalPushoutInr
      (leftCutAttaching m) (roundedCapAttaching m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
  rw [coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage]
  rw [Set.range_comp]
  exact (leftCappingToDirectCommonModel m).toHomeomorph.isClosedMap _ hclosed

private theorem isOpen_coordinateExteriorPlanarNeckLeftDirectCommonModel_offBoundary :
    IsOpen (collaredCutSideOffBoundary
      (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
      (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m)) := by
  rw [coordinateExteriorPlanarNeckLeftDirectCommonModel_offBoundary_eq_compl_closedImage m]
  exact (isClosed_coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage
    m).isOpen_compl

/-- Compact left cut identified with the literal common-target complement. -/
def compactNeckLeftCutHomeomorphDirectCommonModelComplement :
    CompactNeckLeftCut m ≃ₜ CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement m := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let A : Set (CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m) :=
    topologicalPushoutInr (leftCutAttaching m) (roundedCapAttaching m) ''
      coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m
  exact
    ((isEmbedding_topologicalPushoutInl
        (leftCutAttaching m) (roundedCapAttaching m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
      ).toHomeomorph.trans
        (Homeomorph.setCongr (by
          dsimp only [A]
          exact range_topologicalPushoutInl_eq_compl_image_inr_compl_range _ _
            (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap
              m).injective))).trans <|
    (((leftCappingToDirectCommonModel m).toHomeomorph.image Aᶜ).trans <|
      Homeomorph.setCongr (by
        simpa [coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier,
          coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapInterior, A] using
          (leftCappingToDirectCommonModel m).toHomeomorph.toEquiv.image_compl A))

@[simp] theorem compactNeckLeftCutHomeomorphDirectCommonModelComplement_coe
    (x : CompactNeckLeftCut m) :
    (compactNeckLeftCutHomeomorphDirectCommonModelComplement m x :
        ZMod m × CoordinateExteriorRightTubeClosed) =
      leftCappingToDirectCommonModel m
        (topologicalPushoutInl (leftCutAttaching m) (roundedCapAttaching m) x) := by
  rfl

/-- The compact-cut half collar transported into the literal common target. -/
private def coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient
    (p : ZMod m × EuclideanFourBallCollarDomain) :
    ZMod m × CoordinateExteriorRightTubeClosed :=
  (compactNeckLeftCutHomeomorphDirectCommonModelComplement m
    ⟨compactNeckLeftBoundaryCollarMap m p,
      compactNeckLeftBoundaryCollarMap_range_subset m (mem_range_self p)⟩ :
      CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement m)

private theorem
    range_leftComplementCollarAmbient_subset :
    range (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m) ⊆
      coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m := by
  rintro _ ⟨p, rfl⟩
  exact (compactNeckLeftCutHomeomorphDirectCommonModelComplement m
    ⟨compactNeckLeftBoundaryCollarMap m p,
      compactNeckLeftBoundaryCollarMap_range_subset m (mem_range_self p)⟩).2

private theorem
    isOpenEmbedding_leftComplementBoundaryCollar :
    IsOpenEmbedding (collaredCutSideHalfCollarMap
      (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
      (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m)
      (range_leftComplementCollarAmbient_subset m))
        := by
  let sourceCollar := collaredCutSideHalfCollarMap
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
    (compactNeckLeftBoundaryCollarMap m)
    (compactNeckLeftBoundaryCollarMap_range_subset m)
  have h := (compactNeckLeftCutHomeomorphDirectCommonModelComplement m).isOpenEmbedding.comp
    (isOpenEmbedding_compactNeckLeftBoundaryCollarMap_toCut m)
  have hfun : (collaredCutSideHalfCollarMap
      (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
      (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m)
      (range_leftComplementCollarAmbient_subset m)) =
      (compactNeckLeftCutHomeomorphDirectCommonModelComplement m) ∘ sourceCollar := by
    funext p
    apply Subtype.ext
    rfl
  rw [hfun]
  exact h

private theorem coordinateExteriorPlanarNeckLeftDirectCommonModelComplement_collarCoverage
    (z : CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement m) :
    z.1 ∈ collaredCutSideOffBoundary
      (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m) ∨
      z.1 ∈ range (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m) := by
  let x := (compactNeckLeftCutHomeomorphDirectCommonModelComplement m).symm z
  rcases compactNeckLeftCut_collarCoverage m x with hx | hx
  · left
    rw [coordinateExteriorPlanarNeckLeftDirectCommonModel_offBoundary_eq_compl_closedImage m]
    intro hzClosed
    rcases hzClosed with ⟨y, hy⟩
    have hxz := congrArg Subtype.val
      ((compactNeckLeftCutHomeomorphDirectCommonModelComplement m).apply_symm_apply z)
    have hEq : topologicalPushoutInl (leftCutAttaching m) (roundedCapAttaching m) x =
        topologicalPushoutInr (leftCutAttaching m) (roundedCapAttaching m) y := by
      apply (leftCappingToDirectCommonModel m).injective
      exact hxz.trans hy.symm
    obtain ⟨a, hfa, _⟩ :=
      (topologicalPushoutInl_eq_inr_iff
        (leftCutAttaching m) (roundedCapAttaching m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m).injective
        x y).mp hEq
    apply hx.2
    have hxRange : x ∈ range (leftCutAttaching m) := ⟨a, hfa⟩
    rw [range_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap] at hxRange
    exact hxRange
  · right
    obtain ⟨p, hp⟩ := hx
    refine ⟨p, ?_⟩
    rw [← (compactNeckLeftCutHomeomorphDirectCommonModelComplement m).apply_symm_apply z]
    simp only [coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient,
      compactNeckLeftCutHomeomorphDirectCommonModelComplement_coe]
    apply congrArg (fun q :
      CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m ↦
        leftCappingToDirectCommonModel m q)
    change
        (topologicalPushoutInl (leftCutAttaching m) (roundedCapAttaching m)
          ⟨compactNeckLeftBoundaryCollarMap m p,
            compactNeckLeftBoundaryCollarMap_range_subset m (mem_range_self p)⟩) =
        (topologicalPushoutInl (leftCutAttaching m) (roundedCapAttaching m) x)
    congr 2

private def coordinateExteriorPlanarNeckLeftDirectCommonModelSourceBoundaryCollar
    (p : ZMod m × EuclideanFourBallCollarDomain) : CompactNeckLeftCut m :=
  ⟨compactNeckLeftBoundaryCollarMap m p,
    compactNeckLeftBoundaryCollarMap_range_subset m (mem_range_self p)⟩

private theorem
    isLocalDiffeomorph_coordinateExteriorPlanarNeckLeftDirectCommonModelSourceBoundaryCollar :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
        (coordinateExteriorPlanarNeckLeftDirectCommonModelSourceBoundaryCollar m) := by
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ := compactNeckLeftCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckLeftCut m) :=
    isManifold_compactNeckLeftCut m
  have hcompat : ∀ i j : CollaredCutSideAtlasIndex
      (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
      (ZMod m × EuclideanFourBallCollarDomain),
      (collaredCutSideAtlasChart (H := CoordinateUnlinkExteriorModelSpace)
        (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
        (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
        (isOpen_compactNeckLeftCut_offBoundary m)
        (compactNeckLeftBoundaryCollarMap m)
        (compactNeckLeftBoundaryCollarMap_range_subset m)
        (isOpenEmbedding_compactNeckLeftBoundaryCollarMap_toCut m) i).symm.trans
          (collaredCutSideAtlasChart (H := CoordinateUnlinkExteriorModelSpace)
            (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
            (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
            (isOpen_compactNeckLeftCut_offBoundary m)
            (compactNeckLeftBoundaryCollarMap m)
            (compactNeckLeftBoundaryCollarMap_range_subset m)
            (isOpenEmbedding_compactNeckLeftBoundaryCollarMap_toCut m) j) ∈
        contDiffGroupoid ∞ coordinateUnlinkExteriorModel := by
    intro i j
    apply IsManifold.compatible_of_mem_maximalAtlas
    · apply IsManifold.subset_maximalAtlas
      exact ⟨i, rfl⟩
    · apply IsManifold.subset_maximalAtlas
      exact ⟨j, rfl⟩
  change IsLocalDiffeomorph coordinateUnlinkExteriorModel
    coordinateUnlinkExteriorModel ∞
    (collaredCutSideHalfCollarMap
      (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
      (compactNeckLeftBoundaryCollarMap m)
      (compactNeckLeftBoundaryCollarMap_range_subset m))
  exact isLocalDiffeomorph_collaredCutSideHalfCollarMap
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
      (isOpen_compactNeckLeftCut_offBoundary m)
      (compactNeckLeftBoundaryCollarMap m)
      (compactNeckLeftBoundaryCollarMap_range_subset m)
      (isOpenEmbedding_compactNeckLeftBoundaryCollarMap_toCut m)
      (compactNeckLeftCut_collarCoverage m) hcompat

private def coordinateExteriorPlanarNeckLeftDirectCommonModelCappingCutOffSeamOpens : Opens
    (CompactNeckLeftCut m) :=
  topologicalPushoutInlOffSeamOpens (leftCutAttaching m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)

private theorem
    isLocalDiffeomorph_coordinateExteriorPlanarNeckLeftDirectCommonModelCappingCutOffSeamToCommon :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      ((leftCappingToDirectCommonModel m).toHomeomorph ∘
        topologicalPushoutInlOffSeamMap'
          (leftCutAttaching m) (roundedCapAttaching m)
          (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)) := by
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := compactNeckLeftCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckLeftCut m) :=
    isManifold_compactNeckLeftCut m
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let hman : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m) :=
    isManifold_coordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m
  have hcompat : ∀ i j : TopologicalPushoutAtlasIndex
      (leftCutAttaching m) (roundedCapAttaching m)
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m),
      (topologicalPushoutAtlasChart (H := CoordinateUnlinkExteriorModelSpace)
        (leftCutAttaching m) (roundedCapAttaching m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m)
        (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m) i).symm.trans
          (topologicalPushoutAtlasChart (H := CoordinateUnlinkExteriorModelSpace)
            (leftCutAttaching m) (roundedCapAttaching m)
            (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
            (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
            (coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m)
            (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m) j) ∈
        contDiffGroupoid ∞ coordinateUnlinkExteriorModel := by
    intro i j
    exact hman.compatible ⟨i, rfl⟩ ⟨j, rfl⟩
  have hinl : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (topologicalPushoutInlOffSeamMap'
        (leftCutAttaching m) (roundedCapAttaching m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)) := by
    exact isLocalDiffeomorph_topologicalPushoutInlOffSeamMap'
      coordinateUnlinkExteriorModel ∞
      (leftCutAttaching m) (roundedCapAttaching m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
      (coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m)
      (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m)
      (coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap_attaching_coverage m)
      hcompat
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeClosed
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × CoordinateExteriorRightTubeClosed) :=
    isManifold_discreteProductChartedSpace coordinateUnlinkExteriorModel ∞
      (ZMod m) CoordinateExteriorRightTubeClosed
  intro q
  exact (hinl q).comp coordinateUnlinkExteriorModel
    (ZMod m × CoordinateExteriorRightTubeClosed)
    ((leftCappingToDirectCommonModel m).isLocalDiffeomorph _)

private def coordinateExteriorPlanarNeckLeftDirectCommonModelPositiveCollarOpens :
    Opens (ZMod m × EuclideanFourBallCollarDomain) := by
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := compactNeckLeftCutChartedSpace m
  let U := coordinateExteriorPlanarNeckLeftDirectCommonModelCappingCutOffSeamOpens m
  exact ⟨(coordinateExteriorPlanarNeckLeftDirectCommonModelSourceBoundaryCollar m) ⁻¹' U,
    U.2.preimage
      (isLocalDiffeomorph_coordinateExteriorPlanarNeckLeftDirectCommonModelSourceBoundaryCollar
        m).contMDiff.continuous⟩

private theorem
    leftComplementCollar_mem_sourceOffBoundary_of_mem_targetOffBoundary
    (p : ZMod m × EuclideanFourBallCollarDomain)
    (hp : coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m p ∈
      collaredCutSideOffBoundary
        (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m)) :
    coordinateExteriorPlanarNeckLeftDirectCommonModelSourceBoundaryCollar m p ∈
      coordinateExteriorPlanarNeckLeftDirectCommonModelCappingCutOffSeamOpens m := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  change coordinateExteriorPlanarNeckLeftDirectCommonModelSourceBoundaryCollar m p ∉ range
    (leftCutAttaching m)
  intro hpRange
  apply hp.2
  obtain ⟨a, ha⟩ := hpRange
  refine ⟨(roundedCapAttaching m) a, ?_⟩
  change (leftCappingToDirectCommonModel m).toHomeomorph
      (topologicalPushoutInr (leftCutAttaching m) (roundedCapAttaching m)
        ((roundedCapAttaching m) a)) =
          coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m p
  rw [← topologicalPushout_condition (leftCutAttaching m)
    (roundedCapAttaching m) a]
  simp only [coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient,
    compactNeckLeftCutHomeomorphDirectCommonModelComplement_coe]
  exact congrArg (fun q ↦ leftCappingToDirectCommonModel m
    (topologicalPushoutInl (leftCutAttaching m) (roundedCapAttaching m) q)) ha

private theorem
    isLocalDiffeomorphOn_leftComplementCollarAmbient :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m)
      ((coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m) ⁻¹'
        collaredCutSideOffBoundary
          (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
          (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m)) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := compactNeckLeftCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckLeftCut m) :=
    isManifold_compactNeckLeftCut m
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeClosed
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × CoordinateExteriorRightTubeClosed) :=
    isManifold_discreteProductChartedSpace coordinateUnlinkExteriorModel ∞
      (ZMod m) CoordinateExteriorRightTubeClosed
  let W := coordinateExteriorPlanarNeckLeftDirectCommonModelPositiveCollarOpens m
  let U := coordinateExteriorPlanarNeckLeftDirectCommonModelCappingCutOffSeamOpens m
  let c := coordinateExteriorPlanarNeckLeftDirectCommonModelSourceBoundaryCollar m
  have hmem (q : W) : c q.1 ∈ U := by
    exact q.2
  let r : W → U := restrictToOpens c W U hmem
  have hr : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ r :=
    isLocalDiffeomorph_restrictToOpens coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel c W U hmem
      (isLocalDiffeomorph_coordinateExteriorPlanarNeckLeftDirectCommonModelSourceBoundaryCollar m)
  let F : U → ZMod m × CoordinateExteriorRightTubeClosed :=
    (leftCappingToDirectCommonModel m).toHomeomorph ∘
      topologicalPushoutInlOffSeamMap'
        (leftCutAttaching m) (roundedCapAttaching m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
  have hF : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ F :=
    isLocalDiffeomorph_coordinateExteriorPlanarNeckLeftDirectCommonModelCappingCutOffSeamToCommon m
  have hcomp : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (F ∘ r) := by
    intro q
    exact (hr q).comp coordinateUnlinkExteriorModel
      (ZMod m × CoordinateExteriorRightTubeClosed) (hF (r q))
  have hactual : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      ((coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m) ∘
        (Subtype.val : W → _)) := by
    have hfun : F ∘ r =
        (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m) ∘
          (Subtype.val : W → _) := by
      funext q
      change (leftCappingToDirectCommonModel m).toHomeomorph
          (topologicalPushoutInl (leftCutAttaching m) (roundedCapAttaching m)
            (coordinateExteriorPlanarNeckLeftDirectCommonModelSourceBoundaryCollar m q.1)) =
        coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m q.1
      rw [coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient,
        compactNeckLeftCutHomeomorphDirectCommonModelComplement_coe]
      rfl
    rw [← hfun]
    exact hcomp
  rintro ⟨p, hp⟩
  have hpW : p ∈ W :=
    leftComplementCollar_mem_sourceOffBoundary_of_mem_targetOffBoundary m p hp
  let q : W := ⟨p, hpW⟩
  exact isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m) (Subtype.val :
      W → _)
    (isLocalDiffeomorph_opensSubtypeVal coordinateUnlinkExteriorModel W)
    hactual q

/-- The direct ambient/collar atlas on the literal left common-target complement. -/
@[instance_reducible]
def coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement m) := by
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeClosed
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × CoordinateExteriorRightTubeClosed) :=
    isManifold_discreteProductChartedSpace coordinateUnlinkExteriorModel ∞
      (ZMod m) CoordinateExteriorRightTubeClosed
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  exact collaredCutSideChartedSpace
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m)
    (isOpen_coordinateExteriorPlanarNeckLeftDirectCommonModel_offBoundary m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m)
    (range_leftComplementCollarAmbient_subset m)
    (isOpenEmbedding_leftComplementBoundaryCollar m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplement_collarCoverage m)

/-- The literal left common-target complement is a manifold for its direct atlas. -/
theorem isManifold_coordinateExteriorPlanarNeckLeftDirectCommonModelComplement :
    letI := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement m) := by
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeClosed
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × CoordinateExteriorRightTubeClosed) :=
    isManifold_discreteProductChartedSpace coordinateUnlinkExteriorModel ∞
      (ZMod m) CoordinateExteriorRightTubeClosed
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  exact isManifold_collaredCutSideChartedSpace_of_localDiffeomorphOn
    coordinateUnlinkExteriorModel ∞
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m)
    (isOpen_coordinateExteriorPlanarNeckLeftDirectCommonModel_offBoundary m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m)
    (range_leftComplementCollarAmbient_subset m)
    (isOpenEmbedding_leftComplementBoundaryCollar m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplement_collarCoverage m)
    (isLocalDiffeomorphOn_leftComplementCollarAmbient m)

private theorem coordinateExteriorPlanarNeckLeftDirectCommonModelComplement_atlasCompatible :
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
    ∀ i j : CollaredCutSideAtlasIndex
        (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m)
        (ZMod m × EuclideanFourBallCollarDomain),
      (collaredCutSideAtlasChart (H := CoordinateUnlinkExteriorModelSpace)
        (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m)
        (isOpen_coordinateExteriorPlanarNeckLeftDirectCommonModel_offBoundary m)
        (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m)
        (range_leftComplementCollarAmbient_subset m)
        (isOpenEmbedding_leftComplementBoundaryCollar m) i).symm.trans
          (collaredCutSideAtlasChart (H := CoordinateUnlinkExteriorModelSpace)
            (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
            (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m)
            (isOpen_coordinateExteriorPlanarNeckLeftDirectCommonModel_offBoundary m)
            (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m)
            (range_leftComplementCollarAmbient_subset m)
            (isOpenEmbedding_leftComplementBoundaryCollar m) j) ∈
        contDiffGroupoid ∞ coordinateUnlinkExteriorModel := by
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeClosed
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × CoordinateExteriorRightTubeClosed) :=
    isManifold_discreteProductChartedSpace coordinateUnlinkExteriorModel ∞
      (ZMod m) CoordinateExteriorRightTubeClosed
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
  let hman : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement m) :=
        isManifold_coordinateExteriorPlanarNeckLeftDirectCommonModelComplement m
  intro i j
  exact hman.compatible ⟨i, rfl⟩ ⟨j, rfl⟩

private theorem
    isLocalDiffeomorph_leftComplementBoundaryCollar :
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (collaredCutSideHalfCollarMap
        (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m)
        (range_leftComplementCollarAmbient_subset
          m)) := by
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeClosed
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × CoordinateExteriorRightTubeClosed) :=
    isManifold_discreteProductChartedSpace coordinateUnlinkExteriorModel ∞
      (ZMod m) CoordinateExteriorRightTubeClosed
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
  exact isLocalDiffeomorph_collaredCutSideHalfCollarMap
    coordinateUnlinkExteriorModel ∞
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m)
    (isOpen_coordinateExteriorPlanarNeckLeftDirectCommonModel_offBoundary m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m)
    (range_leftComplementCollarAmbient_subset m)
    (isOpenEmbedding_leftComplementBoundaryCollar m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplement_collarCoverage m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplement_atlasCompatible m)

private theorem
    isLocalDiffeomorph_coordinateExteriorPlanarNeckLeftDirectCommonModelComplementOffBoundaryMap :
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (collaredCutSideOffBoundaryOpensMap
        (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m)
        (isOpen_coordinateExteriorPlanarNeckLeftDirectCommonModel_offBoundary m)) := by
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeClosed
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × CoordinateExteriorRightTubeClosed) :=
    isManifold_discreteProductChartedSpace coordinateUnlinkExteriorModel ∞
      (ZMod m) CoordinateExteriorRightTubeClosed
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
  exact isLocalDiffeomorph_collaredCutSideOffBoundaryMap
    coordinateUnlinkExteriorModel ∞
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m)
    (isOpen_coordinateExteriorPlanarNeckLeftDirectCommonModel_offBoundary m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m)
    (range_leftComplementCollarAmbient_subset m)
    (isOpenEmbedding_leftComplementBoundaryCollar m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplement_collarCoverage m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplement_atlasCompatible m)

private theorem isLocalDiffeomorph_compactNeckLeftCutHomeomorphDirectCommonModelComplement :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (compactNeckLeftCutHomeomorphDirectCommonModelComplement m) := by
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ := compactNeckLeftCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckLeftCut m) :=
    isManifold_compactNeckLeftCut m
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeClosed
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × CoordinateExteriorRightTubeClosed) :=
    isManifold_discreteProductChartedSpace coordinateUnlinkExteriorModel ∞
      (ZMod m) CoordinateExteriorRightTubeClosed
  let _ := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
    (CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement m) :=
    isManifold_coordinateExteriorPlanarNeckLeftDirectCommonModelComplement m
  let P := ZMod m × EuclideanFourBallCollarDomain
  let c₁ : P → CompactNeckLeftCut m :=
    coordinateExteriorPlanarNeckLeftDirectCommonModelSourceBoundaryCollar m
  let U := coordinateExteriorPlanarNeckLeftDirectCommonModelCappingCutOffSeamOpens m
  let Uall : Opens U := ⊤
  let c₂ : Uall → CompactNeckLeftCut m := fun q ↦ q.1.1
  have hc₁ : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ c₁ :=
    isLocalDiffeomorph_coordinateExteriorPlanarNeckLeftDirectCommonModelSourceBoundaryCollar m
  have hc₂ : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ c₂ := by
    let h₀ := isLocalDiffeomorph_opensSubtypeVal coordinateUnlinkExteriorModel Uall
    let h₁ := isLocalDiffeomorph_opensSubtypeVal coordinateUnlinkExteriorModel U
    intro q
    exact (h₀ q).comp coordinateUnlinkExteriorModel
      (CompactNeckLeftCut m) (h₁ q.1)
  let targetCollar := collaredCutSideHalfCollarMap
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCollarAmbient m)
    (range_leftComplementCollarAmbient_subset m)
  have hHc₁ : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      ((compactNeckLeftCutHomeomorphDirectCommonModelComplement m) ∘ c₁) := by
    have hfun : (compactNeckLeftCutHomeomorphDirectCommonModelComplement m) ∘ c₁ =
        targetCollar := by
      funext p
      apply Subtype.ext
      rfl
    rw [hfun]
    exact
      isLocalDiffeomorph_leftComplementBoundaryCollar m
  let V := collaredCutSideOffBoundaryOpens
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
    (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m)
    (isOpen_coordinateExteriorPlanarNeckLeftDirectCommonModel_offBoundary m)
  let F : U → ZMod m × CoordinateExteriorRightTubeClosed :=
    (leftCappingToDirectCommonModel m).toHomeomorph ∘
      topologicalPushoutInlOffSeamMap'
        (leftCutAttaching m) (roundedCapAttaching m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
  have hF : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ F :=
    isLocalDiffeomorph_coordinateExteriorPlanarNeckLeftDirectCommonModelCappingCutOffSeamToCommon m
  have hmem (q : Uall) : F q.1 ∈ V := by
    change F q.1 ∈ collaredCutSideOffBoundary
      (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
        (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m)
    rw [coordinateExteriorPlanarNeckLeftDirectCommonModel_offBoundary_eq_compl_closedImage m]
    intro hclosed
    rcases hclosed with ⟨y, hy⟩
    have heq :
        topologicalPushoutInl (leftCutAttaching m) (roundedCapAttaching m) q.1.1 =
          topologicalPushoutInr (leftCutAttaching m) (roundedCapAttaching m) y := by
      apply (leftCappingToDirectCommonModel m).injective
      exact hy.symm
    obtain ⟨a, hfa, _⟩ :=
      (topologicalPushoutInl_eq_inr_iff
        (leftCutAttaching m) (roundedCapAttaching m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m).injective
        q.1.1 y).mp heq
    exact q.1.2 ⟨a, hfa⟩
  let r : Uall → V := restrictToOpens F Uall V hmem
  have hr : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ r :=
    isLocalDiffeomorph_restrictToOpens coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel F Uall V hmem hF
  let d : V → CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement m :=
    collaredCutSideOffBoundaryOpensMap
      (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)
      (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapClosedImage m)
      (isOpen_coordinateExteriorPlanarNeckLeftDirectCommonModel_offBoundary m)
  have hd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ d :=
    isLocalDiffeomorph_coordinateExteriorPlanarNeckLeftDirectCommonModelComplementOffBoundaryMap m
  have hdr : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (d ∘ r) := by
    intro q
    exact (hr q).comp coordinateUnlinkExteriorModel
      (CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement m) (hd (r q))
  have hHc₂ : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      ((compactNeckLeftCutHomeomorphDirectCommonModelComplement m) ∘ c₂) := by
    have hfun : (compactNeckLeftCutHomeomorphDirectCommonModelComplement m) ∘ c₂ = d ∘ r := by
      funext q
      apply Subtype.ext
      change leftCappingToDirectCommonModel m
          (topologicalPushoutInl (leftCutAttaching m) (roundedCapAttaching m) q.1.1) =
        (leftCappingToDirectCommonModel m).toHomeomorph
          (topologicalPushoutInl (leftCutAttaching m) (roundedCapAttaching m) q.1.1)
      rfl
    rw [hfun]
    exact hdr
  have hcover : ∀ x : CompactNeckLeftCut m,
      (∃ p : P, c₁ p = x) ∨ (∃ q : Uall, c₂ q = x) ∨
        (∃ p : P, c₁ p = x) := by
    intro x
    by_cases hx : x ∈ range (leftCutAttaching m)
    · rcases compactNeckLeftCut_collarCoverage m x with hoff | hcollar
      · exfalso
        apply hoff.2
        have hxSeam := hx
        rw [range_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap] at hxSeam
        exact hxSeam
      · left
        obtain ⟨p, hp⟩ := hcollar
        refine ⟨p, ?_⟩
        exact Subtype.ext hp
    · right
      left
      let q : U := ⟨x, hx⟩
      refine ⟨⟨q, Set.mem_univ q⟩, rfl⟩
  exact isLocalDiffeomorph_of_three_localDiffeomorph_parametrizations
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    (compactNeckLeftCutHomeomorphDirectCommonModelComplement m)
    c₁ c₂ c₁ hc₁ hc₂ hc₁ hHc₁ hHc₂ hHc₁ hcover

/-- The compact left cut is diffeomorphic to the literal common-target complement
for the direct complement atlas. -/
def compactNeckLeftCutDiffeomorphDirectCommonModelComplement :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
    CompactNeckLeftCut m ≃ₘ^∞⟮coordinateUnlinkExteriorModel,
      coordinateUnlinkExteriorModel⟯ CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement
        m := by
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := compactNeckLeftCutChartedSpace m
  let _ := coordinateExteriorRightTubeClosedChartedSpace
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
  exact diffeomorphOfHomeomorphIsLocalDiffeomorph
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    (compactNeckLeftCutHomeomorphDirectCommonModelComplement m)
    (isLocalDiffeomorph_compactNeckLeftCutHomeomorphDirectCommonModelComplement m)

@[simp] theorem compactNeckLeftCutDiffeomorphDirectCommonModelComplement_apply
    (x : CompactNeckLeftCut m) :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
    compactNeckLeftCutDiffeomorphDirectCommonModelComplement m x =
      compactNeckLeftCutHomeomorphDirectCommonModelComplement m x := by
  rfl

/-! ## Opaque public construction spine -/

@[expose] public section

/-- The semantic data retained from the direct complement construction.

The closed cap images, collar embeddings, overlap proofs, atlas compatibility, and
parametrized-cover recognition above remain module-private.  This record retains exactly the
point-set and smooth objects needed by later pushout constructions. -/
structure Construction (m : ℕ) [NeZero m] where
  /-- The custom-atlas closed right-tube family is smoothly the natural one-handle family. -/
  rightTubeClosedOneHandleFamilyDiffeomorph :
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    (ZMod m × CoordinateExteriorRightTubeClosed)
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, oneHandlePieceModel⟯
        (ZMod m × OneHandlePiece)
  /-- Exact forward law for the closed right-tube family comparison. -/
  rightTubeClosedOneHandleFamilyDiffeomorph_apply
      (z : ZMod m × CoordinateExteriorRightTubeClosed) :
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    rightTubeClosedOneHandleFamilyDiffeomorph z =
      (z.1, coordinateExteriorRightTubeOneHandleHomeomorph z.2)
  /-- The left capping is smoothly the custom-atlas closed right-tube family. -/
  leftCappingRightTubeClosedFamilyDiffeomorph :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, coordinateUnlinkExteriorModel⟯
        (ZMod m × CoordinateExteriorRightTubeClosed)
  /-- Exact forward law for the left-capping common-target comparison. -/
  leftCappingRightTubeClosedFamilyDiffeomorph_apply
      (z : CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m) :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    leftCappingRightTubeClosedFamilyDiffeomorph z =
      (CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
        m).rightTubeHomeomorph z
  /-- The actual right rounded-cap interior in common right-tube coordinates. -/
  rightRoundedCapInterior : Set (CoordinateExteriorRightTubePowerPullback m)
  /-- The retained right interior is the actual image of the off-seam rounded cap. -/
  rightRoundedCapInterior_eq_image :
    rightRoundedCapInterior =
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m ''
        (topologicalPushoutInr
            (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
            (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) ''
          coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m)
  /-- Point-set cancellation of the right rounded cap. -/
  rightCutHomeomorph :
    CompactNeckRightCut m ≃ₜ CollaredCutSide rightRoundedCapInteriorᶜ
  /-- Exact ambient formula for right point-set cancellation. -/
  rightCutHomeomorph_coe (x : CompactNeckRightCut m) :
    (rightCutHomeomorph x : CoordinateExteriorRightTubePowerPullback m) =
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x)
  /-- The direct generated atlas on the literal right complement. -/
  rightComplementChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CollaredCutSide rightRoundedCapInteriorᶜ)
  /-- The direct right complement atlas is a smooth manifold atlas. -/
  rightComplementIsManifold :
    letI := rightComplementChartedSpace
    IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide rightRoundedCapInteriorᶜ)
  /-- Smooth cancellation of the right rounded cap. -/
  rightCutDiffeomorph :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI := rightComplementChartedSpace
    CompactNeckRightCut m ≃ₘ^∞⟮coordinateUnlinkExteriorModel,
      coordinateUnlinkExteriorModel⟯ CollaredCutSide rightRoundedCapInteriorᶜ
  /-- Smooth and point-set right cancellation have the same forward map. -/
  rightCutDiffeomorph_apply (x : CompactNeckRightCut m) :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI := rightComplementChartedSpace
    rightCutDiffeomorph x = rightCutHomeomorph x
  /-- Forgetting right smooth cancellation recovers point-set cancellation exactly. -/
  rightCutDiffeomorph_toHomeomorph :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI := rightComplementChartedSpace
    rightCutDiffeomorph.toHomeomorph = rightCutHomeomorph
  /-- The actual left rounded-cap interior in common closed-right-tube coordinates. -/
  leftRoundedCapInterior : Set (ZMod m × CoordinateExteriorRightTubeClosed)
  /-- The retained left interior is the actual image of the off-seam rounded cap. -/
  leftRoundedCapInterior_eq_image :
    leftRoundedCapInterior =
      (CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
        m).rightTubeHomeomorph ''
        (topologicalPushoutInr
            (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
            (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) ''
          coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m)
  /-- Point-set cancellation of the left rounded cap. -/
  leftCutHomeomorph :
    CompactNeckLeftCut m ≃ₜ CollaredCutSide leftRoundedCapInteriorᶜ
  /-- Exact ambient formula for left point-set cancellation. -/
  leftCutHomeomorph_coe (x : CompactNeckLeftCut m) :
    (leftCutHomeomorph x : ZMod m × CoordinateExteriorRightTubeClosed) =
      (CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
        m).rightTubeHomeomorph
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
            (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x)
  /-- The direct generated atlas on the literal left complement. -/
  leftComplementChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CollaredCutSide leftRoundedCapInteriorᶜ)
  /-- The direct left complement atlas is a smooth manifold atlas. -/
  leftComplementIsManifold :
    letI := leftComplementChartedSpace
    IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide leftRoundedCapInteriorᶜ)
  /-- Smooth cancellation of the left rounded cap. -/
  leftCutDiffeomorph :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := leftComplementChartedSpace
    CompactNeckLeftCut m ≃ₘ^∞⟮coordinateUnlinkExteriorModel,
      coordinateUnlinkExteriorModel⟯ CollaredCutSide leftRoundedCapInteriorᶜ
  /-- Smooth and point-set left cancellation have the same forward map. -/
  leftCutDiffeomorph_apply (x : CompactNeckLeftCut m) :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := leftComplementChartedSpace
    leftCutDiffeomorph x = leftCutHomeomorph x
  /-- Forgetting left smooth cancellation recovers point-set cancellation exactly. -/
  leftCutDiffeomorph_toHomeomorph :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := leftComplementChartedSpace
    leftCutDiffeomorph.toHomeomorph = leftCutHomeomorph

/-- The opaque semantic package produced by the direct complement construction. -/
noncomputable def construction (m : ℕ) [NeZero m] : Construction m :=
  Classical.choice (by
    exact ⟨{
      rightTubeClosedOneHandleFamilyDiffeomorph :=
        coordinateExteriorRightTubeClosedOneHandleFamilyDiffeomorph m
      rightTubeClosedOneHandleFamilyDiffeomorph_apply :=
        coordinateExteriorRightTubeClosedOneHandleFamilyDiffeomorph_apply m
      leftCappingRightTubeClosedFamilyDiffeomorph :=
        coordinateExteriorPlanarNeckLeftSmoothCappingRightTubeClosedFamilyDiffeomorph m
      leftCappingRightTubeClosedFamilyDiffeomorph_apply :=
        coordinateExteriorPlanarNeckLeftSmoothCappingRightTubeClosedFamilyDiffeomorph_apply m
      rightRoundedCapInterior :=
        coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapInterior m
      rightRoundedCapInterior_eq_image := by
        let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
        let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
        rw [coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapInterior]
        rw [coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph_toHomeomorph]
      rightCutHomeomorph :=
        compactNeckRightCutHomeomorphDirectCommonModelComplement m
      rightCutHomeomorph_coe := by
        intro x
        change coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph m
            (topologicalPushoutInl
              (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
              (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x) = _
        exact coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph_apply m _
      rightComplementChartedSpace :=
        coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
      rightComplementIsManifold :=
        isManifold_coordinateExteriorPlanarNeckRightDirectCommonModelComplement m
      rightCutDiffeomorph :=
        compactNeckRightCutDiffeomorphDirectCommonModelComplement m
      rightCutDiffeomorph_apply :=
        compactNeckRightCutDiffeomorphDirectCommonModelComplement_apply m
      rightCutDiffeomorph_toHomeomorph := rfl
      leftRoundedCapInterior :=
        coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapInterior m
      leftRoundedCapInterior_eq_image := by
        let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
        let _ := coordinateExteriorRightTubeClosedChartedSpace
        let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
          (ZMod m) CoordinateExteriorRightTubeClosed
        rw [coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapInterior]
        apply congrArg (fun e :
          CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m ≃ₜ
            ZMod m × CoordinateExteriorRightTubeClosed ↦ e '' _)
        apply Homeomorph.ext
        intro z
        exact
          coordinateExteriorPlanarNeckLeftSmoothCappingRightTubeClosedFamilyDiffeomorph_apply
            m z
      leftCutHomeomorph :=
        compactNeckLeftCutHomeomorphDirectCommonModelComplement m
      leftCutHomeomorph_coe := by
        intro x
        change coordinateExteriorPlanarNeckLeftSmoothCappingRightTubeClosedFamilyDiffeomorph m
            (topologicalPushoutInl
              (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
              (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x) = _
        exact
          coordinateExteriorPlanarNeckLeftSmoothCappingRightTubeClosedFamilyDiffeomorph_apply
            m _
      leftComplementChartedSpace :=
        coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
      leftComplementIsManifold :=
        isManifold_coordinateExteriorPlanarNeckLeftDirectCommonModelComplement m
      leftCutDiffeomorph :=
        compactNeckLeftCutDiffeomorphDirectCommonModelComplement m
      leftCutDiffeomorph_apply :=
        compactNeckLeftCutDiffeomorphDirectCommonModelComplement_apply m
      leftCutDiffeomorph_toHomeomorph := rfl }⟩)

end

end CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal


/-! ## Public common-target comparisons -/

@[expose] public section

/-- The custom-atlas closed right-tube family is diffeomorphic to the labelled natural
one-handle family. -/
noncomputable def coordinateExteriorRightTubeClosedOneHandleFamilyDiffeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    (ZMod m × CoordinateExteriorRightTubeClosed)
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, oneHandlePieceModel⟯
        (ZMod m × OneHandlePiece) :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).rightTubeClosedOneHandleFamilyDiffeomorph

/-- Exact forward law for the closed right-tube family comparison. -/
@[simp] theorem coordinateExteriorRightTubeClosedOneHandleFamilyDiffeomorph_apply
    (m : ℕ) [NeZero m]
    (z : ZMod m × CoordinateExteriorRightTubeClosed) :
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    coordinateExteriorRightTubeClosedOneHandleFamilyDiffeomorph m z =
      (z.1, coordinateExteriorRightTubeOneHandleHomeomorph z.2) :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).rightTubeClosedOneHandleFamilyDiffeomorph_apply z

/-- The direct left capping is diffeomorphic to the custom-atlas closed right-tube family. -/
noncomputable def
    coordinateExteriorPlanarNeckLeftSmoothCappingRightTubeClosedFamilyDiffeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, coordinateUnlinkExteriorModel⟯
        (ZMod m × CoordinateExteriorRightTubeClosed) :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).leftCappingRightTubeClosedFamilyDiffeomorph

/-- Exact forward law for the left-capping common-target comparison. -/
@[simp] theorem
    coordinateExteriorPlanarNeckLeftSmoothCappingRightTubeClosedFamilyDiffeomorph_apply
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m) :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    coordinateExteriorPlanarNeckLeftSmoothCappingRightTubeClosedFamilyDiffeomorph m z =
      (CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
        m).rightTubeHomeomorph z :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).leftCappingRightTubeClosedFamilyDiffeomorph_apply z

/-! ## Literal right common-model complement -/

/-- The actual rounded-cap interior in the standard right-tube power-pullback target. -/
def coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapInterior
    (m : ℕ) [NeZero m] : Set (CoordinateExteriorRightTubePowerPullback m) :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).rightRoundedCapInterior

/-- The retained right interior is exactly the actual image of the off-seam rounded cap. -/
theorem coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapInterior_eq_image
    (m : ℕ) [NeZero m] :
    coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapInterior m =
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m ''
        (topologicalPushoutInr
            (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
            (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) ''
          coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m) :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).rightRoundedCapInterior_eq_image

/-- Carrier of the literal right common-model rounded-cap complement. -/
def coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier
    (m : ℕ) [NeZero m] : Set (CoordinateExteriorRightTubePowerPullback m) :=
  (coordinateExteriorPlanarNeckRightDirectCommonModelRoundedCapInterior m)ᶜ

/-- The literal right common-model rounded-cap complement. -/
abbrev CoordinateExteriorPlanarNeckRightDirectCommonModelComplement
    (m : ℕ) [NeZero m] :=
  CollaredCutSide
    (coordinateExteriorPlanarNeckRightDirectCommonModelComplementCarrier m)

/-- Point-set cancellation identifies the compact right cut with its literal common-model
complement. -/
noncomputable def compactNeckRightCutHomeomorphDirectCommonModelComplement
    (m : ℕ) [NeZero m] :
    CompactNeckRightCut m ≃ₜ
      CoordinateExteriorPlanarNeckRightDirectCommonModelComplement m :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).rightCutHomeomorph

/-- Exact ambient formula for right point-set cancellation. -/
@[simp] theorem compactNeckRightCutHomeomorphDirectCommonModelComplement_coe
    (m : ℕ) [NeZero m] (x : CompactNeckRightCut m) :
    (compactNeckRightCutHomeomorphDirectCommonModelComplement m x :
        CoordinateExteriorRightTubePowerPullback m) =
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x) :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).rightCutHomeomorph_coe x

/-- The direct ambient/collar atlas on the literal right common-model complement. -/
@[instance_reducible]
noncomputable def coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace
    (m : ℕ) [NeZero m] :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateExteriorPlanarNeckRightDirectCommonModelComplement m) :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).rightComplementChartedSpace

/-- The literal right common-model complement is a manifold for its direct generated atlas. -/
theorem isManifold_coordinateExteriorPlanarNeckRightDirectCommonModelComplement
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorPlanarNeckRightDirectCommonModelComplement m) :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).rightComplementIsManifold

/-- Smooth cancellation identifies the compact right cut with its literal common-model
complement. -/
noncomputable def compactNeckRightCutDiffeomorphDirectCommonModelComplement
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
    CompactNeckRightCut m ≃ₘ^∞⟮coordinateUnlinkExteriorModel,
      coordinateUnlinkExteriorModel⟯
        CoordinateExteriorPlanarNeckRightDirectCommonModelComplement m :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).rightCutDiffeomorph

/-- Smooth and point-set right cancellation have the same forward map. -/
@[simp] theorem compactNeckRightCutDiffeomorphDirectCommonModelComplement_apply
    (m : ℕ) [NeZero m] (x : CompactNeckRightCut m) :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
    compactNeckRightCutDiffeomorphDirectCommonModelComplement m x =
      compactNeckRightCutHomeomorphDirectCommonModelComplement m x :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).rightCutDiffeomorph_apply x

/-- Forgetting right smooth cancellation recovers point-set cancellation exactly. -/
@[simp] theorem compactNeckRightCutDiffeomorphDirectCommonModelComplement_toHomeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
    (compactNeckRightCutDiffeomorphDirectCommonModelComplement m).toHomeomorph =
      compactNeckRightCutHomeomorphDirectCommonModelComplement m :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).rightCutDiffeomorph_toHomeomorph

/-- Exact ambient formula for right smooth cancellation on the transported half collar. -/
theorem
    compactNeckRightCutDiffeomorphDirectCommonModelComplement_boundaryCollar_coe
    (m : ℕ) [NeZero m] (p : ZMod m × EuclideanFourBallCollarDomain) :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI := coordinateExteriorPlanarNeckRightDirectCommonModelComplementChartedSpace m
    ((compactNeckRightCutDiffeomorphDirectCommonModelComplement m
        ⟨compactNeckRightBoundaryCollarMap m p,
          compactNeckRightBoundaryCollarMap_range_subset m (mem_range_self p)⟩ :
      CoordinateExteriorPlanarNeckRightDirectCommonModelComplement m) :
        CoordinateExteriorRightTubePowerPullback m) =
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
          ⟨compactNeckRightBoundaryCollarMap m p,
            compactNeckRightBoundaryCollarMap_range_subset m (mem_range_self p)⟩) := by
  rw [compactNeckRightCutDiffeomorphDirectCommonModelComplement_apply]
  exact compactNeckRightCutHomeomorphDirectCommonModelComplement_coe m _

/-! ## Literal left common-model complement -/

/-- The actual rounded-cap interior in the common closed right-tube family target. -/
def coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapInterior
    (m : ℕ) [NeZero m] :
    Set (ZMod m × CoordinateExteriorRightTubeClosed) :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).leftRoundedCapInterior

/-- The retained left interior is exactly the actual image of the off-seam rounded cap. -/
theorem coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapInterior_eq_image
    (m : ℕ) [NeZero m] :
    coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapInterior m =
      (CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
        m).rightTubeHomeomorph ''
        (topologicalPushoutInr
            (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
            (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) ''
          coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m) :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).leftRoundedCapInterior_eq_image

/-- Carrier of the literal left common-model rounded-cap complement. -/
def coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier
    (m : ℕ) [NeZero m] :
    Set (ZMod m × CoordinateExteriorRightTubeClosed) :=
  (coordinateExteriorPlanarNeckLeftDirectCommonModelRoundedCapInterior m)ᶜ

/-- The literal left common-model rounded-cap complement. -/
abbrev CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement
    (m : ℕ) [NeZero m] :=
  CollaredCutSide
    (coordinateExteriorPlanarNeckLeftDirectCommonModelComplementCarrier m)

/-- Point-set cancellation identifies the compact left cut with its literal common-model
complement. -/
noncomputable def compactNeckLeftCutHomeomorphDirectCommonModelComplement
    (m : ℕ) [NeZero m] :
    CompactNeckLeftCut m ≃ₜ
      CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement m :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).leftCutHomeomorph

/-- Exact ambient formula for left point-set cancellation. -/
@[simp] theorem compactNeckLeftCutHomeomorphDirectCommonModelComplement_coe
    (m : ℕ) [NeZero m] (x : CompactNeckLeftCut m) :
    (compactNeckLeftCutHomeomorphDirectCommonModelComplement m x :
        ZMod m × CoordinateExteriorRightTubeClosed) =
      (CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
        m).rightTubeHomeomorph
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
            (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x) :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).leftCutHomeomorph_coe x

/-- The direct ambient/collar atlas on the literal left common-model complement. -/
@[instance_reducible]
noncomputable def coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace
    (m : ℕ) [NeZero m] :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement m) :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).leftComplementChartedSpace

/-- The literal left common-model complement is a manifold for its direct generated atlas. -/
theorem isManifold_coordinateExteriorPlanarNeckLeftDirectCommonModelComplement
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement m) :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).leftComplementIsManifold

/-- Smooth cancellation identifies the compact left cut with its literal common-model
complement. -/
noncomputable def compactNeckLeftCutDiffeomorphDirectCommonModelComplement
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
    CompactNeckLeftCut m ≃ₘ^∞⟮coordinateUnlinkExteriorModel,
      coordinateUnlinkExteriorModel⟯
        CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement m :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).leftCutDiffeomorph

/-- Smooth and point-set left cancellation have the same forward map. -/
@[simp] theorem compactNeckLeftCutDiffeomorphDirectCommonModelComplement_apply
    (m : ℕ) [NeZero m] (x : CompactNeckLeftCut m) :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
    compactNeckLeftCutDiffeomorphDirectCommonModelComplement m x =
      compactNeckLeftCutHomeomorphDirectCommonModelComplement m x :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).leftCutDiffeomorph_apply x

/-- Forgetting left smooth cancellation recovers point-set cancellation exactly. -/
@[simp] theorem compactNeckLeftCutDiffeomorphDirectCommonModelComplement_toHomeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
    (compactNeckLeftCutDiffeomorphDirectCommonModelComplement m).toHomeomorph =
      compactNeckLeftCutHomeomorphDirectCommonModelComplement m :=
  (CoordinateExteriorPlanarNeckDirectCommonModelComplementsInternal.construction
    m).leftCutDiffeomorph_toHomeomorph

/-- Exact ambient formula for left smooth cancellation on the transported half collar. -/
theorem
    compactNeckLeftCutDiffeomorphDirectCommonModelComplement_boundaryCollar_coe
    (m : ℕ) [NeZero m] (p : ZMod m × EuclideanFourBallCollarDomain) :
    letI := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    letI := coordinateExteriorRightTubeClosedChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := coordinateExteriorPlanarNeckLeftDirectCommonModelComplementChartedSpace m
    ((compactNeckLeftCutDiffeomorphDirectCommonModelComplement m
        ⟨compactNeckLeftBoundaryCollarMap m p,
          compactNeckLeftBoundaryCollarMap_range_subset m (mem_range_self p)⟩ :
      CoordinateExteriorPlanarNeckLeftDirectCommonModelComplement m) :
        ZMod m × CoordinateExteriorRightTubeClosed) =
      (CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
        m).rightTubeHomeomorph
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
            (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
            ⟨compactNeckLeftBoundaryCollarMap m p,
              compactNeckLeftBoundaryCollarMap_range_subset m (mem_range_self p)⟩) := by
  rw [compactNeckLeftCutDiffeomorphDirectCommonModelComplement_apply]
  exact compactNeckLeftCutHomeomorphDirectCommonModelComplement_coe m _

end

end SplittingSpheres
