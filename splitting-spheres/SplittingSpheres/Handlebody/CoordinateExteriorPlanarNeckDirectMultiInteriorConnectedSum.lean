/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCompactCutRegluing
public import
  SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph
public import
  SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph
import SplittingSpheres.Foundations.TopologicalPushoutCongr
import SplittingSpheres.Foundations.TopologicalPushoutEmbedding

/-!
# Direct simultaneous interior connected sum for the planar-neck exterior

This file deletes the actual rounded direct-cap interiors from a labelled family of natural
one-handles and from one central natural one-handle, then reglues the resulting literal
complements along their common labelled sphere family. It identifies the compact coordinate
exterior with that point-set pushout by an explicit homeomorphism whose laws on both pieces are
literal.

The cap family is ZMod m times EuclideanFourBall, so the construction records m disjoint labelled
balls on each side. No smooth structure is placed on the target complements here, and no atlas is
transported through the point-set homeomorphism.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace SplittingSpheres

variable (m : ℕ) [NeZero m]

/-! ## Literal cancellation of the two direct cap families -/

/-- The off-attaching-boundary part of the direct labelled four-ball family. -/
def coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior :
    Set (ZMod m × EuclideanFourBall) :=
  (range (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m))ᶜ

omit [NeZero m] in
/-- In the direct common-model atlas, the off-attaching part is exactly the model interior. -/
theorem coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior_eq_modelInterior :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m =
      coordinateUnlinkExteriorModel.interior (ZMod m × EuclideanFourBall) := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  rw [coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior,
    range_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap]
  exact coordinateUnlinkExteriorModel.compl_boundary

/-- The labelled direct cap interiors transported into the labelled one-handle target of the
left capping. -/
def coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorOneHandles :
    Set (ZMod m × OneHandlePiece) := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := discreteProductChartedSpace OneHandleModelSpace (ZMod m) OneHandlePiece
  exact (coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph m).toHomeomorph ''
    (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) ''
      coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m)

/-- The labelled direct cap interiors transported into the one-handle target of the right
capping. -/
def coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorOneHandle :
    Set OneHandlePiece := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  exact (coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph m).toHomeomorph ''
    (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) ''
      coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m)

/-- The actual direct cap interiors remain open in the labelled natural one-handle target. -/
theorem isOpen_coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorOneHandles :
    IsOpen (coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorOneHandles m) := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := discreteProductChartedSpace OneHandleModelSpace (ZMod m) OneHandlePiece
  exact (coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph
    m).toHomeomorph.isOpenMap _
      (by
        rw [coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior]
        change IsOpen (topologicalPushoutInrOffSeam
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m))
        exact isOpen_topologicalPushoutInrOffSeam
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
          (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap
            m))

/-- The actual direct cap interiors remain open in the central natural one-handle target. -/
theorem isOpen_coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorOneHandle :
    IsOpen (coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorOneHandle m) := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  exact (coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph
    m).toHomeomorph.isOpenMap _
      (by
        rw [coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior]
        change IsOpen (topologicalPushoutInrOffSeam
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m))
        exact isOpen_topologicalPushoutInrOffSeam
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
          (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap
            m))

/-- The actual closed direct cap-family map into the labelled one-handle target. -/
def coordinateUnlinkExteriorPlanarNeckLeftDirectCapMap :
    C(ZMod m × EuclideanFourBall, ZMod m × OneHandlePiece) := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := discreteProductChartedSpace OneHandleModelSpace (ZMod m) OneHandlePiece
  exact
    { toFun := fun y ↦ coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) y)
      continuous_toFun :=
        (coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph
          m).toHomeomorph.continuous.comp
            (topologicalPushoutInr
              (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
              (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)).continuous }

/-- The actual closed direct cap-family map into the central one-handle target. -/
def coordinateUnlinkExteriorPlanarNeckRightDirectCapMap :
    C(ZMod m × EuclideanFourBall, OneHandlePiece) := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  exact
    { toFun := fun y ↦ coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) y)
      continuous_toFun :=
        (coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph
          m).toHomeomorph.continuous.comp
            (topologicalPushoutInr
              (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
              (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)).continuous }

/-- The target left cap-interior set is exactly the image of the actual direct cap map. -/
theorem coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorOneHandles_eq_image :
    coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorOneHandles m =
      coordinateUnlinkExteriorPlanarNeckLeftDirectCapMap m ''
        coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := discreteProductChartedSpace OneHandleModelSpace (ZMod m) OneHandlePiece
  rw [coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorOneHandles,
    image_image]
  rfl

/-- The target right cap-interior set is exactly the image of the actual direct cap map. -/
theorem coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorOneHandle_eq_image :
    coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorOneHandle m =
      coordinateUnlinkExteriorPlanarNeckRightDirectCapMap m ''
        coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  rw [coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorOneHandle,
    image_image]
  rfl

/-- Each labelled direct cap is closed embedded in the labelled one-handle target. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftDirectCapMap :
    IsClosedEmbedding (coordinateUnlinkExteriorPlanarNeckLeftDirectCapMap m) := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := discreteProductChartedSpace OneHandleModelSpace (ZMod m) OneHandlePiece
  exact (coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph
    m).toHomeomorph.isClosedEmbedding.comp <|
      isClosedEmbedding_topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)

/-- Each labelled direct cap is closed embedded in the central one-handle target. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightDirectCapMap :
    IsClosedEmbedding (coordinateUnlinkExteriorPlanarNeckRightDirectCapMap m) := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  exact (coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph
    m).toHomeomorph.isClosedEmbedding.comp <|
      isClosedEmbedding_topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)

/-- The strict interior belonging to one label in the direct cap family. -/
def coordinateUnlinkExteriorPlanarNeckDirectCapInteriorAt (a : ZMod m) :
    Set (ZMod m × EuclideanFourBall) :=
  {p | p.1 = a} ∩ coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m

omit [NeZero m] in
/-- The direct cap-family interior is the union of its labelled ball interiors. -/
theorem coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior_eq_iUnion :
    coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m =
      ⋃ a : ZMod m, coordinateUnlinkExteriorPlanarNeckDirectCapInteriorAt m a := by
  ext p
  simp [coordinateUnlinkExteriorPlanarNeckDirectCapInteriorAt]

/-- Distinct labels give disjoint direct cap interiors in the labelled target. -/
theorem disjoint_coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorAt
    {a b : ZMod m} (hab : a ≠ b) :
    Disjoint
      (coordinateUnlinkExteriorPlanarNeckLeftDirectCapMap m ''
        coordinateUnlinkExteriorPlanarNeckDirectCapInteriorAt m a)
      (coordinateUnlinkExteriorPlanarNeckLeftDirectCapMap m ''
        coordinateUnlinkExteriorPlanarNeckDirectCapInteriorAt m b) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have hsource :=
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftDirectCapMap m).injective hxy
  apply hab
  have hxa : x.1 = a := hx.1
  have hyb : y.1 = b := hy.1
  exact hxa.symm.trans ((congrArg Prod.fst hsource).symm.trans hyb)

/-- Distinct labels give disjoint direct cap interiors in the central target. -/
theorem disjoint_coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorAt
    {a b : ZMod m} (hab : a ≠ b) :
    Disjoint
      (coordinateUnlinkExteriorPlanarNeckRightDirectCapMap m ''
        coordinateUnlinkExteriorPlanarNeckDirectCapInteriorAt m a)
      (coordinateUnlinkExteriorPlanarNeckRightDirectCapMap m ''
        coordinateUnlinkExteriorPlanarNeckDirectCapInteriorAt m b) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have hsource :=
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightDirectCapMap m).injective hxy
  apply hab
  have hxa : x.1 = a := hx.1
  have hyb : y.1 = b := hy.1
  exact hxa.symm.trans ((congrArg Prod.fst hsource).symm.trans hyb)

/-- The labelled target cap-interior set is exactly the union of the individual ball
interiors. -/
theorem coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorOneHandles_eq_iUnion :
    coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorOneHandles m =
      ⋃ a : ZMod m,
        coordinateUnlinkExteriorPlanarNeckLeftDirectCapMap m ''
          coordinateUnlinkExteriorPlanarNeckDirectCapInteriorAt m a := by
  rw [coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorOneHandles_eq_image,
    coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior_eq_iUnion,
    image_iUnion]

/-- The central target cap-interior set is exactly the union of the individual labelled
ball interiors. -/
theorem coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorOneHandle_eq_iUnion :
    coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorOneHandle m =
      ⋃ a : ZMod m,
        coordinateUnlinkExteriorPlanarNeckRightDirectCapMap m ''
          coordinateUnlinkExteriorPlanarNeckDirectCapInteriorAt m a := by
  rw [coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorOneHandle_eq_image,
    coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior_eq_iUnion,
    image_iUnion]

/-- The left cut as the literal complement of its labelled direct cap interiors in the
labelled one-handle target. -/
def compactNeckLeftCutHomeomorphComplementOneHandles :
    CompactNeckLeftCut m ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorOneHandles m)ᶜ := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := discreteProductChartedSpace OneHandleModelSpace (ZMod m) OneHandlePiece
  let A : Set (CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m) :=
    topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) ''
      coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m
  exact
    ((isEmbedding_topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
      ).toHomeomorph.trans
        (Homeomorph.setCongr (by
          dsimp only [A, coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior]
          exact range_topologicalPushoutInl_eq_compl_image_inr_compl_range _ _
            (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap
              m).injective))).trans <|
    ((coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph m).toHomeomorph.image
      Aᶜ).trans <|
        Homeomorph.setCongr (by
          simpa [coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorOneHandles, A] using
            (coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph
              m).toHomeomorph.toEquiv.image_compl
                A)

/-- The right cut as the literal complement of its labelled direct cap interiors in the
central one-handle target. -/
def compactNeckRightCutHomeomorphComplementOneHandle :
    CompactNeckRightCut m ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorOneHandle m)ᶜ := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  let A : Set (CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping m) :=
    topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) ''
      coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior m
  exact
    ((isEmbedding_topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
      ).toHomeomorph.trans
        (Homeomorph.setCongr (by
          dsimp only [A, coordinateUnlinkExteriorPlanarNeckDirectCapFamilyInterior]
          exact range_topologicalPushoutInl_eq_compl_image_inr_compl_range _ _
            (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap
              m).injective))).trans <|
    ((coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph m).toHomeomorph.image
      Aᶜ).trans <|
        Homeomorph.setCongr (by
          simpa [coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorOneHandle, A] using
            (coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph
              m).toHomeomorph.toEquiv.image_compl
                A)

@[simp] theorem compactNeckLeftCutHomeomorphComplementOneHandles_coe
    (x : CompactNeckLeftCut m) :
    (compactNeckLeftCutHomeomorphComplementOneHandles m x :
        ZMod m × OneHandlePiece) = by
      let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
      let _ := discreteProductChartedSpace OneHandleModelSpace (ZMod m) OneHandlePiece
      exact coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x) := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := discreteProductChartedSpace OneHandleModelSpace (ZMod m) OneHandlePiece
  rfl

@[simp] theorem compactNeckRightCutHomeomorphComplementOneHandle_coe
    (x : CompactNeckRightCut m) :
    (compactNeckRightCutHomeomorphComplementOneHandle m x : OneHandlePiece) = by
      let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
      exact coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x) := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  rfl

/-- The actual left cut map into the labelled natural one-handle target. -/
def coordinateUnlinkExteriorPlanarNeckLeftDirectCutMap :
    C(CompactNeckLeftCut m, ZMod m × OneHandlePiece) where
  toFun x := compactNeckLeftCutHomeomorphComplementOneHandles m x
  continuous_toFun := continuous_subtype_val.comp
    (compactNeckLeftCutHomeomorphComplementOneHandles m).continuous

/-- The actual right cut map into the central natural one-handle target. -/
def coordinateUnlinkExteriorPlanarNeckRightDirectCutMap :
    C(CompactNeckRightCut m, OneHandlePiece) where
  toFun x := compactNeckRightCutHomeomorphComplementOneHandle m x
  continuous_toFun := continuous_subtype_val.comp
    (compactNeckRightCutHomeomorphComplementOneHandle m).continuous

/-- The actual left cut has range exactly the complement of the labelled direct cap
interiors. -/
theorem range_coordinateUnlinkExteriorPlanarNeckLeftDirectCutMap :
    range (coordinateUnlinkExteriorPlanarNeckLeftDirectCutMap m) =
      (coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorOneHandles m)ᶜ := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact (compactNeckLeftCutHomeomorphComplementOneHandles m x).property
  · intro hz
    let z' : ↑(coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorOneHandles m)ᶜ :=
      ⟨z, hz⟩
    obtain ⟨x, hx⟩ :=
      (compactNeckLeftCutHomeomorphComplementOneHandles m).surjective z'
    refine ⟨x, ?_⟩
    simpa [coordinateUnlinkExteriorPlanarNeckLeftDirectCutMap] using
      congrArg Subtype.val hx

/-- The actual right cut has range exactly the complement of the labelled direct cap
interiors. -/
theorem range_coordinateUnlinkExteriorPlanarNeckRightDirectCutMap :
    range (coordinateUnlinkExteriorPlanarNeckRightDirectCutMap m) =
      (coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorOneHandle m)ᶜ := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact (compactNeckRightCutHomeomorphComplementOneHandle m x).property
  · intro hz
    let z' : ↑(coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorOneHandle m)ᶜ :=
      ⟨z, hz⟩
    obtain ⟨x, hx⟩ :=
      (compactNeckRightCutHomeomorphComplementOneHandle m).surjective z'
    refine ⟨x, ?_⟩
    simpa [coordinateUnlinkExteriorPlanarNeckRightDirectCutMap] using
      congrArg Subtype.val hx

/-- The actual left cut is closed embedded in the labelled one-handle target. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftDirectCutMap :
    IsClosedEmbedding (coordinateUnlinkExteriorPlanarNeckLeftDirectCutMap m) :=
  (isOpen_coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorOneHandles
      m).isClosed_compl.isClosedEmbedding_subtypeVal.comp
    (compactNeckLeftCutHomeomorphComplementOneHandles m).isClosedEmbedding

/-- The actual right cut is closed embedded in the central one-handle target. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightDirectCutMap :
    IsClosedEmbedding (coordinateUnlinkExteriorPlanarNeckRightDirectCutMap m) :=
  (isOpen_coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorOneHandle
      m).isClosed_compl.isClosedEmbedding_subtypeVal.comp
    (compactNeckRightCutHomeomorphComplementOneHandle m).isClosedEmbedding

/-- The actual labelled sphere boundary of the left direct cap family. -/
def coordinateUnlinkExteriorPlanarNeckLeftDirectCapBoundaryMap :
    C(ZMod m × Sphere 3, ZMod m × OneHandlePiece) :=
  (coordinateUnlinkExteriorPlanarNeckLeftDirectCapMap m).comp
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)

/-- The actual labelled sphere boundary of the central direct cap family. -/
def coordinateUnlinkExteriorPlanarNeckRightDirectCapBoundaryMap :
    C(ZMod m × Sphere 3, OneHandlePiece) :=
  (coordinateUnlinkExteriorPlanarNeckRightDirectCapMap m).comp
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)

/-- The actual labelled sphere boundary is closed embedded in the left target. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftDirectCapBoundaryMap :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarNeckLeftDirectCapBoundaryMap m) :=
  (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftDirectCapMap m).comp
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)

/-- The actual labelled sphere boundary is closed embedded in the central target. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightDirectCapBoundaryMap :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarNeckRightDirectCapBoundaryMap m) :=
  (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightDirectCapMap m).comp
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)

/-- On the common labelled sphere, the left cut map is exactly the actual cap-boundary
map. -/
theorem coordinateUnlinkExteriorPlanarNeckLeftDirectCutMap_attaching
    (p : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarNeckLeftDirectCutMap m
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m p) =
      coordinateUnlinkExteriorPlanarNeckLeftDirectCapBoundaryMap m p := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := discreteProductChartedSpace OneHandleModelSpace (ZMod m) OneHandlePiece
  change coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph m
      (topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m p)) =
    coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph m
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m p))
  exact congrArg (coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph m)
    (topologicalPushout_condition
      (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) p)

/-- On the common labelled sphere, the right cut map is exactly the actual cap-boundary
map. -/
theorem coordinateUnlinkExteriorPlanarNeckRightDirectCutMap_attaching
    (p : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarNeckRightDirectCutMap m
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m p) =
      coordinateUnlinkExteriorPlanarNeckRightDirectCapBoundaryMap m p := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  change coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph m
      (topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m p)) =
    coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph m
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m p))
  exact congrArg (coordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph m)
    (topologicalPushout_condition
      (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) p)

/-- The punctured labelled left one-handle family. -/
abbrev CoordinateUnlinkExteriorPlanarNeckLeftDirectCappingComplement :=
  ↑(coordinateUnlinkExteriorPlanarNeckLeftDirectCapInteriorOneHandles m)ᶜ

/-- The multiply punctured central one-handle. -/
abbrev CoordinateUnlinkExteriorPlanarNeckRightDirectCappingComplement :=
  ↑(coordinateUnlinkExteriorPlanarNeckRightDirectCapInteriorOneHandle m)ᶜ

/-- Attach the common labelled sphere family to the punctured labelled left target. -/
def coordinateUnlinkExteriorPlanarNeckDirectMultiSumToLeft :
    C(ZMod m × Sphere 3,
      CoordinateUnlinkExteriorPlanarNeckLeftDirectCappingComplement m) where
  toFun p := compactNeckLeftCutHomeomorphComplementOneHandles m
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m p)
  continuous_toFun :=
    (compactNeckLeftCutHomeomorphComplementOneHandles m).continuous.comp
      (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m).continuous

/-- Attach the common labelled sphere family to the punctured central target. -/
def coordinateUnlinkExteriorPlanarNeckDirectMultiSumToRight :
    C(ZMod m × Sphere 3,
      CoordinateUnlinkExteriorPlanarNeckRightDirectCappingComplement m) where
  toFun p := compactNeckRightCutHomeomorphComplementOneHandle m
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m p)
  continuous_toFun :=
    (compactNeckRightCutHomeomorphComplementOneHandle m).continuous.comp
      (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m).continuous

/-- The actual left attaching map into the punctured target is closed embedded. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckDirectMultiSumToLeft :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarNeckDirectMultiSumToLeft m) :=
  (compactNeckLeftCutHomeomorphComplementOneHandles m).isClosedEmbedding.comp
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)

/-- The actual right attaching map into the punctured target is closed embedded. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckDirectMultiSumToRight :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarNeckDirectMultiSumToRight m) :=
  (compactNeckRightCutHomeomorphComplementOneHandle m).isClosedEmbedding.comp
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)

@[simp] theorem coordinateUnlinkExteriorPlanarNeckDirectMultiSumToLeft_coe
    (p : ZMod m × Sphere 3) :
    ((coordinateUnlinkExteriorPlanarNeckDirectMultiSumToLeft m p :
        CoordinateUnlinkExteriorPlanarNeckLeftDirectCappingComplement m) :
      ZMod m × OneHandlePiece) =
      coordinateUnlinkExteriorPlanarNeckLeftDirectCutMap m
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m p) :=
  rfl

@[simp] theorem coordinateUnlinkExteriorPlanarNeckDirectMultiSumToRight_coe
    (p : ZMod m × Sphere 3) :
    ((coordinateUnlinkExteriorPlanarNeckDirectMultiSumToRight m p :
        CoordinateUnlinkExteriorPlanarNeckRightDirectCappingComplement m) :
      OneHandlePiece) =
      coordinateUnlinkExteriorPlanarNeckRightDirectCutMap m
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m p) :=
  rfl

/-- The left gluing map is literally the actual direct cap boundary after forgetting the
complement subtype. -/
theorem coordinateUnlinkExteriorPlanarNeckDirectMultiSumToLeft_coe_eq_capBoundary
    (p : ZMod m × Sphere 3) :
    ((coordinateUnlinkExteriorPlanarNeckDirectMultiSumToLeft m p :
        CoordinateUnlinkExteriorPlanarNeckLeftDirectCappingComplement m) :
      ZMod m × OneHandlePiece) =
      coordinateUnlinkExteriorPlanarNeckLeftDirectCapBoundaryMap m p := by
  rw [coordinateUnlinkExteriorPlanarNeckDirectMultiSumToLeft_coe,
    coordinateUnlinkExteriorPlanarNeckLeftDirectCutMap_attaching]

/-- The right gluing map is literally the actual direct cap boundary after forgetting the
complement subtype. -/
theorem coordinateUnlinkExteriorPlanarNeckDirectMultiSumToRight_coe_eq_capBoundary
    (p : ZMod m × Sphere 3) :
    ((coordinateUnlinkExteriorPlanarNeckDirectMultiSumToRight m p :
        CoordinateUnlinkExteriorPlanarNeckRightDirectCappingComplement m) :
      OneHandlePiece) =
      coordinateUnlinkExteriorPlanarNeckRightDirectCapBoundaryMap m p := by
  rw [coordinateUnlinkExteriorPlanarNeckDirectMultiSumToRight_coe,
    coordinateUnlinkExteriorPlanarNeckRightDirectCutMap_attaching]

/-- The literal multi-interior-connected-sum point-set model: delete the interiors of the
labelled direct cap balls from both capping targets and reglue their labelled sphere boundaries.
For general `m`, this is an `m`-edge simultaneous sum, not a single binary connected sum. -/
abbrev CoordinateUnlinkExteriorPlanarNeckDirectMultiInteriorConnectedSum :=
  TopologicalPushout
    (coordinateUnlinkExteriorPlanarNeckDirectMultiSumToLeft m)
    (coordinateUnlinkExteriorPlanarNeckDirectMultiSumToRight m)

/-- Transport the compact cut pushout to the literal complements in the two direct capping
targets. -/
def coordinateUnlinkExteriorPlanarCompactCutPushoutHomeomorphDirectMultiSum :
    CoordinateUnlinkExteriorPlanarCompactCutPushout m ≃ₜ
      CoordinateUnlinkExteriorPlanarNeckDirectMultiInteriorConnectedSum m :=
  topologicalPushoutCongr
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckDirectMultiSumToLeft m)
    (coordinateUnlinkExteriorPlanarNeckDirectMultiSumToRight m)
    (Homeomorph.refl (ZMod m × Sphere 3))
    (compactNeckLeftCutHomeomorphComplementOneHandles m)
    (compactNeckRightCutHomeomorphComplementOneHandle m)
    (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- Exact multi-interior-connected-sum recognition of the original compact coordinate
exterior, at the point-set level. -/
def coordinateUnlinkExteriorPlanarDirectMultiInteriorConnectedSumHomeomorph :
    CoordinateUnlinkExteriorEighthPowerPullback m ≃ₜ
      CoordinateUnlinkExteriorPlanarNeckDirectMultiInteriorConnectedSum m :=
  (coordinateUnlinkExteriorPlanarCompactCutPushoutHomeomorph m).symm.trans
    (coordinateUnlinkExteriorPlanarCompactCutPushoutHomeomorphDirectMultiSum m)

@[simp] theorem
    coordinateUnlinkExteriorPlanarCompactCutPushoutHomeomorphDirectMultiSum_inl
    (x : CompactNeckLeftCut m) :
    coordinateUnlinkExteriorPlanarCompactCutPushoutHomeomorphDirectMultiSum m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m) x) =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckDirectMultiSumToLeft m)
        (coordinateUnlinkExteriorPlanarNeckDirectMultiSumToRight m)
        (compactNeckLeftCutHomeomorphComplementOneHandles m x) := by
  apply topologicalPushoutCongr_inl

@[simp] theorem
    coordinateUnlinkExteriorPlanarCompactCutPushoutHomeomorphDirectMultiSum_inr
    (x : CompactNeckRightCut m) :
    coordinateUnlinkExteriorPlanarCompactCutPushoutHomeomorphDirectMultiSum m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m) x) =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckDirectMultiSumToLeft m)
        (coordinateUnlinkExteriorPlanarNeckDirectMultiSumToRight m)
        (compactNeckRightCutHomeomorphComplementOneHandle m x) := by
  apply topologicalPushoutCongr_inr

@[simp] theorem coordinateUnlinkExteriorPlanarDirectMultiInteriorConnectedSumHomeomorph_left
    (x : CompactNeckLeftCut m) :
    coordinateUnlinkExteriorPlanarDirectMultiInteriorConnectedSumHomeomorph m x.1 =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckDirectMultiSumToLeft m)
        (coordinateUnlinkExteriorPlanarNeckDirectMultiSumToRight m)
        (compactNeckLeftCutHomeomorphComplementOneHandles m x) := by
  let _ := coordinateUnlinkExteriorPlanarCompactCutPushoutChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  have hreg :
      coordinateUnlinkExteriorPlanarCompactCutPushoutHomeomorph m
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
            (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m) x) = x.1 := by
    rw [← coordinateUnlinkExteriorPlanarCompactCutPushoutDiffeomorph_apply]
    exact coordinateUnlinkExteriorPlanarCompactCutPushoutDiffeomorph_inl m x
  unfold coordinateUnlinkExteriorPlanarDirectMultiInteriorConnectedSumHomeomorph
  rw [Homeomorph.trans_apply]
  rw [← hreg]
  rw [Homeomorph.symm_apply_apply]
  exact coordinateUnlinkExteriorPlanarCompactCutPushoutHomeomorphDirectMultiSum_inl m x

@[simp] theorem coordinateUnlinkExteriorPlanarDirectMultiInteriorConnectedSumHomeomorph_right
    (x : CompactNeckRightCut m) :
    coordinateUnlinkExteriorPlanarDirectMultiInteriorConnectedSumHomeomorph m x.1 =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckDirectMultiSumToLeft m)
        (coordinateUnlinkExteriorPlanarNeckDirectMultiSumToRight m)
        (compactNeckRightCutHomeomorphComplementOneHandle m x) := by
  let _ := coordinateUnlinkExteriorPlanarCompactCutPushoutChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  have hreg :
      coordinateUnlinkExteriorPlanarCompactCutPushoutHomeomorph m
          (topologicalPushoutInr
            (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
            (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m) x) = x.1 := by
    rw [← coordinateUnlinkExteriorPlanarCompactCutPushoutDiffeomorph_apply]
    exact coordinateUnlinkExteriorPlanarCompactCutPushoutDiffeomorph_inr m x
  unfold coordinateUnlinkExteriorPlanarDirectMultiInteriorConnectedSumHomeomorph
  rw [Homeomorph.trans_apply]
  rw [← hreg]
  rw [Homeomorph.symm_apply_apply]
  exact coordinateUnlinkExteriorPlanarCompactCutPushoutHomeomorphDirectMultiSum_inr m x

end SplittingSpheres
