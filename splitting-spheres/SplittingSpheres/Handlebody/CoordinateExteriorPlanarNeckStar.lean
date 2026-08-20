/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutEmbedding
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckGridSphereComparison
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckLeftFamilyCapping
public import SplittingSpheres.Handlebody.ProductFourBallBoundaryInclusion

/-!
# The literal neck-star complement model

This file records exactly what remains after removing the strict model interiors of the
standard product-four-ball caps from the two capped neck columns.  The simultaneous left
column becomes a complement inside `ZMod m × OneHandlePiece`, while the right column becomes
a complement inside `OneHandlePiece`.  The original column-first partial spin is then the
pushout of these two displayed complements along `ZMod m × Sphere 3`.

All interiors below are the `ModelWithCorners.interior` of the explicit `ProductFourBall`.
No identification with a conventional connected sum, and no smoothness, local flatness,
manifold, or separation assertion is made.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## Simultaneous left cap family -/

/-- The attaching map from the common neck family to the uncapped left column. -/
abbrev coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckLeftFamilyBoundary m,
      CoordinateUnlinkExteriorPlanarNeckLeftFamilyUncapped m) :=
  (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
    m).verticalCenterToLeft

/-- The attaching map from the common neck family to the labelled cap family. -/
abbrev coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckLeftFamilyBoundary m,
      CoordinateUnlinkExteriorPlanarNeckLeftFamilyCaps m) :=
  (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
    m).verticalCenterToRight

/-- The uncapped-column coprojection into the simultaneously capped left family. -/
abbrev coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedToCapped
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckLeftFamilyUncapped m,
      CoordinateUnlinkExteriorPlanarNeckLeftFamilyCapped m) :=
  topologicalPushoutInl
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped m)
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps m)

/-- The cap-family coprojection into the simultaneously capped left family. -/
abbrev coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsToCapped
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckLeftFamilyCaps m,
      CoordinateUnlinkExteriorPlanarNeckLeftFamilyCapped m) :=
  topologicalPushoutInr
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped m)
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps m)

/-- Exact normalized coordinates on the common simultaneous-left neck family. -/
def coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryHomeomorphSphere
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckLeftFamilyBoundary m ≃ₜ
      ZMod m × Sphere 3 :=
  (coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryHomeomorphOriginal m).trans
    (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m)

/-- The simultaneous-left neck-to-cap map is a closed embedding. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps m) := by
  let Hcap :=
    coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsHomeomorphProductFourBall m
  let Hboundary :=
    coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryHomeomorphSphere m
  have heq :
      Hcap ∘ coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps m =
        coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryInclusion m ∘
          Hboundary := by
    funext q
    exact coordinateUnlinkExteriorPlanarNeckLeftFamily_boundary m q
  apply Hcap.isClosedEmbedding.of_comp_iff.mp
  rw [heq]
  exact
    (isClosedEmbedding_labelledProductFourSphereBoundaryInclusion m).comp
      Hboundary.isClosedEmbedding

/-- The simultaneous-left neck-to-uncapped-column map is a closed embedding. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped m) := by
  let Huncapped :=
    coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal m
  let Hboundary :=
    coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryHomeomorphOriginal m
  have heq :
      Huncapped ∘
          coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped m =
        (coordinateUnlinkExteriorPlanarNeckGridDiagram
          m).verticalCenterToLeft ∘ Hboundary := by
    funext q
    exact simLeft_uncapped_compatibility m q
  apply Huncapped.isClosedEmbedding.of_comp_iff.mp
  rw [heq]
  exact
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckGridVerticalCenterToLeft
      m).comp Hboundary.isClosedEmbedding

/-- The labelled cap family is closed embedded in the capped left family. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsToCapped
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsToCapped m) :=
  isClosedEmbedding_topologicalPushoutInr
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped m)
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped m)

/-- The uncapped left column is closed embedded in the capped left family. -/
theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedToCapped
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedToCapped m) :=
  isClosedEmbedding_topologicalPushoutInl
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped m)
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps m)

/-- The attaching-boundary subset of the labelled left cap family. -/
def coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsBoundary
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorPlanarNeckLeftFamilyCaps m) :=
  range (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps m)

/-- The strict model-interior subset of the labelled left cap family. -/
def coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsStrictInterior
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorPlanarNeckLeftFamilyCaps m) :=
  (coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsHomeomorphProductFourBall m) ⁻¹'
    (univ ×ˢ productFourBallModel.interior ProductFourBall)

theorem coordinateUnlinkExteriorPlanarNeckLeftFamily_mem_capsBoundary_iff
    (m : ℕ) [NeZero m]
    (c : CoordinateUnlinkExteriorPlanarNeckLeftFamilyCaps m) :
    c ∈ coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsBoundary m ↔
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsHomeomorphProductFourBall
        m c).2 ∈ range productFourSphereBoundaryInclusion := by
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryHomeomorphSphere m q).2,
      ?_⟩
    exact (congrArg Prod.snd
      (coordinateUnlinkExteriorPlanarNeckLeftFamily_boundary m q)).symm
  · rintro ⟨s, hs⟩
    let Hcap :=
      coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsHomeomorphProductFourBall m
    let Hboundary :=
      coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryHomeomorphSphere m
    let q := Hboundary.symm ((Hcap c).1, s)
    refine ⟨q, Hcap.injective ?_⟩
    rw [coordinateUnlinkExteriorPlanarNeckLeftFamily_boundary]
    change coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryInclusion m
      (Hboundary q) = Hcap c
    rw [Hboundary.apply_symm_apply]
    exact Prod.ext rfl hs

theorem coordinateUnlinkExteriorPlanarNeckLeftFamily_capsBoundary_eq_preimage
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsBoundary m =
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsHomeomorphProductFourBall
        m) ⁻¹' (univ ×ˢ range productFourSphereBoundaryInclusion) := by
  ext c
  rw [coordinateUnlinkExteriorPlanarNeckLeftFamily_mem_capsBoundary_iff]
  simp only [mem_preimage, mem_prod, mem_univ, true_and]

/-- The boundary complement in each explicit left cap is its strict model interior. -/
theorem coordinateUnlinkExteriorPlanarNeckLeftFamily_compl_capsBoundary
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsBoundary m)ᶜ =
      coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsStrictInterior m := by
  ext c
  rw [mem_compl_iff,
    coordinateUnlinkExteriorPlanarNeckLeftFamily_mem_capsBoundary_iff]
  unfold coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsStrictInterior
  simp only [mem_preimage, mem_prod, mem_univ, true_and]
  rw [← mem_compl_iff, compl_range_productFourSphereBoundaryInclusion]

/-- The image of all strict left cap interiors in the capped left family. -/
def coordinateUnlinkExteriorPlanarNeckLeftFamilyStrictCapInteriorImage
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorPlanarNeckLeftFamilyCapped m) :=
  coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsToCapped m ''
    coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsStrictInterior m

/-- The uncapped left column is exactly the complement of the strict cap-interior image. -/
theorem coordinateUnlinkExteriorPlanarNeckLeftFamily_range_uncappedToCapped
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedToCapped m) =
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyStrictCapInteriorImage m)ᶜ := by
  rw [range_topologicalPushoutInl_eq_compl_image_inr_compl_range
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped m)
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped
      m).injective]
  change
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsToCapped m ''
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsBoundary m)ᶜ)ᶜ =
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyStrictCapInteriorImage m)ᶜ
  rw [coordinateUnlinkExteriorPlanarNeckLeftFamily_compl_capsBoundary]
  rfl

/-- The closed cap-family embedding in the displayed labelled one-handles. -/
def coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsToOneHandles
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckLeftFamilyCaps m,
      ZMod m × OneHandlePiece) where
  toFun c :=
    coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsToCapped m c)
  continuous_toFun :=
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle
      m).continuous.comp
        (coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsToCapped m).continuous

theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsToOneHandles
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsToOneHandles m) :=
  (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle
    m).isClosedEmbedding.comp
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsToCapped m)

/-- On the attaching boundary, the cap and uncapped embeddings agree in the displayed
labelled one-handles. -/
theorem coordinateUnlinkExteriorPlanarNeckLeftFamily_caps_uncapped_compatibility
    (m : ℕ) [NeZero m]
    (q : CoordinateUnlinkExteriorPlanarNeckLeftFamilyBoundary m) :
    coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsToOneHandles m
        (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps m q) =
      coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m
        (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedToCapped m
          (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped m q)) := by
  change coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsToCapped m
        (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps m q)) = _
  exact congrArg
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m)
    (topologicalPushout_condition
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped m)
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps m) q).symm

/-- The strict left cap-interior image transported to the displayed labelled one-handles. -/
def coordinateUnlinkExteriorPlanarNeckLeftFamilyStrictCapInteriorOneHandles
    (m : ℕ) [NeZero m] :
    Set (ZMod m × OneHandlePiece) :=
  coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m ''
    coordinateUnlinkExteriorPlanarNeckLeftFamilyStrictCapInteriorImage m

theorem coordinateUnlinkExteriorPlanarNeckLeftFamily_strictCapInteriorOneHandles_eq_image
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarNeckLeftFamilyStrictCapInteriorOneHandles m =
      coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsToOneHandles m ''
        coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsStrictInterior m := by
  rw [coordinateUnlinkExteriorPlanarNeckLeftFamilyStrictCapInteriorOneHandles,
    coordinateUnlinkExteriorPlanarNeckLeftFamilyStrictCapInteriorImage,
    image_image]
  rfl

/-- The original uncapped left column as the literal complement subtype inside the labelled
one-handle family. -/
def coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphComplementOneHandles
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckLeftFamilyUncapped m ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarNeckLeftFamilyStrictCapInteriorOneHandles m)ᶜ :=
  (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedToCapped
    m).isEmbedding.toHomeomorph |>.trans
      ((Homeomorph.setCongr
        (coordinateUnlinkExteriorPlanarNeckLeftFamily_range_uncappedToCapped m)).trans <|
        ((coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m).image
          (coordinateUnlinkExteriorPlanarNeckLeftFamilyStrictCapInteriorImage m)ᶜ).trans <|
            Homeomorph.setCongr
              (by
                simpa [
                  coordinateUnlinkExteriorPlanarNeckLeftFamilyStrictCapInteriorOneHandles]
                  using
                    (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle
                      m).toEquiv.image_compl
                        (coordinateUnlinkExteriorPlanarNeckLeftFamilyStrictCapInteriorImage
                          m)))

@[simp]
theorem
    coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphComplementOneHandles_apply_coe
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckLeftFamilyUncapped m) :
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphComplementOneHandles
      m x : ZMod m × OneHandlePiece) =
      coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m
        (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedToCapped m x) :=
  rfl

/-! ## Simultaneous right-node cap family -/

/-- Exact normalized coordinates on the common right-node neck family. -/
def coordinateUnlinkExteriorPlanarRightNodeNeckBoundaryHomeomorphSphere
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarRightNodeNeckBoundaryFamily m ≃ₜ
      ZMod m × Sphere 3 :=
  (coordinateUnlinkExteriorPlanarRightNodeNeckBoundaryHomeomorphNeckGridVerticalCenter
    m).trans (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m)

/-- The labelled standard boundary inclusion used by the right cap family. -/
abbrev coordinateUnlinkExteriorPlanarRightNodeBoundaryInclusion
    (m : ℕ) :
    C(ZMod m × Sphere 3, ZMod m × ProductFourBall) :=
  coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryInclusion m

/-- Exact conjugacy of the right-node attaching map with the labelled standard boundary. -/
theorem coordinateUnlinkExteriorPlanarRightNode_neckToCapFamily_conjugacy
    (m : ℕ) [NeZero m]
    (q : CoordinateUnlinkExteriorPlanarRightNodeNeckBoundaryFamily m) :
    coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph m
        (coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m q) =
      coordinateUnlinkExteriorPlanarRightNodeBoundaryInclusion m
        (coordinateUnlinkExteriorPlanarRightNodeNeckBoundaryHomeomorphSphere m q) := by
  let D := coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m
  rcases topologicalPushout_jointly_surjective D.centerToTop D.centerToBottom q with
    ⟨e, rfl⟩ | ⟨x, rfl⟩
  · rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inl,
      coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph_inl]
    change _ = coordinateUnlinkExteriorPlanarRightNodeBoundaryInclusion m
      (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToTop
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToBottom e))
    rw [coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_inl]
    change (_, _) = (_, productFourSphereBoundaryInclusion
      (productFourBoundaryPushoutHomeomorphSphere
        (topologicalPushoutInr productFourCornerToSide productFourCornerToEnd
          (e.1.2, e.2))))
    rw [productFourSphereBoundaryInclusion_end]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact euclideanClosedBallOneHomeomorphUnitInterval.symm_apply_apply
          ⟨e.1.2.1, sphere_subset_closedBall e.1.2.2⟩
      · rfl
  · rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inr,
      coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph_inr]
    change _ = coordinateUnlinkExteriorPlanarRightNodeBoundaryInclusion m
      (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToTop
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToBottom x))
    rw [coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_inr]
    change (_, _) = (_, productFourSphereBoundaryInclusion
      (productFourBoundaryPushoutHomeomorphSphere
        (topologicalPushoutInl productFourCornerToSide productFourCornerToEnd
          (unitIntervalToEuclideanClosedBallOne x.1.2, x.2))))
    rw [productFourSphereBoundaryInclusion_side]
    rfl

theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m) := by
  let Hcap := coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph m
  let Hboundary :=
    coordinateUnlinkExteriorPlanarRightNodeNeckBoundaryHomeomorphSphere m
  have heq :
      Hcap ∘ coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m =
        coordinateUnlinkExteriorPlanarRightNodeBoundaryInclusion m ∘
          Hboundary := by
    funext q
    exact coordinateUnlinkExteriorPlanarRightNode_neckToCapFamily_conjugacy m q
  apply Hcap.isClosedEmbedding.of_comp_iff.mp
  rw [heq]
  exact
    (isClosedEmbedding_labelledProductFourSphereBoundaryInclusion m).comp
      Hboundary.isClosedEmbedding

theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped m) := by
  change IsClosedEmbedding
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
  exact
    isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckGridVerticalCenterToRight m

theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarRightNodeCapFamilyToCapped
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarRightNodeCapFamilyToCapped m) :=
  isClosedEmbedding_topologicalPushoutInl
    (coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m)
    (coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped m)

theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarRightNodeUncappedToCapped
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarRightNodeUncappedToCapped m) :=
  isClosedEmbedding_topologicalPushoutInr
    (coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m)
    (coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m)

/-- The attaching-boundary subset of the right-node cap family. -/
def coordinateUnlinkExteriorPlanarRightNodeCapFamilyBoundary
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorPlanarRightNodeCapFamily m) :=
  range (coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m)

/-- The strict model-interior subset of the right-node cap family. -/
def coordinateUnlinkExteriorPlanarRightNodeCapFamilyStrictInterior
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorPlanarRightNodeCapFamily m) :=
  (coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph m) ⁻¹'
    (univ ×ˢ productFourBallModel.interior ProductFourBall)

theorem coordinateUnlinkExteriorPlanarRightNode_mem_capFamilyBoundary_iff
    (m : ℕ) [NeZero m]
    (c : CoordinateUnlinkExteriorPlanarRightNodeCapFamily m) :
    c ∈ coordinateUnlinkExteriorPlanarRightNodeCapFamilyBoundary m ↔
      (coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph m c).2 ∈
        range productFourSphereBoundaryInclusion := by
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨
      (coordinateUnlinkExteriorPlanarRightNodeNeckBoundaryHomeomorphSphere m q).2,
      ?_⟩
    exact (congrArg Prod.snd
      (coordinateUnlinkExteriorPlanarRightNode_neckToCapFamily_conjugacy
        m q)).symm
  · rintro ⟨s, hs⟩
    let Hcap := coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph m
    let Hboundary :=
      coordinateUnlinkExteriorPlanarRightNodeNeckBoundaryHomeomorphSphere m
    let q := Hboundary.symm ((Hcap c).1, s)
    refine ⟨q, Hcap.injective ?_⟩
    rw [coordinateUnlinkExteriorPlanarRightNode_neckToCapFamily_conjugacy,
      Hboundary.apply_symm_apply]
    exact Prod.ext rfl hs

theorem coordinateUnlinkExteriorPlanarRightNode_capFamilyBoundary_eq_preimage
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarRightNodeCapFamilyBoundary m =
      (coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph m) ⁻¹'
        (univ ×ˢ range productFourSphereBoundaryInclusion) := by
  ext c
  rw [coordinateUnlinkExteriorPlanarRightNode_mem_capFamilyBoundary_iff]
  simp only [mem_preimage, mem_prod, mem_univ, true_and]

/-- The boundary complement in the right cap family is its strict model interior. -/
theorem coordinateUnlinkExteriorPlanarRightNode_compl_capFamilyBoundary
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarRightNodeCapFamilyBoundary m)ᶜ =
      coordinateUnlinkExteriorPlanarRightNodeCapFamilyStrictInterior m := by
  ext c
  rw [mem_compl_iff,
    coordinateUnlinkExteriorPlanarRightNode_mem_capFamilyBoundary_iff]
  unfold coordinateUnlinkExteriorPlanarRightNodeCapFamilyStrictInterior
  simp only [mem_preimage, mem_prod, mem_univ, true_and]
  rw [← mem_compl_iff, compl_range_productFourSphereBoundaryInclusion]

/-- The image of the strict right cap interiors in the capped right node. -/
def coordinateUnlinkExteriorPlanarRightNodeStrictCapInteriorImage
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorPlanarRightNodeCapped m) :=
  coordinateUnlinkExteriorPlanarRightNodeCapFamilyToCapped m ''
    coordinateUnlinkExteriorPlanarRightNodeCapFamilyStrictInterior m

/-- The uncapped right node is exactly the complement of the strict cap-interior image. -/
theorem coordinateUnlinkExteriorPlanarRightNode_range_uncappedToCapped
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarRightNodeUncappedToCapped m) =
      (coordinateUnlinkExteriorPlanarRightNodeStrictCapInteriorImage m)ᶜ := by
  rw [range_topologicalPushoutInr_eq_compl_image_inl_compl_range
    (coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m)
    (coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped
      m).injective]
  change
    (coordinateUnlinkExteriorPlanarRightNodeCapFamilyToCapped m ''
      (coordinateUnlinkExteriorPlanarRightNodeCapFamilyBoundary m)ᶜ)ᶜ =
      (coordinateUnlinkExteriorPlanarRightNodeStrictCapInteriorImage m)ᶜ
  rw [coordinateUnlinkExteriorPlanarRightNode_compl_capFamilyBoundary]
  rfl

/-- The closed right cap-family embedding in the displayed central one-handle. -/
def coordinateUnlinkExteriorPlanarRightNodeCapFamilyToOneHandle
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarRightNodeCapFamily m,
      OneHandlePiece) where
  toFun c :=
    coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle m
      (coordinateUnlinkExteriorPlanarRightNodeCapFamilyToCapped m c)
  continuous_toFun :=
    (coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle
      m).continuous.comp
        (coordinateUnlinkExteriorPlanarRightNodeCapFamilyToCapped m).continuous

theorem isClosedEmbedding_coordinateUnlinkExteriorPlanarRightNodeCapFamilyToOneHandle
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarRightNodeCapFamilyToOneHandle m) :=
  (coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle
    m).isClosedEmbedding.comp
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarRightNodeCapFamilyToCapped m)

/-- On the attaching boundary, the cap and uncapped embeddings agree in the displayed
central one-handle. -/
theorem coordinateUnlinkExteriorPlanarRightNode_cap_uncapped_compatibility
    (m : ℕ) [NeZero m]
    (q : CoordinateUnlinkExteriorPlanarRightNodeNeckBoundaryFamily m) :
    coordinateUnlinkExteriorPlanarRightNodeCapFamilyToOneHandle m
        (coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m q) =
      coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle m
        (coordinateUnlinkExteriorPlanarRightNodeUncappedToCapped m
          (coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped m q)) := by
  change coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle m
      (coordinateUnlinkExteriorPlanarRightNodeCapFamilyToCapped m
        (coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m q)) = _
  exact congrArg
    (coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle m)
    (topologicalPushout_condition
      (coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m)
      (coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped m) q)

/-- The strict right cap-interior image transported to the displayed one-handle. -/
def coordinateUnlinkExteriorPlanarRightNodeStrictCapInteriorOneHandle
    (m : ℕ) [NeZero m] :
    Set OneHandlePiece :=
  coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle m ''
    coordinateUnlinkExteriorPlanarRightNodeStrictCapInteriorImage m

theorem coordinateUnlinkExteriorPlanarRightNode_strictCapInteriorOneHandle_eq_image
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarRightNodeStrictCapInteriorOneHandle m =
      coordinateUnlinkExteriorPlanarRightNodeCapFamilyToOneHandle m ''
        coordinateUnlinkExteriorPlanarRightNodeCapFamilyStrictInterior m := by
  rw [coordinateUnlinkExteriorPlanarRightNodeStrictCapInteriorOneHandle,
    coordinateUnlinkExteriorPlanarRightNodeStrictCapInteriorImage, image_image]
  rfl

/-- The original uncapped right column as the literal complement subtype in a one-handle. -/
def coordinateUnlinkExteriorPlanarRightNodeUncappedHomeomorphComplementOneHandle
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarRightNodeUncapped m ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarRightNodeStrictCapInteriorOneHandle m)ᶜ :=
  (isClosedEmbedding_coordinateUnlinkExteriorPlanarRightNodeUncappedToCapped
    m).isEmbedding.toHomeomorph |>.trans
      ((Homeomorph.setCongr
        (coordinateUnlinkExteriorPlanarRightNode_range_uncappedToCapped m)).trans <|
        ((coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle m).image
          (coordinateUnlinkExteriorPlanarRightNodeStrictCapInteriorImage m)ᶜ).trans <|
            Homeomorph.setCongr
              (by
                simpa [coordinateUnlinkExteriorPlanarRightNodeStrictCapInteriorOneHandle]
                  using
                    (coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle
                      m).toEquiv.image_compl
                        (coordinateUnlinkExteriorPlanarRightNodeStrictCapInteriorImage m)))

@[simp]
theorem
    coordinateUnlinkExteriorPlanarRightNodeUncappedHomeomorphComplementOneHandle_apply_coe
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarRightNodeUncapped m) :
    (coordinateUnlinkExteriorPlanarRightNodeUncappedHomeomorphComplementOneHandle
      m x : OneHandlePiece) =
      coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle m
        (coordinateUnlinkExteriorPlanarRightNodeUncappedToCapped m x) :=
  rfl

/-! ## Literal star pushout -/

/-- The displayed complement of the strict cap interiors in the labelled left one-handles. -/
abbrev CoordinateUnlinkExteriorPlanarNeckLeftComplement
    (m : ℕ) [NeZero m] :=
  ↑(coordinateUnlinkExteriorPlanarNeckLeftFamilyStrictCapInteriorOneHandles m)ᶜ

/-- The displayed complement of the strict cap interiors in the central one-handle. -/
abbrev CoordinateUnlinkExteriorPlanarNeckRightComplement
    (m : ℕ) [NeZero m] :=
  ↑(coordinateUnlinkExteriorPlanarRightNodeStrictCapInteriorOneHandle m)ᶜ

/-- Identify the original left grid column with its literal complement model. -/
def coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalLeft ≃ₜ
      CoordinateUnlinkExteriorPlanarNeckLeftComplement m :=
  (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal
    m).symm.trans
      (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphComplementOneHandles
        m)

/-- Identify the original right grid column with its literal complement model. -/
def coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalRight ≃ₜ
      CoordinateUnlinkExteriorPlanarNeckRightComplement m :=
  (coordinateUnlinkExteriorPlanarRightNodeUncappedHomeomorphNeckGridVerticalRight
    m).symm.trans
      (coordinateUnlinkExteriorPlanarRightNodeUncappedHomeomorphComplementOneHandle
        m)

/-- The left star attaching map, obtained by transporting the original left grid leg to the
literal complement coordinates. -/
def coordinateUnlinkExteriorPlanarNeckStarToLeft
    (m : ℕ) [NeZero m] :
    C(ZMod m × Sphere 3,
      CoordinateUnlinkExteriorPlanarNeckLeftComplement m) where
  toFun x :=
    coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
      ((coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
        ((coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x))
  continuous_toFun :=
    (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement
      m).continuous.comp <|
      (coordinateUnlinkExteriorPlanarNeckGridDiagram
        m).verticalCenterToLeft.continuous.comp
          (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph
            m).symm.continuous

/-- The right star attaching map, obtained by transporting the original right grid leg to the
literal complement coordinates. -/
def coordinateUnlinkExteriorPlanarNeckStarToRight
    (m : ℕ) [NeZero m] :
    C(ZMod m × Sphere 3,
      CoordinateUnlinkExteriorPlanarNeckRightComplement m) where
  toFun x :=
    coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m
      ((coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
        ((coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm x))
  continuous_toFun :=
    (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement
      m).continuous.comp <|
      (coordinateUnlinkExteriorPlanarNeckGridDiagram
        m).verticalCenterToRight.continuous.comp
          (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph
            m).symm.continuous

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckStarToLeft_apply
    (m : ℕ) [NeZero m] (x : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarNeckStarToLeft m x =
      coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m
        ((coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
          ((coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm
            x)) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckStarToRight_apply
    (m : ℕ) [NeZero m] (x : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarNeckStarToRight m x =
      coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m
        ((coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
          ((coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m).symm
            x)) :=
  rfl

/-- The literal star-shaped point-set model: labelled left complements and the central right
complement are attached along their common normalized family of three-spheres. -/
abbrev CoordinateUnlinkExteriorPlanarNeckStar
    (m : ℕ) [NeZero m] :=
  TopologicalPushout
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)

/-- The original column-first regrouping is exactly the literal complement star. -/
def coordinateUnlinkExteriorPlanarNeckGridColumnFirstHomeomorphStar
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).columnFirst ≃ₜ
      CoordinateUnlinkExteriorPlanarNeckStar m :=
  topologicalPushoutCongr
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m)
    (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m)
    (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement m)
    (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement m)
    (by
      intro q
      rw [coordinateUnlinkExteriorPlanarNeckStarToLeft_apply,
        (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph
          m).symm_apply_apply])
    (by
      intro q
      rw [coordinateUnlinkExteriorPlanarNeckStarToRight_apply,
        (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph
          m).symm_apply_apply])

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridColumnFirstHomeomorphStar_inl
    (m : ℕ) [NeZero m]
    (x : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalLeft) :
    coordinateUnlinkExteriorPlanarNeckGridColumnFirstHomeomorphStar m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight x) =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)
        (coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement
          m x) := by
  apply topologicalPushoutCongr_inl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridColumnFirstHomeomorphStar_inr
    (m : ℕ) [NeZero m]
    (x : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalRight) :
    coordinateUnlinkExteriorPlanarNeckGridColumnFirstHomeomorphStar m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToRight x) =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)
        (coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement
          m x) := by
  apply topologicalPushoutCongr_inr

/-- The original flower partial spin, via its exact column regrouping, is homeomorphic to the
literal complement star. -/
def coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m ≃ₜ
      CoordinateUnlinkExteriorPlanarNeckStar m :=
  (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckGridColumnFirst
    m).trans
      (coordinateUnlinkExteriorPlanarNeckGridColumnFirstHomeomorphStar m)

end SplittingSpheres
