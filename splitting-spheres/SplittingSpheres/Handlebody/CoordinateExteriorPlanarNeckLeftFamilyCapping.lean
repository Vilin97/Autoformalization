/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCapping
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckGridVerticalCenter
public import SplittingSpheres.Handlebody.ProductFourBallBoundaryInclusion

/-!
# Simultaneously capping the labelled left neck family

This file retains the original neck grid's left column and central neck family and attaches
one interval-product four-ball for every label.  It identifies the cap family with a product
of `ZMod m` and `ProductFourBall`, and the capped family with `ZMod m × OneHandlePiece`.

The endpoint-to-seam offset remains symbolic.  These are point-set topological statements:
no smoothness, separation, or connected-sum assertion is made.
-/

@[expose] public section

open Function Metric Topology

noncomputable section

namespace SplittingSpheres

open SplittingSpheres

abbrev SimLeftC (m : ℕ) := CoordinateUnlinkExteriorPlanarNeckGridC m
abbrev SimLeftE (m : ℕ) := CoordinateUnlinkExteriorPlanarNeckGridE m
abbrev SimLeftA (m : ℕ) := CoordinateUnlinkExteriorPlanarNeckGridA m
abbrev SimLeftBL (m : ℕ) := CoordinateUnlinkExteriorPlanarNeckGridBL m
abbrev SimLeftBR (m : ℕ) := CoordinateUnlinkExteriorPlanarNeckGridA m
abbrev SimLeftHL (m : ℕ) := CoordinateUnlinkExteriorPlanarNeckGridHL m
abbrev SimLeftHR (m : ℕ) := CoordinateUnlinkExteriorPlanarNeckGridHR m
abbrev SimLeftFL (m : ℕ) := CoordinateUnlinkExteriorPlanarNeckGridFL m
abbrev SimLeftFR (m : ℕ) := CoordinateUnlinkExteriorPlanarNeckGridA m

def simLeftDiagram (m : ℕ) [NeZero m] :
    TopologicalPushoutGridDiagram
      (SimLeftC m) (SimLeftE m) (SimLeftA m)
      (SimLeftBL m) (SimLeftBR m) (SimLeftHL m) (SimLeftHR m)
      (SimLeftFL m) (SimLeftFR m) where
  centerToTop := (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToTop
  centerToBottom := (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToBottom
  centerToLeft := (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToLeft
  centerToRight :=
    coordinateUnlinkExteriorPlanarRightNodeCappingGridCenterToLeft m
  topToTopLeft := (coordinateUnlinkExteriorPlanarNeckGridDiagram m).topToTopLeft
  topToTopRight :=
    coordinateUnlinkExteriorPlanarRightNodeCappingGridTopToTopLeft m
  bottomToBottomLeft :=
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).bottomToBottomLeft
  bottomToBottomRight :=
    coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomLeft m
  leftToTopLeft := (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
  leftToBottomLeft :=
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
  rightToTopRight :=
    coordinateUnlinkExteriorPlanarRightNodeCappingGridLeftToTopLeft m
  rightToBottomRight :=
    coordinateUnlinkExteriorPlanarRightNodeCappingGridLeftToBottomLeft m
  commTopLeft := coordinateUnlinkExteriorPlanarNeckGrid_commTopLeft m
  commTopRight := by rintro ⟨⟨a, e⟩, s⟩; rfl
  commBottomLeft := coordinateUnlinkExteriorPlanarNeckGrid_commBottomLeft m
  commBottomRight := by rintro ⟨⟨a, t⟩, s⟩; rfl

def simLeftVerticalCenterOriginal (m : ℕ) [NeZero m] :
    (simLeftDiagram m).verticalCenter ≃ₜ
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenter :=
  topologicalPushoutCongr
    (simLeftDiagram m).centerToTop (simLeftDiagram m).centerToBottom
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToTop
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToBottom
    (Homeomorph.refl (SimLeftC m)) (Homeomorph.refl (SimLeftE m))
    (Homeomorph.refl (SimLeftA m)) (by intro; rfl) (by intro; rfl)

def simLeftVerticalLeftOriginal (m : ℕ) [NeZero m] :
    (simLeftDiagram m).verticalLeft ≃ₜ
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalLeft :=
  topologicalPushoutCongr
    (simLeftDiagram m).leftToTopLeft (simLeftDiagram m).leftToBottomLeft
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft
    (Homeomorph.refl (SimLeftBL m)) (Homeomorph.refl (SimLeftHL m))
    (Homeomorph.refl (SimLeftFL m)) (by intro; rfl) (by intro; rfl)

def simLeftVerticalRightCapFamily (m : ℕ) [NeZero m] :
    (simLeftDiagram m).verticalRight ≃ₜ
      CoordinateUnlinkExteriorPlanarRightNodeCapFamily m :=
  topologicalPushoutCongr
    (simLeftDiagram m).rightToTopRight (simLeftDiagram m).rightToBottomRight
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).leftToTopLeft
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).leftToBottomLeft
    (Homeomorph.refl (SimLeftBR m)) (Homeomorph.refl (SimLeftHR m))
    (Homeomorph.refl (SimLeftFR m)) (by intro; rfl) (by intro; rfl)

@[simp]
theorem simLeftVerticalCenterOriginal_inl
    (m : ℕ) [NeZero m] (e : SimLeftE m) :
    simLeftVerticalCenterOriginal m
        (topologicalPushoutInl (simLeftDiagram m).centerToTop
          (simLeftDiagram m).centerToBottom e) =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToTop
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToBottom e := by
  apply topologicalPushoutCongr_inl

@[simp]
theorem simLeftVerticalCenterOriginal_inr
    (m : ℕ) [NeZero m] (x : SimLeftA m) :
    simLeftVerticalCenterOriginal m
        (topologicalPushoutInr (simLeftDiagram m).centerToTop
          (simLeftDiagram m).centerToBottom x) =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToTop
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToBottom x := by
  apply topologicalPushoutCongr_inr

@[simp]
theorem simLeftVerticalLeftOriginal_inl
    (m : ℕ) [NeZero m] (x : SimLeftHL m) :
    simLeftVerticalLeftOriginal m
        (topologicalPushoutInl (simLeftDiagram m).leftToTopLeft
          (simLeftDiagram m).leftToBottomLeft x) =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft x := by
  apply topologicalPushoutCongr_inl

@[simp]
theorem simLeftVerticalLeftOriginal_inr
    (m : ℕ) [NeZero m] (x : SimLeftFL m) :
    simLeftVerticalLeftOriginal m
        (topologicalPushoutInr (simLeftDiagram m).leftToTopLeft
          (simLeftDiagram m).leftToBottomLeft x) =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
        (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft x := by
  apply topologicalPushoutCongr_inr

@[simp]
theorem simLeftVerticalRightCapFamily_inl
    (m : ℕ) [NeZero m] (x : SimLeftHR m) :
    simLeftVerticalRightCapFamily m
        (topologicalPushoutInl (simLeftDiagram m).rightToTopRight
          (simLeftDiagram m).rightToBottomRight x) =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).leftToTopLeft
        (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).leftToBottomLeft x := by
  apply topologicalPushoutCongr_inl

@[simp]
theorem simLeftVerticalRightCapFamily_inr
    (m : ℕ) [NeZero m] (x : SimLeftFR m) :
    simLeftVerticalRightCapFamily m
        (topologicalPushoutInr (simLeftDiagram m).rightToTopRight
          (simLeftDiagram m).rightToBottomRight x) =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).leftToTopLeft
        (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).leftToBottomLeft x := by
  apply topologicalPushoutCongr_inr

abbrev SimultaneousLeftCapped (m : ℕ) [NeZero m] :=
  (simLeftDiagram m).columnFirst

def simultaneousLeftNeckToUncapped (m : ℕ) [NeZero m] :
    C((simLeftDiagram m).verticalCenter, (simLeftDiagram m).verticalLeft) :=
  (simLeftDiagram m).verticalCenterToLeft

def simultaneousLeftNeckToCapFamily (m : ℕ) [NeZero m] :
    C((simLeftDiagram m).verticalCenter, (simLeftDiagram m).verticalRight) :=
  (simLeftDiagram m).verticalCenterToRight

example (m : ℕ) [NeZero m] :
    SimultaneousLeftCapped m =
      TopologicalPushout (simultaneousLeftNeckToUncapped m)
        (simultaneousLeftNeckToCapFamily m) :=
  rfl

def simLeftCapFamilyHomeomorph (m : ℕ) [NeZero m] :
    (simLeftDiagram m).verticalRight ≃ₜ ZMod m × ProductFourBall :=
  (simLeftVerticalRightCapFamily m).trans
    (coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph m)

@[simp]
theorem simLeftCapFamilyHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (b : EuclideanClosedBall 3) :
    simLeftCapFamilyHomeomorph m
        (topologicalPushoutInl
          (simLeftDiagram m).rightToTopRight
          (simLeftDiagram m).rightToBottomRight (x, b)) =
      (x.1, (unitIntervalToEuclideanClosedBallOne x.2, b)) := by
  rw [simLeftCapFamilyHomeomorph, Homeomorph.trans_apply]
  rw [simLeftVerticalRightCapFamily_inl,
    coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph_inl]

@[simp]
theorem simLeftCapFamilyHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (s : Sphere 2) :
    simLeftCapFamilyHomeomorph m
        (topologicalPushoutInr
          (simLeftDiagram m).rightToTopRight
          (simLeftDiagram m).rightToBottomRight (x, s)) =
      (x.1, (unitIntervalToEuclideanClosedBallOne x.2,
        coordinateUnlinkExteriorPlanarNeckGridSphereToBall s)) := by
  rw [simLeftCapFamilyHomeomorph, Homeomorph.trans_apply]
  rw [simLeftVerticalRightCapFamily_inr,
    coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph_inr]

def labelledProductFourSphereBoundaryInclusion (m : ℕ) :
    C(ZMod m × Sphere 3, ZMod m × ProductFourBall) :=
  (ContinuousMap.id (ZMod m)).prodMap productFourSphereBoundaryInclusion

@[simp]
theorem labelledProductFourSphereBoundaryInclusion_apply
    (m : ℕ) (x : ZMod m × Sphere 3) :
    labelledProductFourSphereBoundaryInclusion m x =
      (x.1, productFourSphereBoundaryInclusion x.2) :=
  rfl

theorem capFamily_boundary_compatibility
    (m : ℕ) [NeZero m]
    (q : (simLeftDiagram m).verticalCenter) :
    simLeftCapFamilyHomeomorph m
        (simultaneousLeftNeckToCapFamily m q) =
      labelledProductFourSphereBoundaryInclusion m
        (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m
          (simLeftVerticalCenterOriginal m q)) := by
  rcases topologicalPushout_jointly_surjective
      (simLeftDiagram m).centerToTop
      (simLeftDiagram m).centerToBottom q with
    ⟨e, rfl⟩ | ⟨x, rfl⟩
  · rw [simultaneousLeftNeckToCapFamily,
      TopologicalPushoutGridDiagram.verticalCenterToRight_inl,
      simLeftCapFamilyHomeomorph_inl,
      simLeftVerticalCenterOriginal_inl,
      coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_inl,
      labelledProductFourSphereBoundaryInclusion_apply,
      productFourSphereBoundaryInclusion_end]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · change euclideanClosedBallOneHomeomorphUnitInterval.symm
            (productFourEndUnitInterval e.1.2) =
          ⟨e.1.2.1, sphere_subset_closedBall e.1.2.2⟩
        exact euclideanClosedBallOneHomeomorphUnitInterval.symm_apply_apply _
      · rfl
  · rw [simultaneousLeftNeckToCapFamily,
      TopologicalPushoutGridDiagram.verticalCenterToRight_inr,
      simLeftCapFamilyHomeomorph_inr,
      simLeftVerticalCenterOriginal_inr,
      coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_inr,
      labelledProductFourSphereBoundaryInclusion_apply,
      productFourSphereBoundaryInclusion_side]
    change
      (x.1.1, (unitIntervalToEuclideanClosedBallOne x.1.2,
        coordinateUnlinkExteriorPlanarNeckGridSphereToBall x.2)) =
      (x.1.1, (unitIntervalToEuclideanClosedBallOne x.1.2,
        coordinateUnlinkExteriorPlanarNeckGridSphereToBall x.2))
    rfl

theorem simLeft_uncapped_compatibility
    (m : ℕ) [NeZero m] (q : (simLeftDiagram m).verticalCenter) :
    simLeftVerticalLeftOriginal m ((simLeftDiagram m).verticalCenterToLeft q) =
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
        (simLeftVerticalCenterOriginal m q) := by
  rcases topologicalPushout_jointly_surjective
      (simLeftDiagram m).centerToTop (simLeftDiagram m).centerToBottom q with
    ⟨e, rfl⟩ | ⟨x, rfl⟩
  · rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inl,
      simLeftVerticalLeftOriginal_inl, simLeftVerticalCenterOriginal_inl,
      TopologicalPushoutGridDiagram.verticalCenterToLeft_inl]
    apply congrArg (topologicalPushoutInl
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft)
    rfl
  · rw [TopologicalPushoutGridDiagram.verticalCenterToLeft_inr,
      simLeftVerticalLeftOriginal_inr, simLeftVerticalCenterOriginal_inr,
      TopologicalPushoutGridDiagram.verticalCenterToLeft_inr]
    apply congrArg (topologicalPushoutInr
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft)
    rfl

def originalNeckToSimultaneousCapFamily (m : ℕ) [NeZero m] :
    C((coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenter,
      CoordinateUnlinkExteriorPlanarRightNodeCapFamily m) where
  toFun q := simLeftVerticalRightCapFamily m
    ((simLeftDiagram m).verticalCenterToRight ((simLeftVerticalCenterOriginal m).symm q))
  continuous_toFun :=
    (simLeftVerticalRightCapFamily m).continuous.comp <|
      (simLeftDiagram m).verticalCenterToRight.continuous.comp
        (simLeftVerticalCenterOriginal m).symm.continuous

theorem originalNeckToSimultaneousCapFamily_boundary
    (m : ℕ) [NeZero m]
    (q : (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenter) :
    coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph m
        (originalNeckToSimultaneousCapFamily m q) =
      labelledProductFourSphereBoundaryInclusion m
        (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m q) := by
  have h := capFamily_boundary_compatibility m
    ((simLeftVerticalCenterOriginal m).symm q)
  rw [(simLeftVerticalCenterOriginal m).apply_symm_apply] at h
  exact h

theorem isClosedEmbedding_labelledProductFourSphereBoundaryInclusion
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding (labelledProductFourSphereBoundaryInclusion m) :=
  (labelledProductFourSphereBoundaryInclusion m).continuous.isClosedEmbedding <| by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    exact Prod.ext
      (congrArg (fun z : ZMod m × ProductFourBall ↦ z.1) h) <|
      injective_productFourSphereBoundaryInclusion
        (congrArg (fun z : ZMod m × ProductFourBall ↦ z.2) h)

theorem isClosedEmbedding_originalNeckToSimultaneousCapFamily
    (m : ℕ) [NeZero m] :
    IsClosedEmbedding (originalNeckToSimultaneousCapFamily m) := by
  let H := coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph m
  let V := coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m
  have hcomp : IsClosedEmbedding (H ∘ originalNeckToSimultaneousCapFamily m) := by
    have heq : (H ∘ originalNeckToSimultaneousCapFamily m) =
        labelledProductFourSphereBoundaryInclusion m ∘ V := by
      funext q
      exact originalNeckToSimultaneousCapFamily_boundary m q
    rw [heq]
    exact (isClosedEmbedding_labelledProductFourSphereBoundaryInclusion m).comp
      V.isClosedEmbedding
  exact IsClosedEmbedding.of_comp H.isEmbedding hcomp

theorem simLeft_cap_compatibility
    (m : ℕ) [NeZero m] (q : (simLeftDiagram m).verticalCenter) :
    simLeftVerticalRightCapFamily m ((simLeftDiagram m).verticalCenterToRight q) =
      originalNeckToSimultaneousCapFamily m (simLeftVerticalCenterOriginal m q) := by
  change _ = simLeftVerticalRightCapFamily m
    ((simLeftDiagram m).verticalCenterToRight
      ((simLeftVerticalCenterOriginal m).symm (simLeftVerticalCenterOriginal m q)))
  rw [(simLeftVerticalCenterOriginal m).symm_apply_apply]

abbrev SimultaneousLeftOuterPushout (m : ℕ) [NeZero m] :=
  TopologicalPushout
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
    (originalNeckToSimultaneousCapFamily m)

def simLeftColumnFirstOuterHomeomorph (m : ℕ) [NeZero m] :
    (simLeftDiagram m).columnFirst ≃ₜ SimultaneousLeftOuterPushout m :=
  topologicalPushoutCongr
    (simLeftDiagram m).verticalCenterToLeft
    (simLeftDiagram m).verticalCenterToRight
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenterToLeft
    (originalNeckToSimultaneousCapFamily m)
    (simLeftVerticalCenterOriginal m) (simLeftVerticalLeftOriginal m)
    (simLeftVerticalRightCapFamily m)
    (simLeft_uncapped_compatibility m) (simLeft_cap_compatibility m)

def zmodFiberwiseHomeomorph
    (m : ℕ) {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ZMod m → X ≃ₜ Y) :
    ZMod m × X ≃ₜ ZMod m × Y where
  toFun x := (x.1, e x.1 x.2)
  invFun y := (y.1, (e y.1).symm y.2)
  left_inv x := by
    exact Prod.ext rfl ((e x.1).symm_apply_apply x.2)
  right_inv y := by
    exact Prod.ext rfl ((e y.1).apply_symm_apply y.2)
  continuous_toFun := by
    rw [continuous_prod_of_discrete_left]
    exact fun a ↦ continuous_const.prodMk (e a).continuous
  continuous_invFun := by
    rw [continuous_prod_of_discrete_left]
    exact fun a ↦ continuous_const.prodMk (e a).symm.continuous

@[simp]
theorem zmodFiberwiseHomeomorph_apply
    (m : ℕ) {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ZMod m → X ≃ₜ Y) (x : ZMod m × X) :
    zmodFiberwiseHomeomorph m e x = (x.1, e x.1 x.2) :=
  rfl

def simLeftTopCenterHomeomorph (m : ℕ) [NeZero m] :
    SimLeftE m ≃ₜ ZMod m × CoordinateUnlinkExteriorPlanarLeftCappingGridE :=
  ((coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m).prodCongr
    (Homeomorph.refl (EuclideanClosedBall 3))).trans
      (Homeomorph.prodAssoc (ZMod m)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) (EuclideanClosedBall 3))

def simLeftTopLeftHomeomorph (m : ℕ) [NeZero m] :
    SimLeftHL m ≃ₜ ZMod m × CoordinateUnlinkExteriorPlanarLeftCappingGridHL :=
  Homeomorph.prodAssoc (ZMod m) CoordinateUnlinkExteriorPlanarBaseLeftOuterArc
    (EuclideanClosedBall 3)

def simLeftTopRightHomeomorph (m : ℕ) [NeZero m] :
    SimLeftHR m ≃ₜ ZMod m × CoordinateUnlinkExteriorPlanarLeftCappingGridHR :=
  Homeomorph.prodAssoc (ZMod m) CoordinateUnlinkExteriorPlanarNeckInterval
    (EuclideanClosedBall 3)

@[simp]
theorem simLeftTopLeftHomeomorph_apply
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftOuterArc)
    (b : EuclideanClosedBall 3) :
    simLeftTopLeftHomeomorph m (x, b) = (x.1, (x.2, b)) :=
  rfl

@[simp]
theorem simLeftTopRightHomeomorph_apply
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (b : EuclideanClosedBall 3) :
    simLeftTopRightHomeomorph m (x, b) = (x.1, (x.2, b)) :=
  rfl

def simLeftHorizontalTopCongr (m : ℕ) [NeZero m] :
    (simLeftDiagram m).horizontalTop ≃ₜ
      TopologicalPushout
        ((ContinuousMap.id (ZMod m)).prodMap
          coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft)
        ((ContinuousMap.id (ZMod m)).prodMap
          coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight) :=
  topologicalPushoutCongr
    (simLeftDiagram m).topToTopLeft (simLeftDiagram m).topToTopRight
    ((ContinuousMap.id (ZMod m)).prodMap
      coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft)
    ((ContinuousMap.id (ZMod m)).prodMap
      coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight)
    (simLeftTopCenterHomeomorph m) (simLeftTopLeftHomeomorph m)
    (simLeftTopRightHomeomorph m) (by rintro ⟨⟨a, e⟩, b⟩; rfl)
    (by rintro ⟨⟨a, e⟩, b⟩; rfl)

def simLeftFixedHorizontalTopHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    TopologicalPushout
        coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft
        coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight ≃ₜ OneHandlePiece :=
  { toEquiv :=
      (coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalTopHomeomorph m a).toEquiv
    continuous_toFun :=
      (coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalTopHomeomorph m a).continuous
    continuous_invFun :=
      (coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalTopHomeomorph m
        a).symm.continuous }

@[simp]
theorem simLeftFixedHorizontalTopHomeomorph_inl
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarLeftCappingGridHL) :
    simLeftFixedHorizontalTopHomeomorph m a
        (topologicalPushoutInl
          coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft
          coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight x) =
      coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalTopHomeomorph m a
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).topToTopLeft
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).topToTopRight x) := by
  rfl

@[simp]
theorem simLeftFixedHorizontalTopHomeomorph_inr
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarLeftCappingGridHR) :
    simLeftFixedHorizontalTopHomeomorph m a
        (topologicalPushoutInr
          coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft
          coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight x) =
      coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalTopHomeomorph m a
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).topToTopLeft
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).topToTopRight x) := by
  rfl

theorem injective_simLeftFixedTopLeft :
    Injective coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft := by
  rintro ⟨e, b⟩ ⟨e', b'⟩ h
  exact Prod.ext
    (injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
      (congrArg (fun z : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc ×
        EuclideanClosedBall 3 ↦ z.1) h))
    (congrArg (fun z : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc ×
      EuclideanClosedBall 3 ↦ z.2) h)

theorem injective_simLeftFixedTopRight :
    Injective coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight := by
  rintro ⟨e, b⟩ ⟨e', b'⟩ h
  exact Prod.ext
    (injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam
      (congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckInterval ×
        EuclideanClosedBall 3 ↦ z.1) h))
    (congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckInterval ×
      EuclideanClosedBall 3 ↦ z.2) h)

def simLeftTopProductHomeomorph (m : ℕ) [NeZero m] :
    TopologicalPushout
        ((ContinuousMap.id (ZMod m)).prodMap
          coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft)
        ((ContinuousMap.id (ZMod m)).prodMap
          coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight) ≃ₜ
      ZMod m × TopologicalPushout
        coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft
        coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight := by
  let _ : T2Space
      (TopologicalPushout
        coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft
        coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight) :=
    (simLeftFixedHorizontalTopHomeomorph m 0).symm.t2Space
  exact topologicalPushoutLeftProductHomeomorph (ZMod m)
    coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft
    coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight
    injective_simLeftFixedTopLeft injective_simLeftFixedTopRight

@[simp]
theorem simLeftTopProductHomeomorph_inl
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarLeftCappingGridHL) :
    simLeftTopProductHomeomorph m
        (topologicalPushoutInl
          ((ContinuousMap.id (ZMod m)).prodMap
            coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft)
          ((ContinuousMap.id (ZMod m)).prodMap
            coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight) (a, x)) =
      (a, topologicalPushoutInl
        coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft
        coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight x) := by
  let _ : T2Space
      (TopologicalPushout
        coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft
        coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight) :=
    (simLeftFixedHorizontalTopHomeomorph m 0).symm.t2Space
  apply topologicalPushoutLeftProductHomeomorph_inl

@[simp]
theorem simLeftTopProductHomeomorph_inr
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarLeftCappingGridHR) :
    simLeftTopProductHomeomorph m
        (topologicalPushoutInr
          ((ContinuousMap.id (ZMod m)).prodMap
            coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft)
          ((ContinuousMap.id (ZMod m)).prodMap
            coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight) (a, x)) =
      (a, topologicalPushoutInr
        coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft
        coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight x) := by
  let _ : T2Space
      (TopologicalPushout
        coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft
        coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight) :=
    (simLeftFixedHorizontalTopHomeomorph m 0).symm.t2Space
  apply topologicalPushoutLeftProductHomeomorph_inr

def simLeftHorizontalTopHomeomorph (m : ℕ) [NeZero m] :
    (simLeftDiagram m).horizontalTop ≃ₜ ZMod m × OneHandlePiece := by
  exact (simLeftHorizontalTopCongr m).trans <|
    (simLeftTopProductHomeomorph m).trans <|
        zmodFiberwiseHomeomorph m (simLeftFixedHorizontalTopHomeomorph m)

@[simp]
theorem simLeftHorizontalTopHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftOuterArc)
    (b : EuclideanClosedBall 3) :
    simLeftHorizontalTopHomeomorph m
      (topologicalPushoutInl (simLeftDiagram m).topToTopLeft
          (simLeftDiagram m).topToTopRight (x, b)) =
      (x.1, (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap x.2, b)) := by
  rw [simLeftHorizontalTopHomeomorph, Homeomorph.trans_apply,
    Homeomorph.trans_apply, simLeftHorizontalTopCongr,
    topologicalPushoutCongr_inl, simLeftTopLeftHomeomorph_apply,
    simLeftTopProductHomeomorph_inl,
    zmodFiberwiseHomeomorph_apply, simLeftFixedHorizontalTopHomeomorph_inl]
  refine Prod.ext rfl ?_
  exact coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph_inl
    m x.1 x.2 b

@[simp]
theorem simLeftHorizontalTopHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (b : EuclideanClosedBall 3) :
    simLeftHorizontalTopHomeomorph m
      (topologicalPushoutInr (simLeftDiagram m).topToTopLeft
          (simLeftDiagram m).topToTopRight (x, b)) =
      (x.1, (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m x.1 x.2, b)) := by
  rw [simLeftHorizontalTopHomeomorph, Homeomorph.trans_apply,
    Homeomorph.trans_apply, simLeftHorizontalTopCongr,
    topologicalPushoutCongr_inr, simLeftTopRightHomeomorph_apply,
    simLeftTopProductHomeomorph_inr,
    zmodFiberwiseHomeomorph_apply, simLeftFixedHorizontalTopHomeomorph_inr]
  refine Prod.ext rfl ?_
  exact coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph_inr
    m x.1 x.2 b

def simLeftMiddleCenterHomeomorph (m : ℕ) [NeZero m] :
    SimLeftC m ≃ₜ ZMod m × CoordinateUnlinkExteriorPlanarLeftCappingGridC :=
  ((coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m).prodCongr
    (Homeomorph.refl (Sphere 2))).trans
      (Homeomorph.prodAssoc (ZMod m)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) (Sphere 2))

def simLeftMiddleLeftHomeomorph (m : ℕ) [NeZero m] :
    SimLeftBL m ≃ₜ ZMod m × CoordinateUnlinkExteriorPlanarLeftCappingGridBL :=
  Homeomorph.prodAssoc (ZMod m) CoordinateUnlinkExteriorPlanarBaseLeftOuterArc (Sphere 2)

def simLeftMiddleRightHomeomorph (m : ℕ) [NeZero m] :
    SimLeftBR m ≃ₜ ZMod m × CoordinateUnlinkExteriorPlanarLeftCappingGridBR :=
  Homeomorph.prodAssoc (ZMod m) CoordinateUnlinkExteriorPlanarNeckInterval (Sphere 2)

@[simp]
theorem simLeftMiddleLeftHomeomorph_apply
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftOuterArc) (s : Sphere 2) :
    simLeftMiddleLeftHomeomorph m (x, s) = (x.1, (x.2, s)) :=
  rfl

@[simp]
theorem simLeftMiddleRightHomeomorph_apply
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    simLeftMiddleRightHomeomorph m (x, s) = (x.1, (x.2, s)) :=
  rfl

def simLeftHorizontalMiddleCongr (m : ℕ) [NeZero m] :
    (simLeftDiagram m).horizontalMiddle ≃ₜ
      TopologicalPushout
        ((ContinuousMap.id (ZMod m)).prodMap
          coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft)
        ((ContinuousMap.id (ZMod m)).prodMap
          coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight) :=
  topologicalPushoutCongr
    (simLeftDiagram m).centerToLeft (simLeftDiagram m).centerToRight
    ((ContinuousMap.id (ZMod m)).prodMap
      coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft)
    ((ContinuousMap.id (ZMod m)).prodMap
      coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight)
    (simLeftMiddleCenterHomeomorph m) (simLeftMiddleLeftHomeomorph m)
    (simLeftMiddleRightHomeomorph m) (by rintro ⟨⟨a, e⟩, s⟩; rfl)
    (by rintro ⟨⟨a, e⟩, s⟩; rfl)

def simLeftFixedHorizontalMiddleHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    TopologicalPushout
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight ≃ₜ
      OneHandleCapBoundary :=
  { toEquiv :=
      (coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph m a).toEquiv
    continuous_toFun :=
      (coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph m a).continuous
    continuous_invFun :=
      (coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph m
        a).symm.continuous }

@[simp]
theorem simLeftFixedHorizontalMiddleHomeomorph_inl
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarLeftCappingGridBL) :
    simLeftFixedHorizontalMiddleHomeomorph m a
        (topologicalPushoutInl
          coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft
          coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight x) =
      coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph m a
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToLeft
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToRight x) := by
  rfl

@[simp]
theorem simLeftFixedHorizontalMiddleHomeomorph_inr
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarLeftCappingGridBR) :
    simLeftFixedHorizontalMiddleHomeomorph m a
        (topologicalPushoutInr
          coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft
          coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight x) =
      coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph m a
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToLeft
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToRight x) := by
  rfl

theorem injective_simLeftFixedMiddleLeft :
    Injective coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft := by
  rintro ⟨e, s⟩ ⟨e', s'⟩ h
  exact Prod.ext
    (injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
      (congrArg (fun z : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc × Sphere 2 ↦
        z.1) h))
    (congrArg (fun z : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc × Sphere 2 ↦
      z.2) h)

theorem injective_simLeftFixedMiddleRight :
    Injective coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight := by
  rintro ⟨e, s⟩ ⟨e', s'⟩ h
  exact Prod.ext
    (injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam
      (congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2 ↦ z.1) h))
    (congrArg (fun z : CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2 ↦ z.2) h)

def simLeftMiddleProductHomeomorph (m : ℕ) [NeZero m] :
    TopologicalPushout
        ((ContinuousMap.id (ZMod m)).prodMap
          coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft)
        ((ContinuousMap.id (ZMod m)).prodMap
          coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight) ≃ₜ
      ZMod m × TopologicalPushout
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight := by
  let _ : T2Space
      (TopologicalPushout
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight) :=
    (simLeftFixedHorizontalMiddleHomeomorph m 0).symm.t2Space
  exact topologicalPushoutLeftProductHomeomorph (ZMod m)
    coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft
    coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight
    injective_simLeftFixedMiddleLeft injective_simLeftFixedMiddleRight

@[simp]
theorem simLeftMiddleProductHomeomorph_inl
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarLeftCappingGridBL) :
    simLeftMiddleProductHomeomorph m
        (topologicalPushoutInl
          ((ContinuousMap.id (ZMod m)).prodMap
            coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft)
          ((ContinuousMap.id (ZMod m)).prodMap
            coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight) (a, x)) =
      (a, topologicalPushoutInl
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight x) := by
  let _ : T2Space
      (TopologicalPushout
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight) :=
    (simLeftFixedHorizontalMiddleHomeomorph m 0).symm.t2Space
  apply topologicalPushoutLeftProductHomeomorph_inl

@[simp]
theorem simLeftMiddleProductHomeomorph_inr
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : CoordinateUnlinkExteriorPlanarLeftCappingGridBR) :
    simLeftMiddleProductHomeomorph m
        (topologicalPushoutInr
          ((ContinuousMap.id (ZMod m)).prodMap
            coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft)
          ((ContinuousMap.id (ZMod m)).prodMap
            coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight) (a, x)) =
      (a, topologicalPushoutInr
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight x) := by
  let _ : T2Space
      (TopologicalPushout
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight) :=
    (simLeftFixedHorizontalMiddleHomeomorph m 0).symm.t2Space
  apply topologicalPushoutLeftProductHomeomorph_inr

def simLeftHorizontalMiddleHomeomorph (m : ℕ) [NeZero m] :
    (simLeftDiagram m).horizontalMiddle ≃ₜ ZMod m × OneHandleCapBoundary := by
  exact (simLeftHorizontalMiddleCongr m).trans <|
    (simLeftMiddleProductHomeomorph m).trans <|
        zmodFiberwiseHomeomorph m (simLeftFixedHorizontalMiddleHomeomorph m)

@[simp]
theorem simLeftHorizontalMiddleHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftOuterArc)
    (s : Sphere 2) :
    simLeftHorizontalMiddleHomeomorph m
        (topologicalPushoutInl (simLeftDiagram m).centerToLeft
          (simLeftDiagram m).centerToRight (x, s)) =
      (x.1, (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap x.2, s)) := by
  rw [simLeftHorizontalMiddleHomeomorph, Homeomorph.trans_apply,
    Homeomorph.trans_apply, simLeftHorizontalMiddleCongr,
    topologicalPushoutCongr_inl, simLeftMiddleLeftHomeomorph_apply,
    simLeftMiddleProductHomeomorph_inl,
    zmodFiberwiseHomeomorph_apply,
    simLeftFixedHorizontalMiddleHomeomorph_inl,
    coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph_inl]

@[simp]
theorem simLeftHorizontalMiddleHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (s : Sphere 2) :
    simLeftHorizontalMiddleHomeomorph m
        (topologicalPushoutInr (simLeftDiagram m).centerToLeft
          (simLeftDiagram m).centerToRight (x, s)) =
      (x.1, (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m x.1 x.2, s)) := by
  rw [simLeftHorizontalMiddleHomeomorph, Homeomorph.trans_apply,
    Homeomorph.trans_apply, simLeftHorizontalMiddleCongr,
    topologicalPushoutCongr_inr, simLeftMiddleRightHomeomorph_apply,
    simLeftMiddleProductHomeomorph_inr,
    zmodFiberwiseHomeomorph_apply,
    simLeftFixedHorizontalMiddleHomeomorph_inr,
    coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph_inr]

def simLeftHorizontalBottomIdentityCongr (m : ℕ) [NeZero m] :
    (simLeftDiagram m).horizontalBottom ≃ₜ
      TopologicalPushout (simLeftDiagram m).bottomToBottomLeft
        (ContinuousMap.id (SimLeftA m)) :=
  topologicalPushoutCongr
    (simLeftDiagram m).bottomToBottomLeft (simLeftDiagram m).bottomToBottomRight
    (simLeftDiagram m).bottomToBottomLeft (ContinuousMap.id (SimLeftA m))
    (Homeomorph.refl (SimLeftA m)) (Homeomorph.refl (SimLeftFL m))
    (Homeomorph.refl (SimLeftA m)) (by intro; rfl) (by intro; rfl)

@[simp]
theorem simLeftHorizontalBottomIdentityCongr_inl
    (m : ℕ) [NeZero m] (x : SimLeftFL m) :
    simLeftHorizontalBottomIdentityCongr m
        (topologicalPushoutInl (simLeftDiagram m).bottomToBottomLeft
          (simLeftDiagram m).bottomToBottomRight x) =
      topologicalPushoutInl (simLeftDiagram m).bottomToBottomLeft
        (ContinuousMap.id (SimLeftA m)) x := by
  apply topologicalPushoutCongr_inl

@[simp]
theorem simLeftHorizontalBottomIdentityCongr_inr
    (m : ℕ) [NeZero m] (x : SimLeftA m) :
    simLeftHorizontalBottomIdentityCongr m
        (topologicalPushoutInr (simLeftDiagram m).bottomToBottomLeft
          (simLeftDiagram m).bottomToBottomRight x) =
      topologicalPushoutInr (simLeftDiagram m).bottomToBottomLeft
        (ContinuousMap.id (SimLeftA m)) x := by
  apply topologicalPushoutCongr_inr

def simLeftHorizontalBottomHomeomorph (m : ℕ) [NeZero m] :
    (simLeftDiagram m).horizontalBottom ≃ₜ
      ZMod m × CoordinateUnlinkExteriorPlanarLeftCappingGridFL :=
  (simLeftHorizontalBottomIdentityCongr m).trans <|
  (coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
    (simLeftDiagram m).bottomToBottomLeft).trans <|
      Homeomorph.prodAssoc (ZMod m) PartialSphereSpinAnnulus (Sphere 2)

@[simp]
theorem simLeftHorizontalBottomHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : ZMod m × PartialSphereSpinAnnulus) (s : Sphere 2) :
    simLeftHorizontalBottomHomeomorph m
        (topologicalPushoutInl (simLeftDiagram m).bottomToBottomLeft
          (simLeftDiagram m).bottomToBottomRight (x, s)) =
      (x.1, (x.2, s)) := by
  rw [simLeftHorizontalBottomHomeomorph, Homeomorph.trans_apply,
    simLeftHorizontalBottomIdentityCongr_inl, Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph_inl]
  rfl

@[simp]
theorem simLeftHorizontalBottomHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    simLeftHorizontalBottomHomeomorph m
        (topologicalPushoutInr (simLeftDiagram m).bottomToBottomLeft
          (simLeftDiagram m).bottomToBottomRight (x, s)) =
      (x.1, (partialSphereSpinAnnulusOne
        (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m x.1 x.2), s)) := by
  rw [simLeftHorizontalBottomHomeomorph, Homeomorph.trans_apply,
    simLeftHorizontalBottomIdentityCongr_inr, Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph_inr]
  change ((coordinateUnlinkExteriorPlanarNormalizedLeftSeam m x).1,
      ((coordinateUnlinkExteriorPlanarNormalizedLeftSeam m x).2, s)) = _
  apply Prod.ext
  · exact coordinateUnlinkExteriorPlanarNormalizedLeftSeam_fst m x
  · apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact coordinateUnlinkExteriorPlanarNormalizedLeftSeam_time m x
    · rfl

def simLeftLabelledOneHandleBoundaryInclusion (m : ℕ) :
    C(ZMod m × OneHandleCapBoundary, ZMod m × OneHandlePiece) :=
  (ContinuousMap.id (ZMod m)).prodMap oneHandleBoundaryInclusion

def simLeftLabelledAnnulusBoundaryInclusion (m : ℕ) :
    C(ZMod m × OneHandleCapBoundary,
      ZMod m × (PartialSphereSpinAnnulus × Sphere 2)) :=
  (ContinuousMap.id (ZMod m)).prodMap
    (partialSphereSpinBoundaryInclusion partialSphereSpinAnnulusOne)

@[simp]
theorem simLeftLabelledOneHandleBoundaryInclusion_apply
    (m : ℕ) (x : ZMod m × OneHandleCapBoundary) :
    simLeftLabelledOneHandleBoundaryInclusion m x =
      (x.1, oneHandleBoundaryInclusion x.2) :=
  rfl

@[simp]
theorem simLeftLabelledAnnulusBoundaryInclusion_apply
    (m : ℕ) (x : ZMod m × OneHandleCapBoundary) :
    simLeftLabelledAnnulusBoundaryInclusion m x =
      (x.1, partialSphereSpinBoundaryInclusion partialSphereSpinAnnulusOne x.2) :=
  rfl

theorem simLeftHorizontalTopCompatibility
    (m : ℕ) [NeZero m]
    (z : (simLeftDiagram m).horizontalMiddle) :
    simLeftHorizontalTopHomeomorph m
        ((simLeftDiagram m).horizontalMiddleToTop z) =
      simLeftLabelledOneHandleBoundaryInclusion m
        (simLeftHorizontalMiddleHomeomorph m z) := by
  rcases topologicalPushout_jointly_surjective
      (simLeftDiagram m).centerToLeft (simLeftDiagram m).centerToRight z with
    ⟨⟨x, s⟩, rfl⟩ | ⟨⟨x, s⟩, rfl⟩
  · rw [TopologicalPushoutGridDiagram.horizontalMiddleToTop_inl,
      simLeftHorizontalTopHomeomorph_inl,
      simLeftHorizontalMiddleHomeomorph_inl,
      simLeftLabelledOneHandleBoundaryInclusion_apply,
      oneHandleBoundaryInclusion_apply]
    rfl
  · rw [TopologicalPushoutGridDiagram.horizontalMiddleToTop_inr,
      simLeftHorizontalTopHomeomorph_inr,
      simLeftHorizontalMiddleHomeomorph_inr,
      simLeftLabelledOneHandleBoundaryInclusion_apply,
      oneHandleBoundaryInclusion_apply]
    rfl

theorem simLeftHorizontalBottomCompatibility
    (m : ℕ) [NeZero m]
    (z : (simLeftDiagram m).horizontalMiddle) :
    simLeftHorizontalBottomHomeomorph m
        ((simLeftDiagram m).horizontalMiddleToBottom z) =
      simLeftLabelledAnnulusBoundaryInclusion m
        (simLeftHorizontalMiddleHomeomorph m z) := by
  rcases topologicalPushout_jointly_surjective
      (simLeftDiagram m).centerToLeft (simLeftDiagram m).centerToRight z with
    ⟨⟨x, s⟩, rfl⟩ | ⟨⟨x, s⟩, rfl⟩
  · rw [TopologicalPushoutGridDiagram.horizontalMiddleToBottom_inl,
      simLeftHorizontalBottomHomeomorph_inl,
      simLeftHorizontalMiddleHomeomorph_inl,
      simLeftLabelledAnnulusBoundaryInclusion_apply,
      partialSphereSpinBoundaryInclusion_apply]
    rfl
  · rw [TopologicalPushoutGridDiagram.horizontalMiddleToBottom_inr,
      simLeftHorizontalBottomHomeomorph_inr,
      simLeftHorizontalMiddleHomeomorph_inr,
      simLeftLabelledAnnulusBoundaryInclusion_apply,
      partialSphereSpinBoundaryInclusion_apply]
    change (x.1, (partialSphereSpinAnnulusOne
      (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m x.1 x.2), s)) = _
    rfl

def simLeftRowHomeomorph (m : ℕ) [NeZero m] :
    (simLeftDiagram m).rowFirst ≃ₜ
      TopologicalPushout (simLeftLabelledOneHandleBoundaryInclusion m)
        (simLeftLabelledAnnulusBoundaryInclusion m) :=
  topologicalPushoutCongr
    (simLeftDiagram m).horizontalMiddleToTop
    (simLeftDiagram m).horizontalMiddleToBottom
    (simLeftLabelledOneHandleBoundaryInclusion m)
    (simLeftLabelledAnnulusBoundaryInclusion m)
    (simLeftHorizontalMiddleHomeomorph m)
    (simLeftHorizontalTopHomeomorph m)
    (simLeftHorizontalBottomHomeomorph m)
    (simLeftHorizontalTopCompatibility m)
    (simLeftHorizontalBottomCompatibility m)

@[simp]
theorem simLeftRowHomeomorph_inl
    (m : ℕ) [NeZero m] (x : (simLeftDiagram m).horizontalTop) :
    simLeftRowHomeomorph m
        (topologicalPushoutInl (simLeftDiagram m).horizontalMiddleToTop
          (simLeftDiagram m).horizontalMiddleToBottom x) =
      topologicalPushoutInl (simLeftLabelledOneHandleBoundaryInclusion m)
        (simLeftLabelledAnnulusBoundaryInclusion m)
        (simLeftHorizontalTopHomeomorph m x) := by
  apply topologicalPushoutCongr_inl

@[simp]
theorem simLeftRowHomeomorph_inr
    (m : ℕ) [NeZero m] (x : (simLeftDiagram m).horizontalBottom) :
    simLeftRowHomeomorph m
        (topologicalPushoutInr (simLeftDiagram m).horizontalMiddleToTop
          (simLeftDiagram m).horizontalMiddleToBottom x) =
      topologicalPushoutInr (simLeftLabelledOneHandleBoundaryInclusion m)
        (simLeftLabelledAnnulusBoundaryInclusion m)
        (simLeftHorizontalBottomHomeomorph m x) := by
  apply topologicalPushoutCongr_inr

theorem injective_partialSphereSpinBoundaryInclusion_annulusOne :
    Injective (partialSphereSpinBoundaryInclusion partialSphereSpinAnnulusOne) := by
  rintro ⟨u, s⟩ ⟨v, t⟩ h
  apply Prod.ext
  · exact congrArg (fun z : PartialSphereSpinAnnulus × Sphere 2 ↦ z.1.1) h
  · exact congrArg (fun z : PartialSphereSpinAnnulus × Sphere 2 ↦ z.2) h

def simLeftRowProductHomeomorph (m : ℕ) [NeZero m] :
    TopologicalPushout (simLeftLabelledOneHandleBoundaryInclusion m)
        (simLeftLabelledAnnulusBoundaryInclusion m) ≃ₜ
      ZMod m × PartialSphereSpin partialSphereSpinAnnulusOne := by
  let _ : T2Space (PartialSphereSpin partialSphereSpinAnnulusOne) :=
    partialSphereSpinAnnulusOneHomeomorphOneHandle.symm.t2Space
  exact topologicalPushoutLeftProductHomeomorph (ZMod m)
    oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion partialSphereSpinAnnulusOne)
    oneHandleBoundaryInclusion_injective
    injective_partialSphereSpinBoundaryInclusion_annulusOne

@[simp]
theorem simLeftRowProductHomeomorph_inl
    (m : ℕ) [NeZero m] (a : ZMod m) (x : OneHandlePiece) :
    simLeftRowProductHomeomorph m
        (topologicalPushoutInl (simLeftLabelledOneHandleBoundaryInclusion m)
          (simLeftLabelledAnnulusBoundaryInclusion m) (a, x)) =
      (a, partialSphereSpinInl partialSphereSpinAnnulusOne x) := by
  let _ : T2Space (PartialSphereSpin partialSphereSpinAnnulusOne) :=
    partialSphereSpinAnnulusOneHomeomorphOneHandle.symm.t2Space
  apply topologicalPushoutLeftProductHomeomorph_inl

@[simp]
theorem simLeftRowProductHomeomorph_inr
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : PartialSphereSpinAnnulus × Sphere 2) :
    simLeftRowProductHomeomorph m
        (topologicalPushoutInr (simLeftLabelledOneHandleBoundaryInclusion m)
          (simLeftLabelledAnnulusBoundaryInclusion m) (a, x)) =
      (a, partialSphereSpinInr partialSphereSpinAnnulusOne x) := by
  let _ : T2Space (PartialSphereSpin partialSphereSpinAnnulusOne) :=
    partialSphereSpinAnnulusOneHomeomorphOneHandle.symm.t2Space
  apply topologicalPushoutLeftProductHomeomorph_inr

def simLeftCappedHomeomorph (m : ℕ) [NeZero m] :
    (simLeftDiagram m).columnFirst ≃ₜ ZMod m × OneHandlePiece :=
  (simLeftDiagram m).topologicalPushoutGridHomeomorph.symm |>.trans
    ((simLeftRowHomeomorph m).trans <|
      (simLeftRowProductHomeomorph m).trans <|
        (Homeomorph.refl (ZMod m)).prodCongr
          partialSphereSpinAnnulusOneHomeomorphOneHandle)

@[simp]
theorem simLeftCappedHomeomorph_topLeft
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftOuterArc)
    (b : EuclideanClosedBall 3) :
    simLeftCappedHomeomorph m
        ((simLeftDiagram m).columnFirstTopLeft (x, b)) =
      (x.1, partialSphereSpinAnnulusOneHandleMap
        (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap x.2, b)) := by
  rw [simLeftCappedHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply,
    Homeomorph.trans_apply,
    (simLeftDiagram m).topologicalPushoutGridHomeomorph_symm_apply_topLeft]
  change ((Homeomorph.refl (ZMod m)).prodCongr
      partialSphereSpinAnnulusOneHomeomorphOneHandle)
    (simLeftRowProductHomeomorph m
      (simLeftRowHomeomorph m
        (topologicalPushoutInl
          (simLeftDiagram m).horizontalMiddleToTop
          (simLeftDiagram m).horizontalMiddleToBottom
          (topologicalPushoutInl
            (simLeftDiagram m).topToTopLeft
            (simLeftDiagram m).topToTopRight (x, b))))) = _
  rw [simLeftRowHomeomorph_inl, simLeftHorizontalTopHomeomorph_inl,
    simLeftRowProductHomeomorph_inl]
  refine Prod.ext rfl ?_
  exact partialSphereSpinAnnulusOneHomeomorphOneHandle_inl _

@[simp]
theorem simLeftCappedHomeomorph_topRight
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (b : EuclideanClosedBall 3) :
    simLeftCappedHomeomorph m
        ((simLeftDiagram m).columnFirstTopRight (x, b)) =
      (x.1, partialSphereSpinAnnulusOneHandleMap
        (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m x.1 x.2, b)) := by
  rw [simLeftCappedHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply,
    Homeomorph.trans_apply,
    (simLeftDiagram m).topologicalPushoutGridHomeomorph_symm_apply_topRight]
  change ((Homeomorph.refl (ZMod m)).prodCongr
      partialSphereSpinAnnulusOneHomeomorphOneHandle)
    (simLeftRowProductHomeomorph m
      (simLeftRowHomeomorph m
        (topologicalPushoutInl
          (simLeftDiagram m).horizontalMiddleToTop
          (simLeftDiagram m).horizontalMiddleToBottom
          (topologicalPushoutInr
            (simLeftDiagram m).topToTopLeft
            (simLeftDiagram m).topToTopRight (x, b))))) = _
  rw [simLeftRowHomeomorph_inl, simLeftHorizontalTopHomeomorph_inr,
    simLeftRowProductHomeomorph_inl]
  refine Prod.ext rfl ?_
  exact partialSphereSpinAnnulusOneHomeomorphOneHandle_inl _

@[simp]
theorem simLeftCappedHomeomorph_bottomLeft
    (m : ℕ) [NeZero m]
    (x : ZMod m × PartialSphereSpinAnnulus) (s : Sphere 2) :
    simLeftCappedHomeomorph m
        ((simLeftDiagram m).columnFirstBottomLeft (x, s)) =
      (x.1, partialSphereSpinAnnulusShellMap
        (partialSphereSpinAnnulusReverseHomeomorph x.2, s)) := by
  rw [simLeftCappedHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply,
    Homeomorph.trans_apply,
    (simLeftDiagram m).topologicalPushoutGridHomeomorph_symm_apply_bottomLeft]
  change ((Homeomorph.refl (ZMod m)).prodCongr
      partialSphereSpinAnnulusOneHomeomorphOneHandle)
    (simLeftRowProductHomeomorph m
      (simLeftRowHomeomorph m
        (topologicalPushoutInr
          (simLeftDiagram m).horizontalMiddleToTop
          (simLeftDiagram m).horizontalMiddleToBottom
          (topologicalPushoutInl
            (simLeftDiagram m).bottomToBottomLeft
            (simLeftDiagram m).bottomToBottomRight (x, s))))) = _
  rw [simLeftRowHomeomorph_inr, simLeftHorizontalBottomHomeomorph_inl,
    simLeftRowProductHomeomorph_inr]
  refine Prod.ext rfl ?_
  exact partialSphereSpinAnnulusOneHomeomorphOneHandle_inr _

@[simp]
theorem simLeftCappedHomeomorph_bottomRight
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    simLeftCappedHomeomorph m
        ((simLeftDiagram m).columnFirstBottomRight (x, s)) =
      (x.1, partialSphereSpinAnnulusShellMap
        (partialSphereSpinAnnulusReverseHomeomorph
          (partialSphereSpinAnnulusOne
            (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m x.1 x.2)), s)) := by
  rw [simLeftCappedHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply,
    Homeomorph.trans_apply,
    (simLeftDiagram m).topologicalPushoutGridHomeomorph_symm_apply_bottomRight]
  change ((Homeomorph.refl (ZMod m)).prodCongr
      partialSphereSpinAnnulusOneHomeomorphOneHandle)
    (simLeftRowProductHomeomorph m
      (simLeftRowHomeomorph m
        (topologicalPushoutInr
          (simLeftDiagram m).horizontalMiddleToTop
          (simLeftDiagram m).horizontalMiddleToBottom
          (topologicalPushoutInr
            (simLeftDiagram m).bottomToBottomLeft
            (simLeftDiagram m).bottomToBottomRight (x, s))))) = _
  rw [simLeftRowHomeomorph_inr, simLeftHorizontalBottomHomeomorph_inr,
    simLeftRowProductHomeomorph_inr]
  refine Prod.ext rfl ?_
  exact partialSphereSpinAnnulusOneHomeomorphOneHandle_inr _

/-! ## Public simultaneous-family interface -/

/-- The simultaneous left-family capping grid.  Its left and center columns are the
corresponding columns of the original neck grid; its right column is the labelled cap family. -/
abbrev coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
    (m : ℕ) [NeZero m] :=
  simLeftDiagram m

/-- The uncapped side of the simultaneous left-family attachment. -/
abbrev CoordinateUnlinkExteriorPlanarNeckLeftFamilyUncapped
    (m : ℕ) [NeZero m] :=
  (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram m).verticalLeft

/-- The common labelled neck boundary of the simultaneous left-family attachment. -/
abbrev CoordinateUnlinkExteriorPlanarNeckLeftFamilyBoundary
    (m : ℕ) [NeZero m] :=
  (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram m).verticalCenter

/-- The simultaneous family of interval-product four-ball caps. -/
abbrev CoordinateUnlinkExteriorPlanarNeckLeftFamilyCaps
    (m : ℕ) [NeZero m] :=
  (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram m).verticalRight

/-- The column-first pushout obtained by attaching every labelled left cap. -/
abbrev CoordinateUnlinkExteriorPlanarNeckLeftFamilyCapped
    (m : ℕ) [NeZero m] :=
  (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram m).columnFirst

/-- The common boundary column is exactly the original grid's central column. -/
def coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryHomeomorphOriginal
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckLeftFamilyBoundary m ≃ₜ
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenter :=
  simLeftVerticalCenterOriginal m

/-- The uncapped column is exactly the original grid's left column. -/
def coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckLeftFamilyUncapped m ≃ₜ
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalLeft :=
  simLeftVerticalLeftOriginal m

/-- The labelled cap family is the literal product of the label set and ProductFourBall. -/
def coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsHomeomorphProductFourBall
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckLeftFamilyCaps m ≃ₜ
      ZMod m × ProductFourBall :=
  simLeftCapFamilyHomeomorph m

/-- The labelled standard boundary inclusion for the cap family. -/
abbrev coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryInclusion
    (m : ℕ) :
    C(ZMod m × Sphere 3, ZMod m × ProductFourBall) :=
  labelledProductFourSphereBoundaryInclusion m

/-- In the exact central-column and cap-family coordinates, the attaching map is the labelled
standard inclusion of Sphere 3 in ProductFourBall. -/
theorem coordinateUnlinkExteriorPlanarNeckLeftFamily_boundary
    (m : ℕ) [NeZero m]
    (q : CoordinateUnlinkExteriorPlanarNeckLeftFamilyBoundary m) :
    coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsHomeomorphProductFourBall m
        ((coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
          m).verticalCenterToRight q) =
      coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryInclusion m
        (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m
          (coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryHomeomorphOriginal m q)) :=
  capFamily_boundary_compatibility m q

/-- Simultaneously capping every labelled left neck gives one copy of the point-set
one-handle for every label. -/
def coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckLeftFamilyCapped m ≃ₜ
      ZMod m × OneHandlePiece :=
  simLeftCappedHomeomorph m

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle_topLeft
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftOuterArc)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m
        ((coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
          m).columnFirstTopLeft (x, b)) =
      (x.1, partialSphereSpinAnnulusOneHandleMap
        (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap x.2, b)) :=
  simLeftCappedHomeomorph_topLeft m x b

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle_topRight
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m
        ((coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
          m).columnFirstTopRight (x, b)) =
      (x.1, partialSphereSpinAnnulusOneHandleMap
        (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m x.1 x.2, b)) :=
  simLeftCappedHomeomorph_topRight m x b

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle_bottomLeft
    (m : ℕ) [NeZero m]
    (x : ZMod m × PartialSphereSpinAnnulus) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m
        ((coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
          m).columnFirstBottomLeft (x, s)) =
      (x.1, partialSphereSpinAnnulusShellMap
        (partialSphereSpinAnnulusReverseHomeomorph x.2, s)) :=
  simLeftCappedHomeomorph_bottomLeft m x s

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle_bottomRight
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m
        ((coordinateUnlinkExteriorPlanarNeckLeftFamilyCappingGridDiagram
          m).columnFirstBottomRight (x, s)) =
      (x.1, partialSphereSpinAnnulusShellMap
        (partialSphereSpinAnnulusReverseHomeomorph
          (partialSphereSpinAnnulusOne
            (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m x.1 x.2)), s)) :=
  simLeftCappedHomeomorph_bottomRight m x s


end SplittingSpheres
