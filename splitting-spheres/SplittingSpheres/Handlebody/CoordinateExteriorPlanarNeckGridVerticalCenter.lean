/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutComm
public import SplittingSpheres.Foundations.TopologicalPushoutLeftProduct
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckGridRecognition

/-!
# The central vertical pushout of the planar neck grid

The central column of the neck grid glues the labelled seam cylinders to their two endpoint
three-balls.  Relabelling each endpoint by the incident seam turns this into the product of
`ZMod m` with the standard two-face pushout for the boundary of `D¹ × B³`.  Consequently the
central vertical pushout is homeomorphic to `ZMod m × Sphere 3`.

This is an exact point-set identification.  The canonical endpoint offset remains unevaluated;
no cyclic-order, capping, separation, or smoothness statement is made.
-/

@[expose] public section

noncomputable section

open Function Metric Topology

namespace SplittingSpheres

/-! ## Normalizing the three objects of the central span -/

/-- Relabel the common endpoints by their incident seam and reassociate the product. -/
def coordinateUnlinkExteriorPlanarNeckGridVerticalCenterCornerHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckGridC m ≃ₜ ZMod m × ProductFourCorner :=
  ((coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m).prodCongr
    (Homeomorph.refl (Sphere 2))).trans <|
      Homeomorph.prodAssoc (ZMod m)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) (Sphere 2)

/-- Relabel the endpoint-ball family by its incident seam and reassociate the product. -/
def coordinateUnlinkExteriorPlanarNeckGridVerticalCenterEndHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckGridE m ≃ₜ ZMod m × ProductFourEndPiece :=
  ((coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m).prodCongr
    (Homeomorph.refl (EuclideanClosedBall 3))).trans <|
      Homeomorph.prodAssoc (ZMod m)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) (EuclideanClosedBall 3)

/-- Convert the seam interval to the literal one-ball used by `ProductFourSidePiece`, then
reassociate the product. -/
def coordinateUnlinkExteriorPlanarNeckGridVerticalCenterSideHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckGridA m ≃ₜ ZMod m × ProductFourSidePiece :=
  (((Homeomorph.refl (ZMod m)).prodCongr
      euclideanClosedBallOneHomeomorphUnitInterval.symm).prodCongr
        (Homeomorph.refl (Sphere 2))).trans <|
    Homeomorph.prodAssoc (ZMod m) (EuclideanClosedBall 1) (Sphere 2)

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridVerticalCenterCornerHomeomorph_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridC m) :
    coordinateUnlinkExteriorPlanarNeckGridVerticalCenterCornerHomeomorph m x =
      ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x.1).1,
        (x.1.2, x.2)) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridVerticalCenterEndHomeomorph_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridE m) :
    coordinateUnlinkExteriorPlanarNeckGridVerticalCenterEndHomeomorph m x =
      ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x.1).1,
        (x.1.2, x.2)) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridVerticalCenterSideHomeomorph_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridA m) :
    coordinateUnlinkExteriorPlanarNeckGridVerticalCenterSideHomeomorph m x =
      (x.1.1, (euclideanClosedBallOneHomeomorphUnitInterval.symm x.1.2, x.2)) :=
  rfl

/-! ## Congruence with the labelled product-four boundary span -/

/-- Normalize the central vertical span.  The original top piece becomes the end face, while
the original bottom piece becomes the side face. -/
def coordinateUnlinkExteriorPlanarNeckGridVerticalCenterCongr
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenter ≃ₜ
      TopologicalPushout
        ((ContinuousMap.id (ZMod m)).prodMap productFourCornerToEnd)
        ((ContinuousMap.id (ZMod m)).prodMap productFourCornerToSide) :=
  topologicalPushoutCongr
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToTop
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToBottom
    ((ContinuousMap.id (ZMod m)).prodMap productFourCornerToEnd)
    ((ContinuousMap.id (ZMod m)).prodMap productFourCornerToSide)
    (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterCornerHomeomorph m)
    (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterEndHomeomorph m)
    (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterSideHomeomorph m)
    (by
      rintro ⟨⟨a, e⟩, s⟩
      rfl)
    (by
      rintro ⟨⟨a, e⟩, s⟩
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact euclideanClosedBallOneHomeomorphUnitInterval.symm_apply_apply
            ⟨e.1, sphere_subset_closedBall e.2⟩
        · rfl)

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridVerticalCenterCongr_inl
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridE m) :
    coordinateUnlinkExteriorPlanarNeckGridVerticalCenterCongr m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToTop
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToBottom x) =
      topologicalPushoutInl
        ((ContinuousMap.id (ZMod m)).prodMap productFourCornerToEnd)
        ((ContinuousMap.id (ZMod m)).prodMap productFourCornerToSide)
        (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterEndHomeomorph m x) := by
  apply topologicalPushoutCongr_inl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridVerticalCenterCongr_inr
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridA m) :
    coordinateUnlinkExteriorPlanarNeckGridVerticalCenterCongr m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToTop
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToBottom x) =
      topologicalPushoutInr
        ((ContinuousMap.id (ZMod m)).prodMap productFourCornerToEnd)
        ((ContinuousMap.id (ZMod m)).prodMap productFourCornerToSide)
        (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterSideHomeomorph m x) := by
  apply topologicalPushoutCongr_inr

/-! ## Recognition as the labelled family of three-spheres -/

/-- The central vertical pushout is exactly the labelled family `ZMod m × Sphere 3`. -/
def coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenter ≃ₜ
      ZMod m × Sphere 3 := by
  let _ : T2Space ProductFourBoundaryPushout :=
    productFourBoundaryPushoutHomeomorphSphere.symm.t2Space
  exact
    (coordinateUnlinkExteriorPlanarNeckGridVerticalCenterCongr m).trans <|
      (topologicalPushoutComm
        ((ContinuousMap.id (ZMod m)).prodMap productFourCornerToEnd)
        ((ContinuousMap.id (ZMod m)).prodMap productFourCornerToSide)).trans <|
        (topologicalPushoutLeftProductHomeomorph (ZMod m)
          productFourCornerToSide productFourCornerToEnd
          injective_productFourCornerToSide injective_productFourCornerToEnd).trans <|
          (Homeomorph.refl (ZMod m)).prodCongr
            productFourBoundaryPushoutHomeomorphSphere

/-- Exact action on the endpoint-ball (`E`, or top) coprojection. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_inl
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridE m) :
    coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToTop
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToBottom x) =
      ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x.1).1,
        productFourBoundaryPushoutHomeomorphSphere
          (topologicalPushoutInr productFourCornerToSide productFourCornerToEnd
            (x.1.2, x.2))) := by
  rw [coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph,
    Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarNeckGridVerticalCenterCongr_inl,
    topologicalPushoutComm_inl,
    topologicalPushoutLeftProductHomeomorph_inr]
  rfl

/-- Exact action on the seam-cylinder (`A`, or bottom) coprojection. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph_inr
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridA m) :
    coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToTop
          (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToBottom x) =
      (x.1.1,
        productFourBoundaryPushoutHomeomorphSphere
          (topologicalPushoutInl productFourCornerToSide productFourCornerToEnd
            (euclideanClosedBallOneHomeomorphUnitInterval.symm x.1.2, x.2))) := by
  rw [coordinateUnlinkExteriorPlanarNeckGridVerticalCenterHomeomorph,
    Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarNeckGridVerticalCenterCongr_inr,
    topologicalPushoutComm_inr,
    topologicalPushoutLeftProductHomeomorph_inl]
  rfl

end SplittingSpheres
