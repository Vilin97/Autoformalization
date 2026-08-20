/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutGrid
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarRightNodeBoundary

/-!
# The concrete neck-cut pushout grid

This file packages the nine spaces and twelve maps which simultaneously record the cut of the
normalized planar flower along its lifted seams and the cut of the retained one-handle along the
corresponding endpoint three-balls.  The common endpoint labels are the right-sector labels, so
the map to the seam family retains the canonical upper-endpoint twist.

Only the commuting `3 × 3` diagram is constructed here.  No recognition of either iterated
pushout, separation statement, manifold gluing, or connected-sum conclusion is asserted.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped Topology

namespace SplittingSpheres

/-! ## The nine objects -/

/-- Common endpoint labels: a right-sector label and one of its two ends. -/
abbrev CoordinateUnlinkExteriorPlanarNeckGridEndpoint (m : ℕ) : Type :=
  CoordinateUnlinkExteriorPlanarRightNodeEndpoint m

/-- The complete labelled normalized seam family. -/
abbrev CoordinateUnlinkExteriorPlanarNeckGridSeam (m : ℕ) : Type :=
  ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval

/-- The labelled retained outer arcs on the left normalized annuli. -/
abbrev CoordinateUnlinkExteriorPlanarNeckGridLeftOuter (m : ℕ) : Type :=
  ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftOuterArc

/-- The labelled retained right-sector intervals. -/
abbrev CoordinateUnlinkExteriorPlanarNeckGridRightOuter (m : ℕ) : Type :=
  ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval

/-- The central corner `K × S²`. -/
abbrev CoordinateUnlinkExteriorPlanarNeckGridC (m : ℕ) : Type :=
  CoordinateUnlinkExteriorPlanarNeckGridEndpoint m × Sphere 2

/-- The top central endpoint-ball family `K × B³`. -/
abbrev CoordinateUnlinkExteriorPlanarNeckGridE (m : ℕ) : Type :=
  CoordinateUnlinkExteriorPlanarNeckGridEndpoint m × EuclideanClosedBall 3

/-- The bottom central spun seam family. -/
abbrev CoordinateUnlinkExteriorPlanarNeckGridA (m : ℕ) : Type :=
  CoordinateUnlinkExteriorPlanarNeckGridSeam m × Sphere 2

/-- The middle-left retained-outer boundary family. -/
abbrev CoordinateUnlinkExteriorPlanarNeckGridBL (m : ℕ) : Type :=
  CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m × Sphere 2

/-- The middle-right retained-sector boundary family. -/
abbrev CoordinateUnlinkExteriorPlanarNeckGridBR (m : ℕ) : Type :=
  CoordinateUnlinkExteriorPlanarNeckGridRightOuter m × Sphere 2

/-- The top-left one-handle sector family. -/
abbrev CoordinateUnlinkExteriorPlanarNeckGridHL (m : ℕ) : Type :=
  CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m × EuclideanClosedBall 3

/-- The top-right one-handle sector family. -/
abbrev CoordinateUnlinkExteriorPlanarNeckGridHR (m : ℕ) : Type :=
  CoordinateUnlinkExteriorPlanarNeckGridRightOuter m × EuclideanClosedBall 3

/-- The bottom-left normalized left annuli crossed with `S²`. -/
abbrev CoordinateUnlinkExteriorPlanarNeckGridFL (m : ℕ) : Type :=
  CoordinateUnlinkExteriorPlanarNormalizedLeftHalf m × Sphere 2

/-- The bottom-right normalized right annulus crossed with `S²`. -/
abbrev CoordinateUnlinkExteriorPlanarNeckGridFR : Type :=
  CoordinateUnlinkExteriorPlanarNormalizedRightHalf × Sphere 2

/-! ## Four elementary maps -/

/-- The literal inclusion `S² → B³`. -/
def coordinateUnlinkExteriorPlanarNeckGridSphereToBall :
    C(Sphere 2, EuclideanClosedBall 3) where
  toFun s := ⟨s.1, sphere_subset_closedBall s.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridSphereToBall_apply (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckGridSphereToBall s =
      ⟨s.1, sphere_subset_closedBall s.2⟩ :=
  rfl

/-- Send a right-sector-labelled endpoint to the adjacent left outer arc.  Its label is first
transported through the possibly twisted endpoint-to-seam map. -/
def coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridEndpoint m,
      CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m) where
  toFun x :=
    ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x).1,
      coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc x.2)
  continuous_toFun :=
    ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m).continuous.fst).prodMk <|
      coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc.continuous.comp continuous_snd

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter_apply
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridEndpoint m) :
    coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m x =
      ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x).1,
        coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc x.2) :=
  rfl

/-- Include every labelled left retained arc in the `t = 1` boundary of its normalized left
annulus. -/
def coordinateUnlinkExteriorPlanarNeckGridLeftOuterToNormalizedLeft
    (m : ℕ) :
    C(CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m,
      CoordinateUnlinkExteriorPlanarNormalizedLeftHalf m) where
  toFun x :=
    (x.1, partialSphereSpinAnnulusOne
      (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap x.2))
  continuous_toFun := continuous_fst.prodMk <|
    partialSphereSpinAnnulusOne.continuous.comp <|
      coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap.continuous.comp continuous_snd

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridLeftOuterToNormalizedLeft_apply
    (m : ℕ) (x : CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m) :
    coordinateUnlinkExteriorPlanarNeckGridLeftOuterToNormalizedLeft m x =
      (x.1, partialSphereSpinAnnulusOne
        (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap x.2)) :=
  rfl

/-- Include every labelled retained right sector in the `t = 1` boundary of the normalized
right annulus. -/
def coordinateUnlinkExteriorPlanarNeckGridRightOuterToNormalizedRight
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridRightOuter m,
      CoordinateUnlinkExteriorPlanarNormalizedRightHalf) where
  toFun x := partialSphereSpinAnnulusOne
    (coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m x)
  continuous_toFun := partialSphereSpinAnnulusOne.continuous.comp
    (coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m).continuous

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridRightOuterToNormalizedRight_apply
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckGridRightOuter m) :
    coordinateUnlinkExteriorPlanarNeckGridRightOuterToNormalizedRight m x =
      partialSphereSpinAnnulusOne
        (coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m x) :=
  rfl

/-! ## The twelve grid arrows -/

def coordinateUnlinkExteriorPlanarNeckGridCenterToTop
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridC m,
      CoordinateUnlinkExteriorPlanarNeckGridE m) :=
  (ContinuousMap.id (CoordinateUnlinkExteriorPlanarNeckGridEndpoint m)).prodMap
    coordinateUnlinkExteriorPlanarNeckGridSphereToBall

def coordinateUnlinkExteriorPlanarNeckGridCenterToBottom
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridC m,
      CoordinateUnlinkExteriorPlanarNeckGridA m) :=
  (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m).prodMap
    (ContinuousMap.id (Sphere 2))

def coordinateUnlinkExteriorPlanarNeckGridCenterToLeft
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridC m,
      CoordinateUnlinkExteriorPlanarNeckGridBL m) :=
  (coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m).prodMap
    (ContinuousMap.id (Sphere 2))

def coordinateUnlinkExteriorPlanarNeckGridCenterToRight
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridC m,
      CoordinateUnlinkExteriorPlanarNeckGridBR m) :=
  (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
    (ContinuousMap.id (Sphere 2))

def coordinateUnlinkExteriorPlanarNeckGridTopToTopLeft
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridE m,
      CoordinateUnlinkExteriorPlanarNeckGridHL m) :=
  (coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m).prodMap
    (ContinuousMap.id (EuclideanClosedBall 3))

def coordinateUnlinkExteriorPlanarNeckGridTopToTopRight
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridE m,
      CoordinateUnlinkExteriorPlanarNeckGridHR m) :=
  (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
    (ContinuousMap.id (EuclideanClosedBall 3))

def coordinateUnlinkExteriorPlanarNeckGridBottomToBottomLeft
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridA m,
      CoordinateUnlinkExteriorPlanarNeckGridFL m) :=
  (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m).prodMap
    (ContinuousMap.id (Sphere 2))

def coordinateUnlinkExteriorPlanarNeckGridBottomToBottomRight
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridA m,
      CoordinateUnlinkExteriorPlanarNeckGridFR) :=
  (coordinateUnlinkExteriorPlanarNormalizedRightSeam m).prodMap
    (ContinuousMap.id (Sphere 2))

def coordinateUnlinkExteriorPlanarNeckGridLeftToTopLeft
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridBL m,
      CoordinateUnlinkExteriorPlanarNeckGridHL m) :=
  (ContinuousMap.id (CoordinateUnlinkExteriorPlanarNeckGridLeftOuter m)).prodMap
    coordinateUnlinkExteriorPlanarNeckGridSphereToBall

def coordinateUnlinkExteriorPlanarNeckGridLeftToBottomLeft
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridBL m,
      CoordinateUnlinkExteriorPlanarNeckGridFL m) :=
  (coordinateUnlinkExteriorPlanarNeckGridLeftOuterToNormalizedLeft m).prodMap
    (ContinuousMap.id (Sphere 2))

def coordinateUnlinkExteriorPlanarNeckGridRightToTopRight
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridBR m,
      CoordinateUnlinkExteriorPlanarNeckGridHR m) :=
  (ContinuousMap.id (CoordinateUnlinkExteriorPlanarNeckGridRightOuter m)).prodMap
    coordinateUnlinkExteriorPlanarNeckGridSphereToBall

def coordinateUnlinkExteriorPlanarNeckGridRightToBottomRight
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarNeckGridBR m,
      CoordinateUnlinkExteriorPlanarNeckGridFR) :=
  (coordinateUnlinkExteriorPlanarNeckGridRightOuterToNormalizedRight m).prodMap
    (ContinuousMap.id (Sphere 2))

/-! ## Exact formulas for every arrow -/

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridCenterToTop_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridC m) :
    coordinateUnlinkExteriorPlanarNeckGridCenterToTop m x =
      (x.1, coordinateUnlinkExteriorPlanarNeckGridSphereToBall x.2) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridCenterToBottom_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridC m) :
    coordinateUnlinkExteriorPlanarNeckGridCenterToBottom m x =
      (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x.1, x.2) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridCenterToLeft_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridC m) :
    coordinateUnlinkExteriorPlanarNeckGridCenterToLeft m x =
      (coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m x.1, x.2) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridCenterToRight_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridC m) :
    coordinateUnlinkExteriorPlanarNeckGridCenterToRight m x =
      (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m x.1, x.2) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridTopToTopLeft_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridE m) :
    coordinateUnlinkExteriorPlanarNeckGridTopToTopLeft m x =
      (coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter m x.1, x.2) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridTopToTopRight_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridE m) :
    coordinateUnlinkExteriorPlanarNeckGridTopToTopRight m x =
      (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m x.1, x.2) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridBottomToBottomLeft_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridA m) :
    coordinateUnlinkExteriorPlanarNeckGridBottomToBottomLeft m x =
      (coordinateUnlinkExteriorPlanarNormalizedLeftSeam m x.1, x.2) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridBottomToBottomRight_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridA m) :
    coordinateUnlinkExteriorPlanarNeckGridBottomToBottomRight m x =
      (coordinateUnlinkExteriorPlanarNormalizedRightSeam m x.1, x.2) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridLeftToTopLeft_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridBL m) :
    coordinateUnlinkExteriorPlanarNeckGridLeftToTopLeft m x =
      (x.1, coordinateUnlinkExteriorPlanarNeckGridSphereToBall x.2) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridLeftToBottomLeft_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridBL m) :
    coordinateUnlinkExteriorPlanarNeckGridLeftToBottomLeft m x =
      (coordinateUnlinkExteriorPlanarNeckGridLeftOuterToNormalizedLeft m x.1, x.2) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridRightToTopRight_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridBR m) :
    coordinateUnlinkExteriorPlanarNeckGridRightToTopRight m x =
      (x.1, coordinateUnlinkExteriorPlanarNeckGridSphereToBall x.2) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridRightToBottomRight_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridBR m) :
    coordinateUnlinkExteriorPlanarNeckGridRightToBottomRight m x =
      (coordinateUnlinkExteriorPlanarNeckGridRightOuterToNormalizedRight m x.1, x.2) :=
  rfl

/-! ## The four commuting squares -/

theorem coordinateUnlinkExteriorPlanarNeckGrid_commTopLeft
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridC m) :
    coordinateUnlinkExteriorPlanarNeckGridTopToTopLeft m
        (coordinateUnlinkExteriorPlanarNeckGridCenterToTop m x) =
      coordinateUnlinkExteriorPlanarNeckGridLeftToTopLeft m
        (coordinateUnlinkExteriorPlanarNeckGridCenterToLeft m x) :=
  rfl

theorem coordinateUnlinkExteriorPlanarNeckGrid_commTopRight
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridC m) :
    coordinateUnlinkExteriorPlanarNeckGridTopToTopRight m
        (coordinateUnlinkExteriorPlanarNeckGridCenterToTop m x) =
      coordinateUnlinkExteriorPlanarNeckGridRightToTopRight m
        (coordinateUnlinkExteriorPlanarNeckGridCenterToRight m x) :=
  rfl

theorem coordinateUnlinkExteriorPlanarNeckGrid_commBottomLeft
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridC m) :
    coordinateUnlinkExteriorPlanarNeckGridBottomToBottomLeft m
        (coordinateUnlinkExteriorPlanarNeckGridCenterToBottom m x) =
      coordinateUnlinkExteriorPlanarNeckGridLeftToBottomLeft m
        (coordinateUnlinkExteriorPlanarNeckGridCenterToLeft m x) := by
  apply Prod.ext
  · let sigma := coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x.1
    have hsigma :
        (sigma.1, coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam x.1.2) = sigma := by
      apply Prod.ext
      · rfl
      · rfl
    rw [coordinateUnlinkExteriorPlanarNeckGridBottomToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridCenterToBottom_apply,
      coordinateUnlinkExteriorPlanarNeckGridLeftToBottomLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridCenterToLeft_apply,
      coordinateUnlinkExteriorPlanarNeckGridEndpointToLeftOuter_apply,
      coordinateUnlinkExteriorPlanarNeckGridLeftOuterToNormalizedLeft_apply]
    change coordinateUnlinkExteriorPlanarNormalizedLeftSeam m sigma = _
    rw [← hsigma,
      ← coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap_normalized m sigma.1]
    apply Prod.ext
    · rfl
    · exact congrArg partialSphereSpinAnnulusOne
        (coordinateUnlinkExteriorPlanarLeftLeafBoundary_compatibility
          m sigma.1 x.1.2).symm
  · rfl

theorem coordinateUnlinkExteriorPlanarNeckGrid_commBottomRight
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridC m) :
    coordinateUnlinkExteriorPlanarNeckGridBottomToBottomRight m
        (coordinateUnlinkExteriorPlanarNeckGridCenterToBottom m x) =
      coordinateUnlinkExteriorPlanarNeckGridRightToBottomRight m
        (coordinateUnlinkExteriorPlanarNeckGridCenterToRight m x) := by
  apply Prod.ext
  · apply Prod.ext
    · exact coordinateUnlinkExteriorPlanarRightNodeEndpoint_compatibility m x.1
    · exact coordinateUnlinkExteriorPlanarNormalizedRightSeam_time m
        (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x.1)
  · rfl

/-! ## The bundled diagram -/

/-- The concrete commuting `3 × 3` grid underlying the simultaneous neck and one-handle cut. -/
def coordinateUnlinkExteriorPlanarNeckGridDiagram
    (m : ℕ) [NeZero m] :
    TopologicalPushoutGridDiagram
      (CoordinateUnlinkExteriorPlanarNeckGridC m)
      (CoordinateUnlinkExteriorPlanarNeckGridE m)
      (CoordinateUnlinkExteriorPlanarNeckGridA m)
      (CoordinateUnlinkExteriorPlanarNeckGridBL m)
      (CoordinateUnlinkExteriorPlanarNeckGridBR m)
      (CoordinateUnlinkExteriorPlanarNeckGridHL m)
      (CoordinateUnlinkExteriorPlanarNeckGridHR m)
      (CoordinateUnlinkExteriorPlanarNeckGridFL m)
      CoordinateUnlinkExteriorPlanarNeckGridFR where
  centerToTop := coordinateUnlinkExteriorPlanarNeckGridCenterToTop m
  centerToBottom := coordinateUnlinkExteriorPlanarNeckGridCenterToBottom m
  centerToLeft := coordinateUnlinkExteriorPlanarNeckGridCenterToLeft m
  centerToRight := coordinateUnlinkExteriorPlanarNeckGridCenterToRight m
  topToTopLeft := coordinateUnlinkExteriorPlanarNeckGridTopToTopLeft m
  topToTopRight := coordinateUnlinkExteriorPlanarNeckGridTopToTopRight m
  bottomToBottomLeft := coordinateUnlinkExteriorPlanarNeckGridBottomToBottomLeft m
  bottomToBottomRight := coordinateUnlinkExteriorPlanarNeckGridBottomToBottomRight m
  leftToTopLeft := coordinateUnlinkExteriorPlanarNeckGridLeftToTopLeft m
  leftToBottomLeft := coordinateUnlinkExteriorPlanarNeckGridLeftToBottomLeft m
  rightToTopRight := coordinateUnlinkExteriorPlanarNeckGridRightToTopRight m
  rightToBottomRight := coordinateUnlinkExteriorPlanarNeckGridRightToBottomRight m
  commTopLeft := coordinateUnlinkExteriorPlanarNeckGrid_commTopLeft m
  commTopRight := coordinateUnlinkExteriorPlanarNeckGrid_commTopRight m
  commBottomLeft := coordinateUnlinkExteriorPlanarNeckGrid_commBottomLeft m
  commBottomRight := coordinateUnlinkExteriorPlanarNeckGrid_commBottomRight m

/-! The following projection laws make every bundled leg available without unfolding the
structure. -/

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridDiagram_centerToTop_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridC m) :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToTop x =
      coordinateUnlinkExteriorPlanarNeckGridCenterToTop m x :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridDiagram_centerToBottom_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridC m) :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToBottom x =
      coordinateUnlinkExteriorPlanarNeckGridCenterToBottom m x :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridDiagram_centerToLeft_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridC m) :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToLeft x =
      coordinateUnlinkExteriorPlanarNeckGridCenterToLeft m x :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridDiagram_centerToRight_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridC m) :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).centerToRight x =
      coordinateUnlinkExteriorPlanarNeckGridCenterToRight m x :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridDiagram_topToTopLeft_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridE m) :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).topToTopLeft x =
      coordinateUnlinkExteriorPlanarNeckGridTopToTopLeft m x :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridDiagram_topToTopRight_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridE m) :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).topToTopRight x =
      coordinateUnlinkExteriorPlanarNeckGridTopToTopRight m x :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridDiagram_bottomToBottomLeft_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridA m) :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).bottomToBottomLeft x =
      coordinateUnlinkExteriorPlanarNeckGridBottomToBottomLeft m x :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridDiagram_bottomToBottomRight_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridA m) :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).bottomToBottomRight x =
      coordinateUnlinkExteriorPlanarNeckGridBottomToBottomRight m x :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridDiagram_leftToTopLeft_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridBL m) :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToTopLeft x =
      coordinateUnlinkExteriorPlanarNeckGridLeftToTopLeft m x :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridDiagram_leftToBottomLeft_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridBL m) :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).leftToBottomLeft x =
      coordinateUnlinkExteriorPlanarNeckGridLeftToBottomLeft m x :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridDiagram_rightToTopRight_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridBR m) :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToTopRight x =
      coordinateUnlinkExteriorPlanarNeckGridRightToTopRight m x :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckGridDiagram_rightToBottomRight_apply
    (m : ℕ) [NeZero m] (x : CoordinateUnlinkExteriorPlanarNeckGridBR m) :
    (coordinateUnlinkExteriorPlanarNeckGridDiagram m).rightToBottomRight x =
      coordinateUnlinkExteriorPlanarNeckGridRightToBottomRight m x :=
  rfl

end SplittingSpheres
