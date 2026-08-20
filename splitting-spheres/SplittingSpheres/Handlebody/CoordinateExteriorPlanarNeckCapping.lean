/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckGrid
public import SplittingSpheres.Foundations.TopologicalPushoutComm

/-!
# Capping the two sides of the planar neck grid

This file adds literal interval-product four-balls to the two column models of the planar neck
grid.  For one fixed left label it caps the single neck of that leaf.  For the right node it
caps all labelled necks simultaneously.  Two auxiliary commuting grids reduce both capped
column-first pushouts, row by row, to the partial spin of the standard annulus and hence to
the literal one-handle.

The constructions are point-set topological.  They make no separation, embedding, manifold,
smoothness, or connected-sum assertion.
-/

@[expose] public section


open Function Metric Topology

noncomputable section

namespace SplittingSpheres

universe u

/-! ## Identity-leg contractions local to this capping construction -/

/-- Collapse a pushout whose right leg is the identity.  This helper deliberately remains in
the neck-capping module rather than extending the generic pushout foundation API. -/
def coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
    {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]
    (f : C(A, X)) :
    TopologicalPushout f (ContinuousMap.id A) ≃ₜ X where
  toFun := topologicalPushoutDesc f (ContinuousMap.id A)
    (ContinuousMap.id X) f (by intro a; change f a = f a; rfl)
  invFun := topologicalPushoutInl f (ContinuousMap.id A)
  left_inv z := by
    rcases topologicalPushout_jointly_surjective f (ContinuousMap.id A) z with
      ⟨x, rfl⟩ | ⟨a, rfl⟩
    · rw [topologicalPushoutDesc_inl]
      simp only [ContinuousMap.id_apply]
    · rw [topologicalPushoutDesc_inr]
      simpa only [ContinuousMap.id_apply] using
        topologicalPushout_condition f (ContinuousMap.id A) a
  right_inv x := by
    rw [topologicalPushoutDesc_inl]
    simp only [ContinuousMap.id_apply]
  continuous_toFun :=
    (topologicalPushoutDesc f (ContinuousMap.id A)
      (ContinuousMap.id X) f (by intro a; change f a = f a; rfl)).continuous
  continuous_invFun := (topologicalPushoutInl f (ContinuousMap.id A)).continuous

/-- Collapse a pushout whose left leg is the identity.  This helper deliberately remains in
the neck-capping module rather than extending the generic pushout foundation API. -/
def coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph
    {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]
    (f : C(A, X)) :
    TopologicalPushout (ContinuousMap.id A) f ≃ₜ X where
  toFun := topologicalPushoutDesc (ContinuousMap.id A) f
    f (ContinuousMap.id X) (by intro a; change f a = f a; rfl)
  invFun := topologicalPushoutInr (ContinuousMap.id A) f
  left_inv z := by
    rcases topologicalPushout_jointly_surjective (ContinuousMap.id A) f z with
      ⟨a, rfl⟩ | ⟨x, rfl⟩
    · rw [topologicalPushoutDesc_inl]
      simpa only [ContinuousMap.id_apply] using
        (topologicalPushout_condition (ContinuousMap.id A) f a).symm
    · rw [topologicalPushoutDesc_inr]
      simp only [ContinuousMap.id_apply]
  right_inv x := by
    rw [topologicalPushoutDesc_inr]
    simp only [ContinuousMap.id_apply]
  continuous_toFun :=
    (topologicalPushoutDesc (ContinuousMap.id A) f
      f (ContinuousMap.id X) (by intro a; change f a = f a; rfl)).continuous
  continuous_invFun := (topologicalPushoutInr (ContinuousMap.id A) f).continuous

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph_inl
    {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]
    (f : C(A, X)) (x : X) :
    coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph f
        (topologicalPushoutInl f (ContinuousMap.id A) x) = x :=
  topologicalPushoutDesc_inl _ _ _ _ _ _

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph_inr
    {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]
    (f : C(A, X)) (a : A) :
    coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph f
        (topologicalPushoutInr f (ContinuousMap.id A) a) = f a :=
  topologicalPushoutDesc_inr _ _ _ _ _ _

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph_inl
    {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]
    (f : C(A, X)) (a : A) :
    coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph f
        (topologicalPushoutInl (ContinuousMap.id A) f a) = f a :=
  topologicalPushoutDesc_inl _ _ _ _ _ _

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph_inr
    {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]
    (f : C(A, X)) (x : X) :
    coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph f
        (topologicalPushoutInr (ContinuousMap.id A) f x) = x :=
  topologicalPushoutDesc_inr _ _ _ _ _ _

/- A fixed left leaf, its neck cap, and the three common faces. -/

abbrev CoordinateUnlinkExteriorPlanarLeftCappingGridC := ProductFourCorner
abbrev CoordinateUnlinkExteriorPlanarLeftCappingGridE := ProductFourEndPiece
abbrev CoordinateUnlinkExteriorPlanarLeftCappingGridA :=
  CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2
abbrev CoordinateUnlinkExteriorPlanarLeftCappingGridBL :=
  CoordinateUnlinkExteriorPlanarBaseLeftOuterArc × Sphere 2
abbrev CoordinateUnlinkExteriorPlanarLeftCappingGridBR :=
  CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2
abbrev CoordinateUnlinkExteriorPlanarLeftCappingGridHL :=
  CoordinateUnlinkExteriorPlanarBaseLeftOuterArc × EuclideanClosedBall 3
abbrev CoordinateUnlinkExteriorPlanarLeftCappingGridHR :=
  CoordinateUnlinkExteriorPlanarNeckInterval × EuclideanClosedBall 3
abbrev CoordinateUnlinkExteriorPlanarLeftCappingGridFL := PartialSphereSpinAnnulus × Sphere 2
abbrev CoordinateUnlinkExteriorPlanarLeftCappingGridFR :=
  CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2

def coordinateUnlinkExteriorPlanarLeftCappingGridCenterToTop :
    C(CoordinateUnlinkExteriorPlanarLeftCappingGridC,
      CoordinateUnlinkExteriorPlanarLeftCappingGridE) :=
  productFourCornerToEnd

def coordinateUnlinkExteriorPlanarLeftCappingGridCenterToBottom :
    C(CoordinateUnlinkExteriorPlanarLeftCappingGridC,
      CoordinateUnlinkExteriorPlanarLeftCappingGridA) :=
  coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam.prodMap
    (ContinuousMap.id (Sphere 2))

def coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft :
    C(CoordinateUnlinkExteriorPlanarLeftCappingGridC,
      CoordinateUnlinkExteriorPlanarLeftCappingGridBL) :=
  coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc.prodMap
    (ContinuousMap.id (Sphere 2))

def coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight :
    C(CoordinateUnlinkExteriorPlanarLeftCappingGridC,
      CoordinateUnlinkExteriorPlanarLeftCappingGridBR) :=
  coordinateUnlinkExteriorPlanarLeftCappingGridCenterToBottom

def coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft :
    C(CoordinateUnlinkExteriorPlanarLeftCappingGridE,
      CoordinateUnlinkExteriorPlanarLeftCappingGridHL) :=
  coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc.prodMap
    (ContinuousMap.id (EuclideanClosedBall 3))

def coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight :
    C(CoordinateUnlinkExteriorPlanarLeftCappingGridE,
      CoordinateUnlinkExteriorPlanarLeftCappingGridHR) :=
  coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam.prodMap
    (ContinuousMap.id (EuclideanClosedBall 3))

def coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomLeft
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(CoordinateUnlinkExteriorPlanarLeftCappingGridA,
      CoordinateUnlinkExteriorPlanarLeftCappingGridFL) :=
  (partialSphereSpinAnnulusOne.comp
    (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a)).prodMap
      (ContinuousMap.id (Sphere 2))

def coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomRight :
    C(CoordinateUnlinkExteriorPlanarLeftCappingGridA,
      CoordinateUnlinkExteriorPlanarLeftCappingGridFR) :=
  ContinuousMap.id CoordinateUnlinkExteriorPlanarLeftCappingGridA

def coordinateUnlinkExteriorPlanarLeftCappingGridLeftToTopLeft :
    C(CoordinateUnlinkExteriorPlanarLeftCappingGridBL,
      CoordinateUnlinkExteriorPlanarLeftCappingGridHL) :=
  (ContinuousMap.id CoordinateUnlinkExteriorPlanarBaseLeftOuterArc).prodMap
    coordinateUnlinkExteriorPlanarNeckGridSphereToBall

def coordinateUnlinkExteriorPlanarLeftCappingGridLeftToBottomLeft :
    C(CoordinateUnlinkExteriorPlanarLeftCappingGridBL,
      CoordinateUnlinkExteriorPlanarLeftCappingGridFL) :=
  (partialSphereSpinAnnulusOne.comp
    coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap).prodMap
      (ContinuousMap.id (Sphere 2))

def coordinateUnlinkExteriorPlanarLeftCappingGridRightToTopRight :
    C(CoordinateUnlinkExteriorPlanarLeftCappingGridBR,
      CoordinateUnlinkExteriorPlanarLeftCappingGridHR) :=
  (ContinuousMap.id CoordinateUnlinkExteriorPlanarNeckInterval).prodMap
    coordinateUnlinkExteriorPlanarNeckGridSphereToBall

def coordinateUnlinkExteriorPlanarLeftCappingGridRightToBottomRight :
    C(CoordinateUnlinkExteriorPlanarLeftCappingGridBR,
      CoordinateUnlinkExteriorPlanarLeftCappingGridFR) :=
  ContinuousMap.id CoordinateUnlinkExteriorPlanarLeftCappingGridBR

/-- The auxiliary grid which attaches one interval-product four-ball to the neck of the fixed
left leaf labelled by `a`. -/
def coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram
    (m : ℕ) [NeZero m] (a : ZMod m) :
    TopologicalPushoutGridDiagram CoordinateUnlinkExteriorPlanarLeftCappingGridC
      CoordinateUnlinkExteriorPlanarLeftCappingGridE
      CoordinateUnlinkExteriorPlanarLeftCappingGridA
      CoordinateUnlinkExteriorPlanarLeftCappingGridBL
      CoordinateUnlinkExteriorPlanarLeftCappingGridBR
      CoordinateUnlinkExteriorPlanarLeftCappingGridHL
      CoordinateUnlinkExteriorPlanarLeftCappingGridHR
      CoordinateUnlinkExteriorPlanarLeftCappingGridFL
      CoordinateUnlinkExteriorPlanarLeftCappingGridFR where
  centerToTop := coordinateUnlinkExteriorPlanarLeftCappingGridCenterToTop
  centerToBottom := coordinateUnlinkExteriorPlanarLeftCappingGridCenterToBottom
  centerToLeft := coordinateUnlinkExteriorPlanarLeftCappingGridCenterToLeft
  centerToRight := coordinateUnlinkExteriorPlanarLeftCappingGridCenterToRight
  topToTopLeft := coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopLeft
  topToTopRight := coordinateUnlinkExteriorPlanarLeftCappingGridTopToTopRight
  bottomToBottomLeft := coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomLeft m a
  bottomToBottomRight := coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomRight
  leftToTopLeft := coordinateUnlinkExteriorPlanarLeftCappingGridLeftToTopLeft
  leftToBottomLeft := coordinateUnlinkExteriorPlanarLeftCappingGridLeftToBottomLeft
  rightToTopRight := coordinateUnlinkExteriorPlanarLeftCappingGridRightToTopRight
  rightToBottomRight := coordinateUnlinkExteriorPlanarLeftCappingGridRightToBottomRight
  commTopLeft := by rintro ⟨e, s⟩; rfl
  commTopRight := by rintro ⟨e, s⟩; rfl
  commBottomLeft := by
    rintro ⟨e, s⟩
    apply Prod.ext
    · exact congrArg partialSphereSpinAnnulusOne
        (coordinateUnlinkExteriorPlanarLeftLeafBoundary_compatibility m a e).symm
    · rfl
  commBottomRight := by rintro ⟨e, s⟩; rfl

/- The simultaneous right node: the left column is the cap family, the right column is the
uncapped right node. -/

abbrev CoordinateUnlinkExteriorPlanarRightNodeCappingGridC (m : ℕ) :=
  CoordinateUnlinkExteriorPlanarNeckGridC m
abbrev CoordinateUnlinkExteriorPlanarRightNodeCappingGridE (m : ℕ) :=
  CoordinateUnlinkExteriorPlanarNeckGridE m
abbrev CoordinateUnlinkExteriorPlanarRightNodeCappingGridA (m : ℕ) :=
  CoordinateUnlinkExteriorPlanarNeckGridA m
abbrev CoordinateUnlinkExteriorPlanarRightNodeCappingGridBL (m : ℕ) :=
  CoordinateUnlinkExteriorPlanarNeckGridA m
abbrev CoordinateUnlinkExteriorPlanarRightNodeCappingGridBR (m : ℕ) :=
  CoordinateUnlinkExteriorPlanarNeckGridBR m
abbrev CoordinateUnlinkExteriorPlanarRightNodeCappingGridHL (m : ℕ) :=
  CoordinateUnlinkExteriorPlanarNeckGridHR m
abbrev CoordinateUnlinkExteriorPlanarRightNodeCappingGridHR (m : ℕ) :=
  CoordinateUnlinkExteriorPlanarNeckGridHR m
abbrev CoordinateUnlinkExteriorPlanarRightNodeCappingGridFL (m : ℕ) :=
  CoordinateUnlinkExteriorPlanarNeckGridA m
abbrev CoordinateUnlinkExteriorPlanarRightNodeCappingGridFR :=
  CoordinateUnlinkExteriorPlanarNeckGridFR

def coordinateUnlinkExteriorPlanarRightNodeCappingGridCenterToTop (m : ℕ) [NeZero m] :
  C(CoordinateUnlinkExteriorPlanarRightNodeCappingGridC m,
  CoordinateUnlinkExteriorPlanarRightNodeCappingGridE m) :=
  coordinateUnlinkExteriorPlanarNeckGridCenterToTop m

def coordinateUnlinkExteriorPlanarRightNodeCappingGridCenterToBottom (m : ℕ) [NeZero m] :
  C(CoordinateUnlinkExteriorPlanarRightNodeCappingGridC m,
  CoordinateUnlinkExteriorPlanarRightNodeCappingGridA m) :=
  coordinateUnlinkExteriorPlanarNeckGridCenterToBottom m

def coordinateUnlinkExteriorPlanarRightNodeCappingGridCenterToLeft (m : ℕ) [NeZero m] :
  C(CoordinateUnlinkExteriorPlanarRightNodeCappingGridC m,
  CoordinateUnlinkExteriorPlanarRightNodeCappingGridBL m) :=
  coordinateUnlinkExteriorPlanarRightNodeCappingGridCenterToBottom m

def coordinateUnlinkExteriorPlanarRightNodeCappingGridCenterToRight (m : ℕ) [NeZero m] :
  C(CoordinateUnlinkExteriorPlanarRightNodeCappingGridC m,
  CoordinateUnlinkExteriorPlanarRightNodeCappingGridBR m) :=
  coordinateUnlinkExteriorPlanarNeckGridCenterToRight m

def coordinateUnlinkExteriorPlanarRightNodeCappingGridTopToTopLeft (m : ℕ) [NeZero m] :
  C(CoordinateUnlinkExteriorPlanarRightNodeCappingGridE m,
  CoordinateUnlinkExteriorPlanarRightNodeCappingGridHL m) :=
  (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m).prodMap
    (ContinuousMap.id (EuclideanClosedBall 3))

def coordinateUnlinkExteriorPlanarRightNodeCappingGridTopToTopRight (m : ℕ) [NeZero m] :
  C(CoordinateUnlinkExteriorPlanarRightNodeCappingGridE m,
  CoordinateUnlinkExteriorPlanarRightNodeCappingGridHR m) :=
  coordinateUnlinkExteriorPlanarNeckGridTopToTopRight m

def coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomLeft (m : ℕ) [NeZero m] :
  C(CoordinateUnlinkExteriorPlanarRightNodeCappingGridA m,
  CoordinateUnlinkExteriorPlanarRightNodeCappingGridFL m) :=
  ContinuousMap.id (CoordinateUnlinkExteriorPlanarRightNodeCappingGridA m)

def coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomRight (m : ℕ) [NeZero m] :
  C(CoordinateUnlinkExteriorPlanarRightNodeCappingGridA m,
  CoordinateUnlinkExteriorPlanarRightNodeCappingGridFR) :=
  coordinateUnlinkExteriorPlanarNeckGridBottomToBottomRight m

def coordinateUnlinkExteriorPlanarRightNodeCappingGridLeftToTopLeft (m : ℕ) [NeZero m] :
  C(CoordinateUnlinkExteriorPlanarRightNodeCappingGridBL m,
  CoordinateUnlinkExteriorPlanarRightNodeCappingGridHL m) :=
  (ContinuousMap.id (CoordinateUnlinkExteriorPlanarNeckGridSeam m)).prodMap
    coordinateUnlinkExteriorPlanarNeckGridSphereToBall

def coordinateUnlinkExteriorPlanarRightNodeCappingGridLeftToBottomLeft (m : ℕ) [NeZero m] :
  C(CoordinateUnlinkExteriorPlanarRightNodeCappingGridBL m,
  CoordinateUnlinkExteriorPlanarRightNodeCappingGridFL m) :=
  ContinuousMap.id (CoordinateUnlinkExteriorPlanarRightNodeCappingGridBL m)

def coordinateUnlinkExteriorPlanarRightNodeCappingGridRightToTopRight (m : ℕ) [NeZero m] :
  C(CoordinateUnlinkExteriorPlanarRightNodeCappingGridBR m,
  CoordinateUnlinkExteriorPlanarRightNodeCappingGridHR m) :=
  coordinateUnlinkExteriorPlanarNeckGridRightToTopRight m

def coordinateUnlinkExteriorPlanarRightNodeCappingGridRightToBottomRight (m : ℕ) [NeZero m] :
  C(CoordinateUnlinkExteriorPlanarRightNodeCappingGridBR m,
  CoordinateUnlinkExteriorPlanarRightNodeCappingGridFR) :=
  coordinateUnlinkExteriorPlanarNeckGridRightToBottomRight m

/-- The auxiliary grid which attaches all `m` labelled interval-product four-balls to the
right node simultaneously. -/
def coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram (m : ℕ) [NeZero m] :
    TopologicalPushoutGridDiagram
      (CoordinateUnlinkExteriorPlanarRightNodeCappingGridC m)
        (CoordinateUnlinkExteriorPlanarRightNodeCappingGridE m)
        (CoordinateUnlinkExteriorPlanarRightNodeCappingGridA m)
        (CoordinateUnlinkExteriorPlanarRightNodeCappingGridBL m)
        (CoordinateUnlinkExteriorPlanarRightNodeCappingGridBR m)
      (CoordinateUnlinkExteriorPlanarRightNodeCappingGridHL m)
        (CoordinateUnlinkExteriorPlanarRightNodeCappingGridHR m)
        (CoordinateUnlinkExteriorPlanarRightNodeCappingGridFL m)
        CoordinateUnlinkExteriorPlanarRightNodeCappingGridFR where
  centerToTop := coordinateUnlinkExteriorPlanarRightNodeCappingGridCenterToTop m
  centerToBottom := coordinateUnlinkExteriorPlanarRightNodeCappingGridCenterToBottom m
  centerToLeft := coordinateUnlinkExteriorPlanarRightNodeCappingGridCenterToLeft m
  centerToRight := coordinateUnlinkExteriorPlanarRightNodeCappingGridCenterToRight m
  topToTopLeft := coordinateUnlinkExteriorPlanarRightNodeCappingGridTopToTopLeft m
  topToTopRight := coordinateUnlinkExteriorPlanarRightNodeCappingGridTopToTopRight m
  bottomToBottomLeft := coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomLeft m
  bottomToBottomRight := coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomRight m
  leftToTopLeft := coordinateUnlinkExteriorPlanarRightNodeCappingGridLeftToTopLeft m
  leftToBottomLeft := coordinateUnlinkExteriorPlanarRightNodeCappingGridLeftToBottomLeft m
  rightToTopRight := coordinateUnlinkExteriorPlanarRightNodeCappingGridRightToTopRight m
  rightToBottomRight := coordinateUnlinkExteriorPlanarRightNodeCappingGridRightToBottomRight m
  commTopLeft := by rintro ⟨e, s⟩; rfl
  commTopRight := coordinateUnlinkExteriorPlanarNeckGrid_commTopRight m
  commBottomLeft := by rintro ⟨e, s⟩; rfl
  commBottomRight := coordinateUnlinkExteriorPlanarNeckGrid_commBottomRight m

/- The four intended column-first objects are already honest types. -/

abbrev CoordinateUnlinkExteriorPlanarLeftLeafUncapped (m : ℕ) [NeZero m] (a : ZMod m) :=
  (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).verticalLeft

abbrev CoordinateUnlinkExteriorPlanarLeftLeafNeckBoundary (m : ℕ) [NeZero m] (a : ZMod m) :=
  (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).verticalCenter

abbrev CoordinateUnlinkExteriorPlanarLeftLeafIntervalCap (m : ℕ) [NeZero m] (a : ZMod m) :=
  (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).verticalRight

abbrev CoordinateUnlinkExteriorPlanarLeftLeafCapped (m : ℕ) [NeZero m] (a : ZMod m) :=
  (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).columnFirst

abbrev CoordinateUnlinkExteriorPlanarRightNodeCapFamily (m : ℕ) [NeZero m] :=
  (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).verticalLeft

abbrev CoordinateUnlinkExteriorPlanarRightNodeNeckBoundaryFamily (m : ℕ) [NeZero m] :=
  (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).verticalCenter

abbrev CoordinateUnlinkExteriorPlanarRightNodeUncapped (m : ℕ) [NeZero m] :=
  (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).verticalRight

abbrev CoordinateUnlinkExteriorPlanarRightNodeCapped (m : ℕ) [NeZero m] :=
  (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).columnFirst

/-! ## Canonical maps between the column-first pieces -/

/-- Include the fixed left neck boundary in the uncapped left leaf. -/
abbrev coordinateUnlinkExteriorPlanarLeftLeafNeckToUncapped
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(CoordinateUnlinkExteriorPlanarLeftLeafNeckBoundary m a,
      CoordinateUnlinkExteriorPlanarLeftLeafUncapped m a) :=
  (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).verticalCenterToLeft

/-- Include the fixed left neck boundary in its interval-product cap. -/
abbrev coordinateUnlinkExteriorPlanarLeftLeafNeckToIntervalCap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(CoordinateUnlinkExteriorPlanarLeftLeafNeckBoundary m a,
      CoordinateUnlinkExteriorPlanarLeftLeafIntervalCap m a) :=
  (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).verticalCenterToRight

/-- Include the uncapped fixed left leaf in the capped column pushout. -/
abbrev coordinateUnlinkExteriorPlanarLeftLeafUncappedToCapped
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(CoordinateUnlinkExteriorPlanarLeftLeafUncapped m a,
      CoordinateUnlinkExteriorPlanarLeftLeafCapped m a) :=
  topologicalPushoutInl
    (coordinateUnlinkExteriorPlanarLeftLeafNeckToUncapped m a)
    (coordinateUnlinkExteriorPlanarLeftLeafNeckToIntervalCap m a)

/-- Include the fixed left interval cap in the capped column pushout. -/
abbrev coordinateUnlinkExteriorPlanarLeftLeafIntervalCapToCapped
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(CoordinateUnlinkExteriorPlanarLeftLeafIntervalCap m a,
      CoordinateUnlinkExteriorPlanarLeftLeafCapped m a) :=
  topologicalPushoutInr
    (coordinateUnlinkExteriorPlanarLeftLeafNeckToUncapped m a)
    (coordinateUnlinkExteriorPlanarLeftLeafNeckToIntervalCap m a)

/-- Include every labelled neck boundary in the simultaneous cap family. -/
abbrev coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarRightNodeNeckBoundaryFamily m,
      CoordinateUnlinkExteriorPlanarRightNodeCapFamily m) :=
  (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).verticalCenterToLeft

/-- Include every labelled neck boundary in the uncapped right node. -/
abbrev coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarRightNodeNeckBoundaryFamily m,
      CoordinateUnlinkExteriorPlanarRightNodeUncapped m) :=
  (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).verticalCenterToRight

/-- Include the simultaneous cap family in the capped right-node pushout. -/
abbrev coordinateUnlinkExteriorPlanarRightNodeCapFamilyToCapped
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarRightNodeCapFamily m,
      CoordinateUnlinkExteriorPlanarRightNodeCapped m) :=
  topologicalPushoutInl
    (coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m)
    (coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped m)

/-- Include the uncapped right node in the capped right-node pushout. -/
abbrev coordinateUnlinkExteriorPlanarRightNodeUncappedToCapped
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarRightNodeUncapped m,
      CoordinateUnlinkExteriorPlanarRightNodeCapped m) :=
  topologicalPushoutInr
    (coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m)
    (coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped m)

/-- The uncapped right-node column is definitionally the right column of the original neck
grid. -/
def coordinateUnlinkExteriorPlanarRightNodeUncappedHomeomorphNeckGridVerticalRight
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarRightNodeUncapped m ≃ₜ
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalRight :=
  Homeomorph.refl _

/-- The common right-node neck family is definitionally the center column of the original
neck grid. -/
def coordinateUnlinkExteriorPlanarRightNodeNeckBoundaryHomeomorphNeckGridVerticalCenter
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarRightNodeNeckBoundaryFamily m ≃ₜ
      (coordinateUnlinkExteriorPlanarNeckGridDiagram m).verticalCenter :=
  Homeomorph.refl _

/- The top rows reduce to the already recognized boundary-circle products. -/

def coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalTopHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalTop ≃ₜ
      OneHandlePiece :=
  coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph m a

def coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddle ≃ₜ
      OneHandleCapBoundary := by
  let _ : T2Space CoordinateUnlinkExteriorPlanarLeftLeafBoundaryPushout :=
    (coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph m a).symm.t2Space
  exact
    (topologicalPushoutProductHomeomorph
      coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
      coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam
      (Sphere 2)
      injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
      injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam).trans
      ((coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph m a).prodCongr
        (Homeomorph.refl (Sphere 2)))

def coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalTopHomeomorph
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalTop ≃ₜ
      OneHandlePiece :=
  coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph m

def coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalMiddleHomeomorph
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddle ≃ₜ
      OneHandleCapBoundary := by
  let _ : T2Space (CoordinateUnlinkExteriorPlanarRightNodeBoundaryPushout m) :=
    (coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph m).symm.t2Space
  exact
    (topologicalPushoutProductHomeomorph
      (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m)
      (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m)
      (Sphere 2)
      (injective_coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m)
      (injective_coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m)).trans
      ((coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph m).prodCongr
        (Homeomorph.refl (Sphere 2)))

/- The interval cap itself is the literal product four-ball after the existing affine change
of first coordinate. -/

def coordinateUnlinkExteriorPlanarNeckIntervalCapHomeomorphProductFourBall :
    (CoordinateUnlinkExteriorPlanarNeckInterval × EuclideanClosedBall 3) ≃ₜ
      ProductFourBall :=
  euclideanClosedBallOneHomeomorphUnitInterval.symm.prodCongr
    (Homeomorph.refl (EuclideanClosedBall 3))

def coordinateUnlinkExteriorPlanarNeckIntervalSideHomeomorphProductFourSide :
    (CoordinateUnlinkExteriorPlanarNeckInterval × Sphere 2) ≃ₜ
      ProductFourSidePiece :=
  euclideanClosedBallOneHomeomorphUnitInterval.symm.prodCongr
    (Homeomorph.refl (Sphere 2))

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckIntervalCapHomeomorphProductFourBall_apply
    (t : CoordinateUnlinkExteriorPlanarNeckInterval)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarNeckIntervalCapHomeomorphProductFourBall (t, b) =
      (unitIntervalToEuclideanClosedBallOne t, b) :=
  rfl

theorem coordinateUnlinkExteriorPlanarNeckIntervalSideHomeomorphProductFourSide_endpoint
    (x : ProductFourCorner) :
    coordinateUnlinkExteriorPlanarNeckIntervalSideHomeomorphProductFourSide
      (coordinateUnlinkExteriorPlanarLeftCappingGridCenterToBottom x) =
      productFourCornerToSide x := by
  rcases x with ⟨e, s⟩
  rw [productFourCornerToSide_apply]
  apply Prod.ext
  · change euclideanClosedBallOneHomeomorphUnitInterval.symm
        (euclideanClosedBallOneHomeomorphUnitInterval
          ⟨e.1, sphere_subset_closedBall e.2⟩) = _
    rw [Homeomorph.symm_apply_apply]
  · rfl

theorem coordinateUnlinkExteriorPlanarLeftCappingGridCenterToTop_compatibility
    (x : ProductFourCorner) :
    (Homeomorph.refl ProductFourEndPiece)
        (coordinateUnlinkExteriorPlanarLeftCappingGridCenterToTop x) =
      productFourCornerToEnd ((Homeomorph.refl ProductFourCorner) x) :=
  rfl

theorem coordinateUnlinkExteriorPlanarLeftCappingGridCenterToBottom_compatibility
    (x : ProductFourCorner) :
    coordinateUnlinkExteriorPlanarNeckIntervalSideHomeomorphProductFourSide
        (coordinateUnlinkExteriorPlanarLeftCappingGridCenterToBottom x) =
      productFourCornerToSide ((Homeomorph.refl ProductFourCorner) x) :=
  coordinateUnlinkExteriorPlanarNeckIntervalSideHomeomorphProductFourSide_endpoint x

/-- Identify the fixed left neck boundary with the standard three-sphere through the literal
two-face boundary pushout of `ProductFourBall`. -/
def coordinateUnlinkExteriorPlanarLeftLeafNeckBoundaryHomeomorphSphere
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorPlanarLeftLeafNeckBoundary m a ≃ₜ Sphere 3 :=
  (topologicalPushoutCongr
    coordinateUnlinkExteriorPlanarLeftCappingGridCenterToTop
      coordinateUnlinkExteriorPlanarLeftCappingGridCenterToBottom
    productFourCornerToEnd productFourCornerToSide
    (Homeomorph.refl ProductFourCorner)
    (Homeomorph.refl ProductFourEndPiece)
    coordinateUnlinkExteriorPlanarNeckIntervalSideHomeomorphProductFourSide
    coordinateUnlinkExteriorPlanarLeftCappingGridCenterToTop_compatibility
    coordinateUnlinkExteriorPlanarLeftCappingGridCenterToBottom_compatibility).trans <|
      (topologicalPushoutComm productFourCornerToEnd productFourCornerToSide).trans
        productFourBoundaryPushoutHomeomorphSphere

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafNeckBoundaryHomeomorphSphere_inl
    (m : ℕ) [NeZero m] (a : ZMod m) (e : ProductFourEndPiece) :
    coordinateUnlinkExteriorPlanarLeftLeafNeckBoundaryHomeomorphSphere m a
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToTop
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToBottom e) =
      productFourBallBoundaryHomeomorphSphere (productFourEndToBoundary e) := by
  change ((topologicalPushoutCongr
    coordinateUnlinkExteriorPlanarLeftCappingGridCenterToTop
    coordinateUnlinkExteriorPlanarLeftCappingGridCenterToBottom
    productFourCornerToEnd productFourCornerToSide
    (Homeomorph.refl ProductFourCorner)
    (Homeomorph.refl ProductFourEndPiece)
    coordinateUnlinkExteriorPlanarNeckIntervalSideHomeomorphProductFourSide
    coordinateUnlinkExteriorPlanarLeftCappingGridCenterToTop_compatibility
    coordinateUnlinkExteriorPlanarLeftCappingGridCenterToBottom_compatibility).trans
      ((topologicalPushoutComm productFourCornerToEnd productFourCornerToSide).trans
        productFourBoundaryPushoutHomeomorphSphere))
      (topologicalPushoutInl
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToTop
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToBottom e) = _
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply,
    topologicalPushoutCongr_inl, topologicalPushoutComm_inl]
  change productFourBoundaryPushoutHomeomorphSphere
      (topologicalPushoutInr productFourCornerToSide productFourCornerToEnd e) = _
  rw [productFourBoundaryPushoutHomeomorphSphere, Homeomorph.trans_apply,
    productFourBoundaryPushoutHomeomorph_inr]

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafNeckBoundaryHomeomorphSphere_inr
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarLeftLeafNeckBoundaryHomeomorphSphere m a
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToTop
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToBottom
          (t, s)) =
      productFourBallBoundaryHomeomorphSphere
        (productFourSideToBoundary
          (coordinateUnlinkExteriorPlanarNeckIntervalSideHomeomorphProductFourSide
            (t, s))) := by
  change ((topologicalPushoutCongr
    coordinateUnlinkExteriorPlanarLeftCappingGridCenterToTop
    coordinateUnlinkExteriorPlanarLeftCappingGridCenterToBottom
    productFourCornerToEnd productFourCornerToSide
    (Homeomorph.refl ProductFourCorner)
    (Homeomorph.refl ProductFourEndPiece)
    coordinateUnlinkExteriorPlanarNeckIntervalSideHomeomorphProductFourSide
    coordinateUnlinkExteriorPlanarLeftCappingGridCenterToTop_compatibility
    coordinateUnlinkExteriorPlanarLeftCappingGridCenterToBottom_compatibility).trans
      ((topologicalPushoutComm productFourCornerToEnd productFourCornerToSide).trans
        productFourBoundaryPushoutHomeomorphSphere))
      (topologicalPushoutInr
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToTop
        coordinateUnlinkExteriorPlanarLeftCappingGridCenterToBottom (t, s)) = _
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply,
    topologicalPushoutCongr_inr, topologicalPushoutComm_inr]
  change productFourBoundaryPushoutHomeomorphSphere
      (topologicalPushoutInl productFourCornerToSide productFourCornerToEnd
        (coordinateUnlinkExteriorPlanarNeckIntervalSideHomeomorphProductFourSide
          (t, s))) = _
  rw [productFourBoundaryPushoutHomeomorphSphere, Homeomorph.trans_apply,
    productFourBoundaryPushoutHomeomorph_inl]

def coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalBottomHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalBottom ≃ₜ
      CoordinateUnlinkExteriorPlanarLeftCappingGridFL :=
  coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
    (coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomLeft m a)

/-- The fixed left interval cap is the literal product four-ball `D¹ × B³`. -/
def coordinateUnlinkExteriorPlanarLeftLeafIntervalCapHomeomorphProductFourBall
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).verticalRight ≃ₜ
      ProductFourBall :=
  (coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
    coordinateUnlinkExteriorPlanarLeftCappingGridRightToTopRight).trans
    coordinateUnlinkExteriorPlanarNeckIntervalCapHomeomorphProductFourBall

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafIntervalCapHomeomorphProductFourBall_inl
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarLeftLeafIntervalCapHomeomorphProductFourBall m a
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).rightToTopRight
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).rightToBottomRight (t,
            b)) =
      (unitIntervalToEuclideanClosedBallOne t, b) := by
  change ((coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
    coordinateUnlinkExteriorPlanarLeftCappingGridRightToTopRight).trans
    coordinateUnlinkExteriorPlanarNeckIntervalCapHomeomorphProductFourBall)
      (topologicalPushoutInl coordinateUnlinkExteriorPlanarLeftCappingGridRightToTopRight
        (ContinuousMap.id CoordinateUnlinkExteriorPlanarLeftCappingGridBR) (t, b)) = _
  rw [Homeomorph.trans_apply]
  change coordinateUnlinkExteriorPlanarNeckIntervalCapHomeomorphProductFourBall
      (coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
        coordinateUnlinkExteriorPlanarLeftCappingGridRightToTopRight
        (topologicalPushoutInl coordinateUnlinkExteriorPlanarLeftCappingGridRightToTopRight
          (ContinuousMap.id CoordinateUnlinkExteriorPlanarLeftCappingGridBR) (t, b))) = _
  rw [coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph_inl,
    coordinateUnlinkExteriorPlanarNeckIntervalCapHomeomorphProductFourBall_apply]

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafIntervalCapHomeomorphProductFourBall_inr
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarLeftLeafIntervalCapHomeomorphProductFourBall m a
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).rightToTopRight
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).rightToBottomRight (t,
            s)) =
      (unitIntervalToEuclideanClosedBallOne t,
        coordinateUnlinkExteriorPlanarNeckGridSphereToBall s) := by
  change ((coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
    coordinateUnlinkExteriorPlanarLeftCappingGridRightToTopRight).trans
    coordinateUnlinkExteriorPlanarNeckIntervalCapHomeomorphProductFourBall)
      (topologicalPushoutInr coordinateUnlinkExteriorPlanarLeftCappingGridRightToTopRight
        (ContinuousMap.id CoordinateUnlinkExteriorPlanarLeftCappingGridBR) (t, s)) = _
  rw [Homeomorph.trans_apply]
  change coordinateUnlinkExteriorPlanarNeckIntervalCapHomeomorphProductFourBall
      (coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
        coordinateUnlinkExteriorPlanarLeftCappingGridRightToTopRight
        (topologicalPushoutInr coordinateUnlinkExteriorPlanarLeftCappingGridRightToTopRight
          (ContinuousMap.id CoordinateUnlinkExteriorPlanarLeftCappingGridBR) (t, s))) = _
  rw [coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph_inr,
    coordinateUnlinkExteriorPlanarNeckIntervalCapHomeomorphProductFourBall_apply]
  rfl

def coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalBottomHomeomorph
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalBottom ≃ₜ
      CoordinateUnlinkExteriorPlanarRightNodeCappingGridFR :=
  coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomRight m)

def coordinateUnlinkExteriorPlanarRightNodeCapFamilyCollapseHomeomorph
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).verticalLeft ≃ₜ
      CoordinateUnlinkExteriorPlanarRightNodeCappingGridHL m :=
  coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridLeftToTopLeft m)

/- Exact row-recognition compatibility, shown here for the fixed left leaf. -/

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph_inl
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph m a
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToLeft
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToRight (w, s)) =
      (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap w, s) := by
  let _ : T2Space CoordinateUnlinkExteriorPlanarLeftLeafBoundaryPushout :=
    (coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph m a).symm.t2Space
  change (((topologicalPushoutProductHomeomorph
      coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
      coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam (Sphere 2)
      injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
      injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam).trans
      ((coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph m a).prodCongr
        (Homeomorph.refl (Sphere 2))))
    (topologicalPushoutInl
      (coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc.prodMap
        (ContinuousMap.id (Sphere 2)))
      (coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam.prodMap
        (ContinuousMap.id (Sphere 2))) (w, s))) = _
  rw [Homeomorph.trans_apply,
    topologicalPushoutProductHomeomorph_inl]
  exact Prod.ext
    (coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph_inl m a w) rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph_inr
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph m a
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToLeft
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToRight (t, s)) =
      (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a t, s) := by
  let _ : T2Space CoordinateUnlinkExteriorPlanarLeftLeafBoundaryPushout :=
    (coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph m a).symm.t2Space
  change (((topologicalPushoutProductHomeomorph
      coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
      coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam (Sphere 2)
      injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc
      injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam).trans
      ((coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph m a).prodCongr
        (Homeomorph.refl (Sphere 2))))
    (topologicalPushoutInr
      (coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc.prodMap
        (ContinuousMap.id (Sphere 2)))
      (coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam.prodMap
        (ContinuousMap.id (Sphere 2))) (t, s))) = _
  rw [Homeomorph.trans_apply,
    topologicalPushoutProductHomeomorph_inr]
  exact Prod.ext
    (coordinateUnlinkExteriorPlanarLeftLeafBoundaryPushoutHomeomorph_inr m a t) rfl

theorem coordinateUnlinkExteriorPlanarLeftLeafCappingGridTopCompatibility
    (m : ℕ) [NeZero m] (a : ZMod m)
    (z : (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddle) :
    coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalTopHomeomorph m a
        ((coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToTop z) =
      oneHandleBoundaryInclusion
        (coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph m a z) := by
  rcases topologicalPushout_jointly_surjective
      (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToLeft
      (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToRight z with
    ⟨⟨w, s⟩, rfl⟩ | ⟨⟨t, s⟩, rfl⟩
  · rw [(coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToTop_inl,
      (show (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).leftToTopLeft (w, s) =
        (w, coordinateUnlinkExteriorPlanarNeckGridSphereToBall s) from rfl)]
    change coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph m a
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc.prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          (coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam.prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          (w, coordinateUnlinkExteriorPlanarNeckGridSphereToBall s)) = _
    rw [coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph_inl,
      coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph_inl,
        oneHandleBoundaryInclusion_apply]
    rfl
  · rw [(coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToTop_inr,
      (show (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).rightToTopRight (t, s)
        =
        (t, coordinateUnlinkExteriorPlanarNeckGridSphereToBall s) from rfl)]
    change coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph m a
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc.prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          (coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam.prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          (t, coordinateUnlinkExteriorPlanarNeckGridSphereToBall s)) = _
    rw [coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph_inr,
      coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph_inr,
        oneHandleBoundaryInclusion_apply]
    rfl

theorem coordinateUnlinkExteriorPlanarLeftLeafCappingGridBottomCompatibility
    (m : ℕ) [NeZero m] (a : ZMod m)
    (z : (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddle) :
    coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalBottomHomeomorph m a
        ((coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToBottom
          z) =
      partialSphereSpinBoundaryInclusion partialSphereSpinAnnulusOne
        (coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph m a z) := by
  rcases topologicalPushout_jointly_surjective
      (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToLeft
      (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).centerToRight z with
    ⟨⟨w, s⟩, rfl⟩ | ⟨⟨t, s⟩, rfl⟩
  · rw [(coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m
    a).horizontalMiddleToBottom_inl,
      (show (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).leftToBottomLeft (w, s)
        =
        (partialSphereSpinAnnulusOne
          (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap w), s) from rfl)]
    change coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
      (coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomLeft m a)
        (topologicalPushoutInl (coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomLeft m
          a) (ContinuousMap.id CoordinateUnlinkExteriorPlanarLeftCappingGridA)
          (partialSphereSpinAnnulusOne
            (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap w), s)) = _
    rw [coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph_inl,
      coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph_inl,
      partialSphereSpinBoundaryInclusion_apply]
  · rw [(coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m
    a).horizontalMiddleToBottom_inr,
      (show (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).rightToBottomRight (t,
        s) = (t, s) from rfl)]
    change coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
      (coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomLeft m a)
        (topologicalPushoutInr (coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomLeft m
          a) (ContinuousMap.id CoordinateUnlinkExteriorPlanarLeftCappingGridA) (t, s)) = _
    rw [coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph_inr,
      coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph_inr,
      partialSphereSpinBoundaryInclusion_apply]
    rfl

def coordinateUnlinkExteriorPlanarLeftLeafCappingGridRowHomeomorphPartialSphereSpin
    (m : ℕ) [NeZero m] (a : ZMod m) :
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).rowFirst ≃ₜ
      PartialSphereSpin partialSphereSpinAnnulusOne :=
  topologicalPushoutCongr
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToTop
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToBottom
    oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion partialSphereSpinAnnulusOne)
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalMiddleHomeomorph m a)
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalTopHomeomorph m a)
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalBottomHomeomorph m a)
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridTopCompatibility m a)
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridBottomCompatibility m a)

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafCappingGridRowHomeomorphPartialSphereSpin_inl
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalTop) :
    coordinateUnlinkExteriorPlanarLeftLeafCappingGridRowHomeomorphPartialSphereSpin m a
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToTop
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToBottom
            x) =
      partialSphereSpinInl partialSphereSpinAnnulusOne
        (coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalTopHomeomorph m a x) := by
  apply topologicalPushoutCongr_inl

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafCappingGridRowHomeomorphPartialSphereSpin_inr
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalBottom) :
    coordinateUnlinkExteriorPlanarLeftLeafCappingGridRowHomeomorphPartialSphereSpin m a
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToTop
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToBottom
            x) =
      partialSphereSpinInr partialSphereSpinAnnulusOne
        (coordinateUnlinkExteriorPlanarLeftLeafCappingGridHorizontalBottomHomeomorph m a x) := by
  apply topologicalPushoutCongr_inr

/-- Capping the neck of one normalized left leaf produces the point-set one-handle model. -/
def coordinateUnlinkExteriorPlanarLeftLeafCappedHomeomorphOneHandle
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorPlanarLeftLeafCapped m a ≃ₜ OneHandlePiece :=
  (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m
    a).topologicalPushoutGridHomeomorph.symm |>.trans
    ((coordinateUnlinkExteriorPlanarLeftLeafCappingGridRowHomeomorphPartialSphereSpin m a).trans
      partialSphereSpinAnnulusOneHomeomorphOneHandle)

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafCappedHomeomorphOneHandle_topLeft
    (m : ℕ) [NeZero m] (a : ZMod m)
    (w : CoordinateUnlinkExteriorPlanarBaseLeftOuterArc)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarLeftLeafCappedHomeomorphOneHandle m a
        ((coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).columnFirstTopLeft (w, b))
          =
      partialSphereSpinAnnulusOneHandleMap
        (coordinateUnlinkExteriorPlanarLeftLeafOuterCircleMap w, b) := by
  rw [coordinateUnlinkExteriorPlanarLeftLeafCappedHomeomorphOneHandle, Homeomorph.trans_apply,
    Homeomorph.trans_apply,
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m
      a).topologicalPushoutGridHomeomorph_symm_apply_topLeft]
  change partialSphereSpinAnnulusOneHomeomorphOneHandle
      (coordinateUnlinkExteriorPlanarLeftLeafCappingGridRowHomeomorphPartialSphereSpin m a
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToTop
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToBottom
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).topToTopLeft
            (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).topToTopRight (w, b))))
              = _
  rw [coordinateUnlinkExteriorPlanarLeftLeafCappingGridRowHomeomorphPartialSphereSpin_inl,
    partialSphereSpinAnnulusOneHomeomorphOneHandle_inl]
  change partialSphereSpinAnnulusOneHandleMap
      (coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph m a
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc.prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          (coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam.prodMap
            (ContinuousMap.id (EuclideanClosedBall 3))) (w, b))) = _
  rw [coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph_inl]

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafCappedHomeomorphOneHandle_topRight
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarLeftLeafCappedHomeomorphOneHandle m a
        ((coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).columnFirstTopRight (t,
          b)) =
      partialSphereSpinAnnulusOneHandleMap
        (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a t, b) := by
  rw [coordinateUnlinkExteriorPlanarLeftLeafCappedHomeomorphOneHandle, Homeomorph.trans_apply,
    Homeomorph.trans_apply,
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m
      a).topologicalPushoutGridHomeomorph_symm_apply_topRight]
  change partialSphereSpinAnnulusOneHomeomorphOneHandle
      (coordinateUnlinkExteriorPlanarLeftLeafCappingGridRowHomeomorphPartialSphereSpin m a
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToTop
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToBottom
          (topologicalPushoutInr
            (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).topToTopLeft
            (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).topToTopRight (t, b))))
              = _
  rw [coordinateUnlinkExteriorPlanarLeftLeafCappingGridRowHomeomorphPartialSphereSpin_inl,
    partialSphereSpinAnnulusOneHomeomorphOneHandle_inl]
  change partialSphereSpinAnnulusOneHandleMap
      (coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph m a
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc.prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          (coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam.prodMap
            (ContinuousMap.id (EuclideanClosedBall 3))) (t, b))) = _
  rw [coordinateUnlinkExteriorPlanarLeftLeafOneHandleSplitPushoutHomeomorph_inr]

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafCappedHomeomorphOneHandle_bottomLeft
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : PartialSphereSpinAnnulus) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarLeftLeafCappedHomeomorphOneHandle m a
        ((coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).columnFirstBottomLeft (x,
          s)) =
      partialSphereSpinAnnulusShellMap
        (partialSphereSpinAnnulusReverseHomeomorph x, s) := by
  rw [coordinateUnlinkExteriorPlanarLeftLeafCappedHomeomorphOneHandle, Homeomorph.trans_apply,
    Homeomorph.trans_apply,
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m
      a).topologicalPushoutGridHomeomorph_symm_apply_bottomLeft]
  change partialSphereSpinAnnulusOneHomeomorphOneHandle
      (coordinateUnlinkExteriorPlanarLeftLeafCappingGridRowHomeomorphPartialSphereSpin m a
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToTop
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToBottom
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).bottomToBottomLeft
            (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).bottomToBottomRight (x,
              s)))) = _
  rw [coordinateUnlinkExteriorPlanarLeftLeafCappingGridRowHomeomorphPartialSphereSpin_inr,
    partialSphereSpinAnnulusOneHomeomorphOneHandle_inr]
  change partialSphereSpinAnnulusShellMap
      (partialSphereSpinAnnulusReverseHomeomorph
        (coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
          (coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomLeft m a)
          (topologicalPushoutInl (coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomLeft
            m a) (ContinuousMap.id CoordinateUnlinkExteriorPlanarLeftCappingGridA) (x, s))).1,
        (coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
          (coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomLeft m a)
          (topologicalPushoutInl (coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomLeft
            m a) (ContinuousMap.id CoordinateUnlinkExteriorPlanarLeftCappingGridA) (x, s))).2) = _
  rw [coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph_inl]

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftLeafCappedHomeomorphOneHandle_bottomRight
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarLeftLeafCappedHomeomorphOneHandle m a
        ((coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).columnFirstBottomRight (t,
          s)) =
      partialSphereSpinAnnulusShellMap
        (partialSphereSpinAnnulusReverseHomeomorph
          (partialSphereSpinAnnulusOne
            (coordinateUnlinkExteriorPlanarLeftLeafSeamCircleMap m a t)), s) := by
  rw [coordinateUnlinkExteriorPlanarLeftLeafCappedHomeomorphOneHandle, Homeomorph.trans_apply,
    Homeomorph.trans_apply,
    (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m
      a).topologicalPushoutGridHomeomorph_symm_apply_bottomRight]
  change partialSphereSpinAnnulusOneHomeomorphOneHandle
      (coordinateUnlinkExteriorPlanarLeftLeafCappingGridRowHomeomorphPartialSphereSpin m a
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToTop
          (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).horizontalMiddleToBottom
          (topologicalPushoutInr
            (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).bottomToBottomLeft
            (coordinateUnlinkExteriorPlanarLeftLeafCappingGridDiagram m a).bottomToBottomRight (t,
              s)))) = _
  rw [coordinateUnlinkExteriorPlanarLeftLeafCappingGridRowHomeomorphPartialSphereSpin_inr,
    partialSphereSpinAnnulusOneHomeomorphOneHandle_inr]
  change partialSphereSpinAnnulusShellMap
      (partialSphereSpinAnnulusReverseHomeomorph
        (coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
          (coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomLeft m a)
          (topologicalPushoutInr (coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomLeft
            m a) (ContinuousMap.id CoordinateUnlinkExteriorPlanarLeftCappingGridA) (t, s))).1,
        (coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
          (coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomLeft m a)
          (topologicalPushoutInr (coordinateUnlinkExteriorPlanarLeftCappingGridBottomToBottomLeft
            m a) (ContinuousMap.id CoordinateUnlinkExteriorPlanarLeftCappingGridA) (t, s))).2) = _
  rw [coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph_inr]
  rfl

/- The same row recognition for the right node, with all neck labels retained simultaneously. -/

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalMiddleHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalMiddleHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).centerToLeft
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).centerToRight (x, s)) =
      (coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle m x, s) := by
  let _ : T2Space (CoordinateUnlinkExteriorPlanarRightNodeBoundaryPushout m) :=
    (coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph m).symm.t2Space
  change (((topologicalPushoutProductHomeomorph
      (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m)
      (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m) (Sphere 2)
      (injective_coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m)
      (injective_coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m)).trans
      ((coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph m).prodCongr
        (Homeomorph.refl (Sphere 2))))
    (topologicalPushoutInl
      ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m).prodMap
        (ContinuousMap.id (Sphere 2)))
      ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
        (ContinuousMap.id (Sphere 2))) (x, s))) = _
  rw [Homeomorph.trans_apply, topologicalPushoutProductHomeomorph_inl]
  exact Prod.ext
    (coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph_inl m x) rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalMiddleHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalMiddleHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).centerToLeft
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).centerToRight (x, s)) =
      (coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m x, s) := by
  let _ : T2Space (CoordinateUnlinkExteriorPlanarRightNodeBoundaryPushout m) :=
    (coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph m).symm.t2Space
  change (((topologicalPushoutProductHomeomorph
      (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m)
      (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m) (Sphere 2)
      (injective_coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m)
      (injective_coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m)).trans
      ((coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph m).prodCongr
        (Homeomorph.refl (Sphere 2))))
    (topologicalPushoutInr
      ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m).prodMap
        (ContinuousMap.id (Sphere 2)))
      ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
        (ContinuousMap.id (Sphere 2))) (x, s))) = _
  rw [Homeomorph.trans_apply, topologicalPushoutProductHomeomorph_inr]
  exact Prod.ext
    (coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph_inr m x) rfl

theorem coordinateUnlinkExteriorPlanarRightNodeCappingGridTopCompatibility
    (m : ℕ) [NeZero m]
    (z : (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddle) :
    coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalTopHomeomorph m
        ((coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToTop z) =
      oneHandleBoundaryInclusion
        (coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalMiddleHomeomorph m z) := by
  rcases topologicalPushout_jointly_surjective
      (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).centerToLeft
      (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).centerToRight z with
    ⟨⟨x, s⟩, rfl⟩ | ⟨⟨x, s⟩, rfl⟩
  · rw [(coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToTop_inl,
      (show (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).leftToTopLeft (x, s) =
        (x, coordinateUnlinkExteriorPlanarNeckGridSphereToBall s) from rfl)]
    change coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph m
        (topologicalPushoutInl
          ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          (x, coordinateUnlinkExteriorPlanarNeckGridSphereToBall s)) = _
    rw [coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph_inl,
      coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalMiddleHomeomorph_inl,
        oneHandleBoundaryInclusion_apply]
    rfl
  · rw [(coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToTop_inr,
      (show (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).rightToTopRight (x, s) =
        (x, coordinateUnlinkExteriorPlanarNeckGridSphereToBall s) from rfl)]
    change coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph m
        (topologicalPushoutInr
          ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          (x, coordinateUnlinkExteriorPlanarNeckGridSphereToBall s)) = _
    rw [coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph_inr,
      coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalMiddleHomeomorph_inr,
        oneHandleBoundaryInclusion_apply]
    rfl

theorem coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomCompatibility
    (m : ℕ) [NeZero m]
    (z : (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddle) :
    coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalBottomHomeomorph m
        ((coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToBottom z)
          =
      partialSphereSpinBoundaryInclusion partialSphereSpinAnnulusOne
        (coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalMiddleHomeomorph m z) := by
  rcases topologicalPushout_jointly_surjective
      (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).centerToLeft
      (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).centerToRight z with
    ⟨⟨x, s⟩, rfl⟩ | ⟨⟨x, s⟩, rfl⟩
  · rw [(coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram
    m).horizontalMiddleToBottom_inl,
      (show (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).leftToBottomLeft (x, s)
        = (x, s) from rfl)]
    change coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph
      (coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomRight m)
        (topologicalPushoutInl (ContinuousMap.id
          (CoordinateUnlinkExteriorPlanarRightNodeCappingGridA m))
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomRight m) (x, s)) = _
    rw [coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph_inl,
      coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalMiddleHomeomorph_inl,
      partialSphereSpinBoundaryInclusion_apply]
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact coordinateUnlinkExteriorPlanarNormalizedRightSeam_time m x
    · rfl
  · rw [(coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram
    m).horizontalMiddleToBottom_inr]
    change coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph
      (coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomRight m)
        (topologicalPushoutInr (ContinuousMap.id
          (CoordinateUnlinkExteriorPlanarRightNodeCappingGridA m))
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomRight m)
          ((coordinateUnlinkExteriorPlanarNeckGridRightOuterToNormalizedRight m x), s)) = _
    rw [coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph_inr,
      coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalMiddleHomeomorph_inr,
      partialSphereSpinBoundaryInclusion_apply]
    rfl

def coordinateUnlinkExteriorPlanarRightNodeCappingGridRowHomeomorphPartialSphereSpin
    (m : ℕ) [NeZero m] :
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).rowFirst ≃ₜ
      PartialSphereSpin partialSphereSpinAnnulusOne :=
  topologicalPushoutCongr
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToTop
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToBottom
    oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion partialSphereSpinAnnulusOne)
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalMiddleHomeomorph m)
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalTopHomeomorph m)
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalBottomHomeomorph m)
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridTopCompatibility m)
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomCompatibility m)

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeCappingGridRowHomeomorphPartialSphereSpin_inl
    (m : ℕ) [NeZero m]
    (x : (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalTop) :
    coordinateUnlinkExteriorPlanarRightNodeCappingGridRowHomeomorphPartialSphereSpin m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToTop
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToBottom
            x) =
      partialSphereSpinInl partialSphereSpinAnnulusOne
        (coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalTopHomeomorph m x) := by
  apply topologicalPushoutCongr_inl

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeCappingGridRowHomeomorphPartialSphereSpin_inr
    (m : ℕ) [NeZero m]
    (x : (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalBottom) :
    coordinateUnlinkExteriorPlanarRightNodeCappingGridRowHomeomorphPartialSphereSpin m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToTop
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToBottom
            x) =
      partialSphereSpinInr partialSphereSpinAnnulusOne
        (coordinateUnlinkExteriorPlanarRightNodeCappingGridHorizontalBottomHomeomorph m x) := by
  apply topologicalPushoutCongr_inr

/-- Simultaneously capping every labelled neck of the normalized right node produces the
point-set one-handle model. -/
def coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarRightNodeCapped m ≃ₜ OneHandlePiece :=
  (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram
    m).topologicalPushoutGridHomeomorph.symm |>.trans
    ((coordinateUnlinkExteriorPlanarRightNodeCappingGridRowHomeomorphPartialSphereSpin m).trans
      partialSphereSpinAnnulusOneHomeomorphOneHandle)

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle_topLeft
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle m
        ((coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).columnFirstTopLeft (x, b))
          =
      partialSphereSpinAnnulusOneHandleMap
        (coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle m x, b) := by
  rw [coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle, Homeomorph.trans_apply,
    Homeomorph.trans_apply,
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram
      m).topologicalPushoutGridHomeomorph_symm_apply_topLeft]
  change partialSphereSpinAnnulusOneHomeomorphOneHandle
      (coordinateUnlinkExteriorPlanarRightNodeCappingGridRowHomeomorphPartialSphereSpin m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToTop
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToBottom
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).topToTopLeft
            (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).topToTopRight (x, b))))
              = _
  rw [coordinateUnlinkExteriorPlanarRightNodeCappingGridRowHomeomorphPartialSphereSpin_inl,
    partialSphereSpinAnnulusOneHomeomorphOneHandle_inl]
  change partialSphereSpinAnnulusOneHandleMap
      (coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph m
        (topologicalPushoutInl
          ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3))) (x, b))) = _
  rw [coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph_inl]

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle_topRight
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle m
        ((coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).columnFirstTopRight (x, b))
          =
      partialSphereSpinAnnulusOneHandleMap
        (coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m x, b) := by
  rw [coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle, Homeomorph.trans_apply,
    Homeomorph.trans_apply,
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram
      m).topologicalPushoutGridHomeomorph_symm_apply_topRight]
  change partialSphereSpinAnnulusOneHomeomorphOneHandle
      (coordinateUnlinkExteriorPlanarRightNodeCappingGridRowHomeomorphPartialSphereSpin m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToTop
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToBottom
          (topologicalPushoutInr
            (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).topToTopLeft
            (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).topToTopRight (x, b))))
              = _
  rw [coordinateUnlinkExteriorPlanarRightNodeCappingGridRowHomeomorphPartialSphereSpin_inl,
    partialSphereSpinAnnulusOneHomeomorphOneHandle_inl]
  change partialSphereSpinAnnulusOneHandleMap
      (coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph m
        (topologicalPushoutInr
          ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3))) (x, b))) = _
  rw [coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph_inr]

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle_bottomLeft
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle m
        ((coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).columnFirstBottomLeft (x,
          s)) =
      partialSphereSpinAnnulusShellMap
        (partialSphereSpinAnnulusReverseHomeomorph
          (coordinateUnlinkExteriorPlanarNormalizedRightSeam m x), s) := by
  rw [coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle, Homeomorph.trans_apply,
    Homeomorph.trans_apply,
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram
      m).topologicalPushoutGridHomeomorph_symm_apply_bottomLeft]
  change partialSphereSpinAnnulusOneHomeomorphOneHandle
      (coordinateUnlinkExteriorPlanarRightNodeCappingGridRowHomeomorphPartialSphereSpin m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToTop
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToBottom
          (topologicalPushoutInl
            (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).bottomToBottomLeft
            (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).bottomToBottomRight (x,
              s)))) = _
  rw [coordinateUnlinkExteriorPlanarRightNodeCappingGridRowHomeomorphPartialSphereSpin_inr,
    partialSphereSpinAnnulusOneHomeomorphOneHandle_inr]
  change partialSphereSpinAnnulusShellMap
      (partialSphereSpinAnnulusReverseHomeomorph
        (coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomRight m)
          (topologicalPushoutInl (ContinuousMap.id
            (CoordinateUnlinkExteriorPlanarRightNodeCappingGridA m))
            (coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomRight m) (x, s))).1,
        (coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomRight m)
          (topologicalPushoutInl (ContinuousMap.id
            (CoordinateUnlinkExteriorPlanarRightNodeCappingGridA m))
            (coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomRight m) (x, s))).2)
              = _
  rw [coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph_inl]
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle_bottomRight
    (m : ℕ) [NeZero m]
    (y : CoordinateUnlinkExteriorPlanarNormalizedRightHalf) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle m
        ((coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).columnFirstBottomRight (y,
          s)) =
      partialSphereSpinAnnulusShellMap
        (partialSphereSpinAnnulusReverseHomeomorph y, s) := by
  rw [coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle, Homeomorph.trans_apply,
    Homeomorph.trans_apply,
    (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram
      m).topologicalPushoutGridHomeomorph_symm_apply_bottomRight]
  change partialSphereSpinAnnulusOneHomeomorphOneHandle
      (coordinateUnlinkExteriorPlanarRightNodeCappingGridRowHomeomorphPartialSphereSpin m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToTop
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).horizontalMiddleToBottom
          (topologicalPushoutInr
            (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).bottomToBottomLeft
            (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).bottomToBottomRight (y,
              s)))) = _
  rw [coordinateUnlinkExteriorPlanarRightNodeCappingGridRowHomeomorphPartialSphereSpin_inr,
    partialSphereSpinAnnulusOneHomeomorphOneHandle_inr]
  change partialSphereSpinAnnulusShellMap
      (partialSphereSpinAnnulusReverseHomeomorph
        (coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomRight m)
          (topologicalPushoutInr (ContinuousMap.id
            (CoordinateUnlinkExteriorPlanarRightNodeCappingGridA m))
            (coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomRight m) (y, s))).1,
        (coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomRight m)
          (topologicalPushoutInr (ContinuousMap.id
            (CoordinateUnlinkExteriorPlanarRightNodeCappingGridA m))
            (coordinateUnlinkExteriorPlanarRightNodeCappingGridBottomToBottomRight m) (y, s))).2)
              = _
  rw [coordinateUnlinkExteriorPlanarNeckCappingPushoutLeftIdentityHomeomorph_inr]

/-- The simultaneous cap column is exactly a `ZMod m`-labelled family of product four-balls. -/
def coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarRightNodeCapFamily m ≃ₜ ZMod m × ProductFourBall :=
  (coordinateUnlinkExteriorPlanarRightNodeCapFamilyCollapseHomeomorph m).trans <|
    (Homeomorph.prodAssoc (ZMod m) CoordinateUnlinkExteriorPlanarNeckInterval
      (EuclideanClosedBall 3)).trans
      ((Homeomorph.refl (ZMod m)).prodCongr
        coordinateUnlinkExteriorPlanarNeckIntervalCapHomeomorphProductFourBall)

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).leftToTopLeft
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).leftToBottomLeft (x, b)) =
      (x.1, (unitIntervalToEuclideanClosedBallOne x.2, b)) := by
  rw [coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph, Homeomorph.trans_apply,
    Homeomorph.trans_apply]
  change ((Homeomorph.refl (ZMod m)).prodCongr
    coordinateUnlinkExteriorPlanarNeckIntervalCapHomeomorphProductFourBall)
      ((Homeomorph.prodAssoc (ZMod m) CoordinateUnlinkExteriorPlanarNeckInterval
        (EuclideanClosedBall 3))
        (coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridLeftToTopLeft m)
          (topologicalPushoutInl (coordinateUnlinkExteriorPlanarRightNodeCappingGridLeftToTopLeft
            m) (ContinuousMap.id (CoordinateUnlinkExteriorPlanarRightNodeCappingGridBL m))
            (x, b)))) = _
  rw [coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph_inl]
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).leftToTopLeft
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridDiagram m).leftToBottomLeft (x, s)) =
      (x.1, (unitIntervalToEuclideanClosedBallOne x.2,
        coordinateUnlinkExteriorPlanarNeckGridSphereToBall s)) := by
  rw [coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph, Homeomorph.trans_apply,
    Homeomorph.trans_apply]
  change ((Homeomorph.refl (ZMod m)).prodCongr
    coordinateUnlinkExteriorPlanarNeckIntervalCapHomeomorphProductFourBall)
      ((Homeomorph.prodAssoc (ZMod m) CoordinateUnlinkExteriorPlanarNeckInterval
        (EuclideanClosedBall 3))
        (coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph
          (coordinateUnlinkExteriorPlanarRightNodeCappingGridLeftToTopLeft m)
          (topologicalPushoutInr (coordinateUnlinkExteriorPlanarRightNodeCappingGridLeftToTopLeft
            m) (ContinuousMap.id (CoordinateUnlinkExteriorPlanarRightNodeCappingGridBL m))
            (x, s)))) = _
  rw [coordinateUnlinkExteriorPlanarNeckCappingPushoutRightIdentityHomeomorph_inr]
  rfl
end SplittingSpheres
