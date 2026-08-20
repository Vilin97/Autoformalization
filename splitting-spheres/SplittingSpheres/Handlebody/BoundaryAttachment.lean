/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushout
public import SplittingSpheres.Handlebody.CapPiece
public import SplittingSpheres.Handlebody.OneHandlePiece

/-!
# Attaching `D² × S²` to `S¹ × B³`

The two compact pieces have canonically identified topological boundaries `S¹ × S²`.  This
file forms their literal pushout in `TopCat` and records its exact underlying-set behavior.

This is a topological adjunction space only.  No smooth structure on the pushout, smooth collar,
or smooth gluing theorem is asserted here.  A later module identifies this topological space with
the boundary of `D² × B³`, and hence with the standard four-sphere.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped Topology

namespace SplittingSpheres

/-- The common coordinate boundary used for the cap attachment. -/
abbrev OneHandleCapBoundary : Type := Sphere 1 × Sphere 2

/-- Include the common boundary in `S¹ × B³`. -/
def oneHandleBoundaryInclusion : C(OneHandleCapBoundary, OneHandlePiece) where
  toFun y := (y.1, ⟨y.2.1, sphere_subset_closedBall y.2.2⟩)
  continuous_toFun := continuous_fst.prodMk <|
    (continuous_subtype_val.comp continuous_snd).subtype_mk _

/-- Include the common boundary in `D² × S²`. -/
def capBoundaryInclusion : C(OneHandleCapBoundary, CapPiece) where
  toFun y := (⟨y.1.1, sphere_subset_closedBall y.1.2⟩, y.2)
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd

@[simp]
theorem oneHandleBoundaryInclusion_apply (y : OneHandleCapBoundary) :
    oneHandleBoundaryInclusion y = (y.1, ⟨y.2.1, sphere_subset_closedBall y.2.2⟩) :=
  rfl

@[simp]
theorem capBoundaryInclusion_apply (y : OneHandleCapBoundary) :
    capBoundaryInclusion y = (⟨y.1.1, sphere_subset_closedBall y.1.2⟩, y.2) :=
  rfl

/-- The coordinate inclusion agrees with the inverse of the canonical boundary homeomorphism
for the one-handle piece, followed by subtype inclusion. -/
theorem oneHandleBoundaryInclusion_eq_homeomorph (y : OneHandleCapBoundary) :
    oneHandleBoundaryInclusion y = (oneHandlePieceBoundaryHomeomorph.symm y).1 :=
  rfl

/-- The coordinate inclusion agrees with the inverse of the canonical boundary homeomorphism
for the cap piece, followed by subtype inclusion. -/
theorem capBoundaryInclusion_eq_homeomorph (y : OneHandleCapBoundary) :
    capBoundaryInclusion y = (capPieceBoundaryHomeomorph.symm y).1 :=
  rfl

theorem oneHandleBoundaryInclusion_injective : Injective oneHandleBoundaryInclusion := by
  intro x y h
  apply oneHandlePieceBoundaryHomeomorph.symm.injective
  apply Subtype.ext
  simpa only [oneHandleBoundaryInclusion_eq_homeomorph] using h

theorem capBoundaryInclusion_injective : Injective capBoundaryInclusion := by
  intro x y h
  apply capPieceBoundaryHomeomorph.symm.injective
  apply Subtype.ext
  simpa only [capBoundaryInclusion_eq_homeomorph] using h

/-- The topological space obtained by capping `S¹ × B³` with `D² × S²` along their
literal common `S¹ × S²` boundary. -/
abbrev CappedOneHandle : TopCat :=
  TopologicalPushout oneHandleBoundaryInclusion capBoundaryInclusion

/-- The one-handle piece inside the capped adjunction space. -/
abbrev cappedOneHandleInl : C(OneHandlePiece, CappedOneHandle) :=
  topologicalPushoutInl oneHandleBoundaryInclusion capBoundaryInclusion

/-- The cap piece inside the capped adjunction space. -/
abbrev cappedOneHandleInr : C(CapPiece, CappedOneHandle) :=
  topologicalPushoutInr oneHandleBoundaryInclusion capBoundaryInclusion

theorem cappedOneHandle_condition (y : OneHandleCapBoundary) :
    cappedOneHandleInl (oneHandleBoundaryInclusion y) =
      cappedOneHandleInr (capBoundaryInclusion y) :=
  topologicalPushout_condition oneHandleBoundaryInclusion capBoundaryInclusion y

theorem cappedOneHandleInl_injective : Injective cappedOneHandleInl :=
  topologicalPushoutInl_injective oneHandleBoundaryInclusion capBoundaryInclusion
    capBoundaryInclusion_injective

theorem cappedOneHandleInr_injective : Injective cappedOneHandleInr :=
  topologicalPushoutInr_injective oneHandleBoundaryInclusion capBoundaryInclusion
    oneHandleBoundaryInclusion_injective

/-- Cross-piece equality in the adjunction space occurs exactly on the common boundary. -/
theorem cappedOneHandleInl_eq_inr_iff (x : OneHandlePiece) (y : CapPiece) :
    cappedOneHandleInl x = cappedOneHandleInr y ↔
      ∃ z : OneHandleCapBoundary,
        oneHandleBoundaryInclusion z = x ∧ capBoundaryInclusion z = y :=
  topologicalPushoutInl_eq_inr_iff oneHandleBoundaryInclusion capBoundaryInclusion
    oneHandleBoundaryInclusion_injective x y

/-- The images of the two pieces cover the capped adjunction space. -/
theorem range_cappedOneHandleInl_union_range_cappedOneHandleInr :
    range cappedOneHandleInl ∪ range cappedOneHandleInr = univ :=
  range_topologicalPushoutInl_union_range_topologicalPushoutInr
    oneHandleBoundaryInclusion capBoundaryInclusion

/-- The images of the two pieces intersect in precisely their common boundary. -/
theorem range_cappedOneHandleInl_inter_range_cappedOneHandleInr :
    range cappedOneHandleInl ∩ range cappedOneHandleInr =
      range (fun z ↦ cappedOneHandleInl (oneHandleBoundaryInclusion z)) :=
  range_topologicalPushoutInl_inter_range_topologicalPushoutInr
    oneHandleBoundaryInclusion capBoundaryInclusion oneHandleBoundaryInclusion_injective

/-- The one-handle piece is path connected, packaged as an instance for the attachment API. -/
instance oneHandlePiecePathConnectedSpace : PathConnectedSpace OneHandlePiece :=
  pathConnectedSpace_iff_univ.mpr isPathConnected_oneHandlePiece

/-- The cap piece is path connected, packaged as an instance for the attachment API. -/
instance capPiecePathConnectedSpace : PathConnectedSpace CapPiece :=
  pathConnectedSpace_iff_univ.mpr isPathConnected_capPiece

/-- The common sphere-product boundary is nonempty. -/
instance oneHandleCapBoundaryNonempty : Nonempty OneHandleCapBoundary :=
  by
    obtain ⟨x⟩ :=
      (NormedSpace.sphere_nonempty
        (E := EuclideanSpace ℝ (Fin 2)) (x := 0) (r := 1) |>.mpr zero_le_one).to_subtype
    obtain ⟨y⟩ :=
      (NormedSpace.sphere_nonempty
        (E := EuclideanSpace ℝ (Fin 3)) (x := 0) (r := 1) |>.mpr zero_le_one).to_subtype
    exact ⟨(x, y)⟩

/-- The capped adjunction space is path connected. -/
instance cappedOneHandlePathConnectedSpace : PathConnectedSpace CappedOneHandle :=
  topologicalPushoutPathConnectedSpace oneHandleBoundaryInclusion capBoundaryInclusion

/-- The capped adjunction space is compact. -/
instance cappedOneHandleCompactSpace : CompactSpace CappedOneHandle :=
  topologicalPushoutCompactSpace oneHandleBoundaryInclusion capBoundaryInclusion

end SplittingSpheres
