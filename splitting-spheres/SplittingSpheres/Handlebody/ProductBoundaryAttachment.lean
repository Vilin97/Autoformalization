/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutHomeomorph
public import SplittingSpheres.Handlebody.BoundaryAttachment
public import SplittingSpheres.Handlebody.ProductFiveBall

/-!
# The cap attachment as the boundary of `D² × B³`

The boundary of the product body `D² × B³` is the union of its two faces
`S¹ × B³` and `D² × S²`, meeting along `S¹ × S²`.  This file proves that the literal
topological pushout constructed in `BoundaryAttachment.lean` is homeomorphic to that boundary.
Composing with the convex radial identification from `ProductFiveBall.lean` gives an honest
homeomorphism with the project's literal `Sphere 4`.

This remains a topological calculation.  Neither homeomorphism is claimed to be a smooth
diffeomorphism, and the pushout is not given a manifold structure here.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped Topology

namespace SplittingSpheres

/-- The `S¹ × B³` face inside the model boundary of `D² × B³`. -/
def oneHandlePieceToProductFiveBallBoundary :
    C(OneHandlePiece, ProductFiveBallBoundary) where
  toFun x :=
    ⟨(⟨x.1.1, sphere_subset_closedBall x.1.2⟩, x.2), by
      apply (Set.ext_iff.mp productFiveBallModel_boundary _).mpr
      exact Or.inr ⟨x.1.2, mem_univ _⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd

/-- The `D² × S²` face inside the model boundary of `D² × B³`. -/
def capPieceToProductFiveBallBoundary :
    C(CapPiece, ProductFiveBallBoundary) where
  toFun x :=
    ⟨(x.1, ⟨x.2.1, sphere_subset_closedBall x.2.2⟩), by
      apply (Set.ext_iff.mp productFiveBallModel_boundary _).mpr
      exact Or.inl ⟨mem_univ _, x.2.2⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk <|
      (continuous_subtype_val.comp continuous_snd).subtype_mk _

@[simp]
theorem oneHandlePieceToProductFiveBallBoundary_apply_val (x : OneHandlePiece) :
    (oneHandlePieceToProductFiveBallBoundary x : ProductFiveBall) =
      (⟨x.1.1, sphere_subset_closedBall x.1.2⟩, x.2) :=
  rfl

@[simp]
theorem capPieceToProductFiveBallBoundary_apply_val (x : CapPiece) :
    (capPieceToProductFiveBallBoundary x : ProductFiveBall) =
      (x.1, ⟨x.2.1, sphere_subset_closedBall x.2.2⟩) :=
  rfl

/-- The two face maps agree exactly on the chosen common-boundary coordinates. -/
theorem productFiveBallFace_compatibility (z : OneHandleCapBoundary) :
    oneHandlePieceToProductFiveBallBoundary (oneHandleBoundaryInclusion z) =
      capPieceToProductFiveBallBoundary (capBoundaryInclusion z) := by
  apply Subtype.ext
  rfl

theorem oneHandlePieceToProductFiveBallBoundary_injective :
    Injective oneHandlePieceToProductFiveBallBoundary := by
  intro x y h
  have hval := congr_arg Subtype.val h
  apply Prod.ext
  · apply Subtype.ext
    exact congr_arg (fun z : EuclideanClosedBall 2 ↦ z.1)
      (congr_arg (fun z : ProductFiveBall ↦ z.1) hval)
  · exact congr_arg (fun z : ProductFiveBall ↦ z.2) hval

theorem capPieceToProductFiveBallBoundary_injective :
    Injective capPieceToProductFiveBallBoundary := by
  intro x y h
  have hval := congr_arg Subtype.val h
  apply Prod.ext
  · exact congr_arg (fun z : ProductFiveBall ↦ z.1) hval
  · apply Subtype.ext
    exact congr_arg (fun z : EuclideanClosedBall 3 ↦ z.1)
      (congr_arg (fun z : ProductFiveBall ↦ z.2) hval)

/-- A cross-face equality in the product boundary comes from a common-boundary point. -/
theorem productFiveBallFaces_cross_overlap (x : OneHandlePiece) (y : CapPiece)
    (h : oneHandlePieceToProductFiveBallBoundary x =
      capPieceToProductFiveBallBoundary y) :
    ∃ z : OneHandleCapBoundary,
      oneHandleBoundaryInclusion z = x ∧ capBoundaryInclusion z = y := by
  have hval := congr_arg Subtype.val h
  have hfst := congr_arg Prod.fst hval
  have hsnd := congr_arg Prod.snd hval
  refine ⟨(x.1, y.2), ?_, ?_⟩
  · exact Prod.ext rfl hsnd.symm
  · exact Prod.ext hfst rfl

/-- The two product-boundary faces cover the entire model boundary. -/
theorem range_productFiveBallFaces :
    range oneHandlePieceToProductFiveBallBoundary ∪
      range capPieceToProductFiveBallBoundary = univ := by
  ext z
  constructor
  · exact fun _ ↦ mem_univ z
  · intro _
    have hz : z.1 ∈ productFiveBallBoundarySet :=
      (Set.ext_iff.mp productFiveBallModel_boundary z.1).mp z.2
    rcases hz with hz | hz
    · apply Or.inr
      let y : CapPiece := (z.1.1, ⟨z.1.2.1, hz.2⟩)
      refine ⟨y, ?_⟩
      apply Subtype.ext
      exact Prod.ext rfl (Subtype.ext rfl)
    · apply Or.inl
      let x : OneHandlePiece := (⟨z.1.1.1, hz.1⟩, z.1.2)
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact Prod.ext (Subtype.ext rfl) rfl

/-- The cap adjunction space is the literal model boundary of `D² × B³`. -/
def cappedOneHandleHomeomorphProductFiveBallBoundary :
    CappedOneHandle ≃ₜ ProductFiveBallBoundary :=
  topologicalPushoutHomeomorph
    oneHandleBoundaryInclusion capBoundaryInclusion
    oneHandlePieceToProductFiveBallBoundary capPieceToProductFiveBallBoundary
    productFiveBallFace_compatibility
    oneHandleBoundaryInclusion_injective
    oneHandlePieceToProductFiveBallBoundary_injective
    capPieceToProductFiveBallBoundary_injective
    productFiveBallFaces_cross_overlap
    range_productFiveBallFaces

@[simp]
theorem cappedOneHandleHomeomorphProductFiveBallBoundary_inl (x : OneHandlePiece) :
    cappedOneHandleHomeomorphProductFiveBallBoundary (cappedOneHandleInl x) =
      oneHandlePieceToProductFiveBallBoundary x :=
  topologicalPushoutHomeomorph_inl
    oneHandleBoundaryInclusion capBoundaryInclusion
    oneHandlePieceToProductFiveBallBoundary capPieceToProductFiveBallBoundary
    productFiveBallFace_compatibility
    oneHandleBoundaryInclusion_injective
    oneHandlePieceToProductFiveBallBoundary_injective
    capPieceToProductFiveBallBoundary_injective
    productFiveBallFaces_cross_overlap
    range_productFiveBallFaces x

@[simp]
theorem cappedOneHandleHomeomorphProductFiveBallBoundary_inr (x : CapPiece) :
    cappedOneHandleHomeomorphProductFiveBallBoundary (cappedOneHandleInr x) =
      capPieceToProductFiveBallBoundary x :=
  topologicalPushoutHomeomorph_inr
    oneHandleBoundaryInclusion capBoundaryInclusion
    oneHandlePieceToProductFiveBallBoundary capPieceToProductFiveBallBoundary
    productFiveBallFace_compatibility
    oneHandleBoundaryInclusion_injective
    oneHandlePieceToProductFiveBallBoundary_injective
    capPieceToProductFiveBallBoundary_injective
    productFiveBallFaces_cross_overlap
    range_productFiveBallFaces x

/-- The capped one-handle adjunction space is homeomorphic to the standard four-sphere. -/
def cappedOneHandleHomeomorphSphere : CappedOneHandle ≃ₜ Sphere 4 :=
  cappedOneHandleHomeomorphProductFiveBallBoundary.trans
    productFiveBallBoundaryHomeomorphSphere

@[simp]
theorem cappedOneHandleHomeomorphSphere_inl (x : OneHandlePiece) :
    cappedOneHandleHomeomorphSphere (cappedOneHandleInl x) =
      productFiveBallBoundaryHomeomorphSphere
        (oneHandlePieceToProductFiveBallBoundary x) := by
  change productFiveBallBoundaryHomeomorphSphere
    (cappedOneHandleHomeomorphProductFiveBallBoundary (cappedOneHandleInl x)) = _
  rw [cappedOneHandleHomeomorphProductFiveBallBoundary_inl]

@[simp]
theorem cappedOneHandleHomeomorphSphere_inr (x : CapPiece) :
    cappedOneHandleHomeomorphSphere (cappedOneHandleInr x) =
      productFiveBallBoundaryHomeomorphSphere
        (capPieceToProductFiveBallBoundary x) := by
  change productFiveBallBoundaryHomeomorphSphere
    (cappedOneHandleHomeomorphProductFiveBallBoundary (cappedOneHandleInr x)) = _
  rw [cappedOneHandleHomeomorphProductFiveBallBoundary_inr]

end SplittingSpheres
