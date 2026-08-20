/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import SplittingSpheres.Geometry.ClosedBall
public import SplittingSpheres.Statement

/-!
# The cap piece `D² × S²`

This file models the capping piece as the product of the convex-range closed Euclidean two-ball
with the standard two-sphere.  The model with corners is the corresponding product model.  Its
manifold interior and boundary are computed literally, and its boundary subtype is identified
topologically with `S¹ × S²` in the natural factor order.

The boundary identification below is only a homeomorphism.  No induced smooth structure on the
boundary subtype, smooth boundary diffeomorphism, collar, or gluing theorem is asserted.
-/

@[expose] public section

open Metric Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

/-- The capping piece `D² × S²`, with the disk factor first. -/
abbrev CapPiece : Type := EuclideanClosedBall 2 × Sphere 2

/-- The product model with corners on `D² × S²`. -/
abbrev capPieceModel := (euclideanClosedBallModel 2).prod (𝓡 2)

/-- The literal open-disk-times-sphere subset of the cap piece. -/
def capPieceInteriorSet : Set CapPiece :=
  (Subtype.val ⁻¹' ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ×ˢ
    (univ : Set (Sphere 2))

/-- The literal circle-times-sphere subset of the cap piece. -/
def capPieceBoundarySet : Set CapPiece :=
  (Subtype.val ⁻¹' sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ×ˢ
    (univ : Set (Sphere 2))

/-- The product model makes the cap piece a smooth manifold with corners to every regularity. -/
theorem isManifold_capPiece (n : ℕ∞ω) : IsManifold capPieceModel n CapPiece :=
  inferInstance

/-- The cap piece is compact. -/
theorem isCompact_capPiece : IsCompact (univ : Set CapPiece) := by
  rw [← Set.univ_prod_univ]
  exact (isCompact_euclideanClosedBall 2).prod isCompact_univ

/-- Euclidean three-space has rank strictly larger than one. -/
private theorem one_lt_rank_euclideanThree :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
  rw [← not_le]
  intro hrank
  have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) ≤ 1 :=
    FiniteDimensional.finrank_le_iff_rank_le.mpr (by simpa using hrank)
  norm_num at hfinrank

/-- The standard two-sphere is path connected. -/
theorem isPathConnected_sphereTwo : IsPathConnected (univ : Set (Sphere 2)) := by
  let h : PathConnectedSpace (Sphere 2) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere one_lt_rank_euclideanThree
        (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num))
  exact pathConnectedSpace_iff_univ.mp h

/-- The cap piece is path connected. -/
theorem isPathConnected_capPiece : IsPathConnected (univ : Set CapPiece) := by
  rw [← Set.univ_prod_univ]
  exact (isPathConnected_euclideanClosedBall 2).prod isPathConnected_sphereTwo

/-- The manifold interior of the product model is exactly the open disk times the two-sphere. -/
theorem capPieceModel_interior :
    capPieceModel.interior CapPiece = capPieceInteriorSet := by
  rw [ModelWithCorners.interior_prod, closedUnitBallModel_interior,
    ModelWithCorners.interior_eq_univ]
  rfl

/-- The manifold boundary of the product model is exactly the unit circle times the two-sphere. -/
theorem capPieceModel_boundary :
    capPieceModel.boundary CapPiece = capPieceBoundarySet := by
  rw [ModelWithCorners.boundary_of_boundaryless_right, closedUnitBallModel_boundary]
  rfl

/-- The model-boundary subtype of `D² × S²` is canonically homeomorphic to `S¹ × S²`, with the
boundary of the disk retained as the first factor.  This is a topological statement only. -/
def capPieceBoundaryHomeomorph :
    ↥(capPieceModel.boundary CapPiece) ≃ₜ Sphere 1 × Sphere 2 :=
  Homeomorph.mk
    { toFun := fun x ↦
        (⟨x.1.1.1, by
          have hx : x.1 ∈ capPieceBoundarySet :=
            (Set.ext_iff.mp capPieceModel_boundary x.1).mp x.2
          exact hx.1⟩, x.1.2)
      invFun := fun y ↦
        ⟨(⟨y.1.1, sphere_subset_closedBall y.1.2⟩, y.2), by
          apply (Set.ext_iff.mp capPieceModel_boundary _).mpr
          exact ⟨y.1.2, mem_univ _⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
    (by
      exact
        (continuous_subtype_val.comp
          (continuous_fst.comp continuous_subtype_val)).subtype_mk _ |>.prodMk
            (continuous_snd.comp continuous_subtype_val))
    (by
      apply Continuous.subtype_mk
      exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd)

@[simp]
theorem capPieceBoundaryHomeomorph_apply_fst_val
    (x : ↥(capPieceModel.boundary CapPiece)) :
    (capPieceBoundaryHomeomorph x).1.1 = x.1.1.1 :=
  rfl

@[simp]
theorem capPieceBoundaryHomeomorph_apply_snd
    (x : ↥(capPieceModel.boundary CapPiece)) :
    (capPieceBoundaryHomeomorph x).2 = x.1.2 :=
  rfl

@[simp]
theorem capPieceBoundaryHomeomorph_symm_apply_fst_val (x : Sphere 1 × Sphere 2) :
    (((capPieceBoundaryHomeomorph).symm x).1.1.1 :
      EuclideanSpace ℝ (Fin 2)) = x.1.1 :=
  rfl

@[simp]
theorem capPieceBoundaryHomeomorph_symm_apply_snd (x : Sphere 1 × Sphere 2) :
    ((capPieceBoundaryHomeomorph).symm x).1.2 = x.2 :=
  rfl

end SplittingSpheres
