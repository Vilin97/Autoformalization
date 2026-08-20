/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.ClosedBall
public import SplittingSpheres.Statement
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# The compact one-handle piece

This file packages the product `S¹ × B³` used as a compact four-dimensional piece in the
handlebody constructions.  The circle is the project's literal `Sphere 1`, and the closed ball is
equipped with the convex-range model from `SplittingSpheres.Geometry.ClosedBall`.  Their product is
therefore a genuine manifold with corners to every regularity.

The model interior and boundary are computed exactly.  The boundary subtype is identified
topologically with `Sphere 1 × Sphere 2`.  We deliberately make no claim that this boundary
subtype carries an induced smooth structure, or that the closed-ball model is equivalent to the
standard half-space model.
-/

@[expose] public section

open Metric Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

/-- The compact product `S¹ × B³` underlying one four-dimensional one-handle piece. -/
abbrev OneHandlePiece : Type :=
  Sphere 1 × EuclideanClosedBall 3

/-- The product model with corners on `S¹ × B³`.

Its model vector space has dimension `1 + 3 = 4`; no identification with a standard
half-space model is asserted. -/
abbrev OneHandleModelSpace : Type :=
  ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanClosedBall 3)

/-- The product model with corners on `S¹ × B³`. -/
abbrev oneHandlePieceModel :
    ModelWithCorners ℝ
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3))
      OneHandleModelSpace :=
  (𝓡 1).prod (euclideanClosedBallModel 3)

/-- The model vector space of `oneHandlePieceModel` is four-dimensional. -/
theorem oneHandlePieceModel_finrank :
    Module.finrank ℝ
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)) = 4 := by
  simp

/-- The compact one-handle piece is a manifold with corners to every regularity. -/
theorem isManifold_oneHandlePiece (n : ℕ∞ω) :
    IsManifold oneHandlePieceModel n OneHandlePiece :=
  inferInstance

/-- The exact product formula for the model interior of `S¹ × B³`. -/
theorem oneHandlePieceModel_interior :
    oneHandlePieceModel.interior OneHandlePiece =
      (univ : Set (Sphere 1)) ×ˢ
        (euclideanClosedBallModel 3).interior (EuclideanClosedBall 3) := by
  rw [ModelWithCorners.interior_prod, ModelWithCorners.interior_eq_univ]

/-- In ambient ball coordinates, the model interior is exactly `S¹` times the open unit
three-ball. -/
theorem oneHandlePieceModel_interior_eq :
    oneHandlePieceModel.interior OneHandlePiece =
      (univ : Set (Sphere 1)) ×ˢ
        (Subtype.val ⁻¹' ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  rw [oneHandlePieceModel_interior, closedUnitBallModel_interior]

/-- The exact product formula for the model boundary of `S¹ × B³`. -/
theorem oneHandlePieceModel_boundary :
    oneHandlePieceModel.boundary OneHandlePiece =
      (univ : Set (Sphere 1)) ×ˢ
        (euclideanClosedBallModel 3).boundary (EuclideanClosedBall 3) := by
  exact ModelWithCorners.boundary_of_boundaryless_left
    (I := 𝓡 1) (J := euclideanClosedBallModel 3)
    (M := Sphere 1) (N := EuclideanClosedBall 3)

/-- In ambient ball coordinates, the model boundary is exactly `S¹` times the unit
two-sphere. -/
theorem oneHandlePieceModel_boundary_eq :
    oneHandlePieceModel.boundary OneHandlePiece =
      (univ : Set (Sphere 1)) ×ˢ
        (Subtype.val ⁻¹' sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  rw [oneHandlePieceModel_boundary, closedUnitBallModel_boundary]

/-- The circle factor, regarded as a whole subtype, is path connected. -/
theorem isPathConnected_sphereOne :
    IsPathConnected (univ : Set (Sphere 1)) := by
  apply pathConnectedSpace_iff_univ.mp
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere
  · exact Module.one_lt_rank_of_one_lt_finrank (by simp)
  · norm_num

/-- The compact one-handle piece is compact. -/
theorem isCompact_oneHandlePiece :
    IsCompact (univ : Set OneHandlePiece) :=
  isCompact_univ

/-- The compact one-handle piece is path connected. -/
theorem isPathConnected_oneHandlePiece :
    IsPathConnected (univ : Set OneHandlePiece) := by
  rw [← univ_prod_univ]
  exact isPathConnected_sphereOne.prod (isPathConnected_euclideanClosedBall 3)

/-- The literal model-boundary subtype of the compact one-handle piece. -/
abbrev OneHandlePieceBoundary : Type :=
  ↥(oneHandlePieceModel.boundary OneHandlePiece)

/-- The model-boundary subtype of `S¹ × B³` is canonically homeomorphic to
`S¹ × S²`.

This is only a homeomorphism of the literal subtypes.  No induced smooth structure on the model
boundary is asserted. -/
def oneHandlePieceBoundaryHomeomorph :
    OneHandlePieceBoundary ≃ₜ Sphere 1 × Sphere 2 :=
  (Homeomorph.setCongr oneHandlePieceModel_boundary).trans <|
    (Homeomorph.Set.prod
      (univ : Set (Sphere 1))
      ((euclideanClosedBallModel 3).boundary (EuclideanClosedBall 3))).trans <|
      (Homeomorph.Set.univ (Sphere 1)).prodCongr
        (euclideanClosedBallBoundaryHomeomorphSphere 2)

@[simp]
theorem oneHandlePieceBoundaryHomeomorph_apply
    (x : OneHandlePieceBoundary) :
    oneHandlePieceBoundaryHomeomorph x =
      (x.1.1, euclideanClosedBallBoundaryHomeomorphSphere 2
        ⟨x.1.2, by
          exact (Set.ext_iff.mp oneHandlePieceModel_boundary x.1).mp x.2 |>.2⟩) :=
  rfl

@[simp]
theorem oneHandlePieceBoundaryHomeomorph_symm_apply_val
    (y : Sphere 1 × Sphere 2) :
    ((oneHandlePieceBoundaryHomeomorph.symm y).1 : OneHandlePiece) =
      (y.1, (euclideanClosedBallBoundaryHomeomorphSphere 2).symm y.2 |>.1) :=
  rfl

end SplittingSpheres
