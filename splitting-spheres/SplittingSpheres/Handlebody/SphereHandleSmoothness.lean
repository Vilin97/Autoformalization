/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.SphereHandleDecomposition

/-!
# Smoothness of the direct handle faces in the four-sphere

The direct coordinate maps from `S¹ × B³` and `D² × S²` into the literal unit
four-sphere use a square-root radial factor.  Its radicand is bounded below by `1 / 2` on either
closed ball, so the formula is smooth all the way to the model boundary.  This file proves joint
`C∞` smoothness of both face maps for the convex-range closed-ball models.

No smooth structure is put on the topological pushout here, and no smooth gluing or immersion
claim is made.
-/

@[expose] public section

noncomputable section

open Metric Set
open scoped ContDiff Manifold

namespace SplittingSpheres

/-- The square-root scale is smooth on every Euclidean closed unit ball. -/
theorem contMDiff_sphereHandleScale_closedBall (n : ℕ) :
    ContMDiff (euclideanClosedBallModel n) (modelWithCornersSelf ℝ ℝ) ∞
      (fun x : EuclideanClosedBall n ↦ sphereHandleScale ‖x.1‖) := by
  intro x
  have hxnorm : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
  have hradicand :
      ContDiffAt ℝ ∞
        (fun v : EuclideanSpace ℝ (Fin n) ↦
          1 - sphereHandleRadius ^ 2 * ‖v‖ ^ 2) x.1 :=
    contDiffAt_const.sub (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt)
  have hne :
      1 - sphereHandleRadius ^ 2 * ‖x.1‖ ^ 2 ≠ 0 := by
    rw [sphereHandleRadius_sq]
    have hsq : ‖x.1‖ ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hxnorm
    nlinarith
  have hsqrt :
      ContDiffAt ℝ ∞
        (fun v : EuclideanSpace ℝ (Fin n) ↦
          Real.sqrt (1 - sphereHandleRadius ^ 2 * ‖v‖ ^ 2)) x.1 :=
    hradicand.sqrt hne
  have hcomp := hsqrt.contMDiffAt.comp x
    (contMDiff_closedUnitBall_inclusion (EuclideanSpace ℝ (Fin n))).contMDiffAt
  exact hcomp.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun _ ↦ rfl

/-- The ambient formula for the `S¹ × B³` face is smooth up to its model boundary. -/
theorem contMDiff_oneHandleSphereRaw :
    ContMDiff oneHandlePieceModel
      (modelWithCornersSelf ℝ SphereHandleAmbient) ∞ oneHandleSphereRaw := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) := ⟨by simp⟩
  have hz : ContMDiff oneHandlePieceModel
      (modelWithCornersSelf ℝ SphereHandleFirst) ∞
      (fun x : OneHandlePiece ↦ x.1.1) :=
    contMDiff_coe_sphere.comp contMDiff_fst
  have hb : ContMDiff oneHandlePieceModel
      (modelWithCornersSelf ℝ SphereHandleSecond) ∞
      (fun x : OneHandlePiece ↦ x.2.1) :=
    (contMDiff_closedUnitBall_inclusion SphereHandleSecond).comp contMDiff_snd
  have hs : ContMDiff oneHandlePieceModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun x : OneHandlePiece ↦ sphereHandleScale ‖x.2.1‖) :=
    (contMDiff_sphereHandleScale_closedBall 3).comp contMDiff_snd
  have hfirst : ContMDiff oneHandlePieceModel
      (modelWithCornersSelf ℝ SphereHandleFirst) ∞
      (fun x : OneHandlePiece ↦ sphereHandleScale ‖x.2.1‖ • x.1.1) :=
    hs.smul hz
  have hsecond : ContMDiff oneHandlePieceModel
      (modelWithCornersSelf ℝ SphereHandleSecond) ∞
      (fun x : OneHandlePiece ↦ sphereHandleRadius • x.2.1) :=
    (show ContMDiff oneHandlePieceModel (modelWithCornersSelf ℝ ℝ) ∞
        (fun _ : OneHandlePiece ↦ sphereHandleRadius) from contMDiff_const).smul hb
  have hpair : ContMDiff oneHandlePieceModel
      (modelWithCornersSelf ℝ (SphereHandleFirst × SphereHandleSecond)) ∞
      (fun x : OneHandlePiece ↦
        (sphereHandleScale ‖x.2.1‖ • x.1.1, sphereHandleRadius • x.2.1)) :=
    (contMDiff_prod_module_iff _).2 ⟨hfirst, hsecond⟩
  exact (sphereHandleSplitEquiv.symm.contDiff.comp_contMDiff hpair).congr fun _ ↦ rfl

/-- The ambient formula for the `D² × S²` face is smooth up to its model boundary. -/
theorem contMDiff_capSphereRaw :
    ContMDiff capPieceModel
      (modelWithCornersSelf ℝ SphereHandleAmbient) ∞ capSphereRaw := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have ha : ContMDiff capPieceModel
      (modelWithCornersSelf ℝ SphereHandleFirst) ∞
      (fun x : CapPiece ↦ x.1.1) :=
    (contMDiff_closedUnitBall_inclusion SphereHandleFirst).comp contMDiff_fst
  have hw : ContMDiff capPieceModel
      (modelWithCornersSelf ℝ SphereHandleSecond) ∞
      (fun x : CapPiece ↦ x.2.1) :=
    contMDiff_coe_sphere.comp contMDiff_snd
  have hs : ContMDiff capPieceModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun x : CapPiece ↦ sphereHandleScale ‖x.1.1‖) :=
    (contMDiff_sphereHandleScale_closedBall 2).comp contMDiff_fst
  have hfirst : ContMDiff capPieceModel
      (modelWithCornersSelf ℝ SphereHandleFirst) ∞
      (fun x : CapPiece ↦ sphereHandleRadius • x.1.1) :=
    (show ContMDiff capPieceModel (modelWithCornersSelf ℝ ℝ) ∞
        (fun _ : CapPiece ↦ sphereHandleRadius) from contMDiff_const).smul ha
  have hsecond : ContMDiff capPieceModel
      (modelWithCornersSelf ℝ SphereHandleSecond) ∞
      (fun x : CapPiece ↦ sphereHandleScale ‖x.1.1‖ • x.2.1) :=
    hs.smul hw
  have hpair : ContMDiff capPieceModel
      (modelWithCornersSelf ℝ (SphereHandleFirst × SphereHandleSecond)) ∞
      (fun x : CapPiece ↦
        (sphereHandleRadius • x.1.1, sphereHandleScale ‖x.1.1‖ • x.2.1)) :=
    (contMDiff_prod_module_iff _).2 ⟨hfirst, hsecond⟩
  exact (sphereHandleSplitEquiv.symm.contDiff.comp_contMDiff hpair).congr fun _ ↦ rfl

/-- The direct `S¹ × B³` face map into the unit four-sphere is smooth. -/
theorem contMDiff_oneHandleSphereMap :
    ContMDiff oneHandlePieceModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞ oneHandleSphereMap := by
  let : Fact (Module.finrank ℝ SphereHandleAmbient = 4 + 1) := ⟨by simp⟩
  exact (contMDiff_oneHandleSphereRaw.codRestrict_sphere
    (fun x ↦ (oneHandleSphereMap x).2)).congr fun _ ↦ rfl

/-- The direct `D² × S²` cap-face map into the unit four-sphere is smooth. -/
theorem contMDiff_sphereHandleCapMap :
    ContMDiff capPieceModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞ sphereHandleCapMap := by
  let : Fact (Module.finrank ℝ SphereHandleAmbient = 4 + 1) := ⟨by simp⟩
  exact (contMDiff_capSphereRaw.codRestrict_sphere
    (fun x ↦ (sphereHandleCapMap x).2)).congr fun _ ↦ rfl

end SplittingSpheres
