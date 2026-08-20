/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.AlignedSphereHandleDecomposition
public import SplittingSpheres.Handlebody.SphereHandleSmoothness
public import TauCeti.Geometry.Diffeomorphism.Sphere

/-!
# Smoothness of the aligned sphere-handle faces

The coordinate permutation used to align the direct sphere-handle decomposition with the
coordinate unlink is orthogonal.  Its restriction to the unit four-sphere is therefore a
genuine smooth diffeomorphism.  Composing it with the already smooth direct face maps proves
smoothness of the aligned one-handle and cap faces.

This file concerns only the two face maps.  It does not install a smooth structure on their
topological pushout or assert a smooth gluing theorem.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Manifold

namespace SplittingSpheres

local instance :
    Fact (Module.finrank ℝ SphereHandleAmbient = 4 + 1) := ⟨by simp⟩

/-- The aligned coordinate permutation restricted to the unit four-sphere, as a smooth
diffeomorphism. -/
def unlinkAlignedSphereDiffeomorph :
    Sphere 4 ≃ₘ^∞⟮
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)),
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))⟯ Sphere 4 :=
  TauCeti.LinearIsometryEquiv.unitSphereDiffeomorph
    (n := 4) (k := 4) unlinkAlignedAmbientEquiv ∞

@[simp]
theorem unlinkAlignedSphereDiffeomorph_apply (q : Sphere 4) :
    unlinkAlignedSphereDiffeomorph q = unlinkAlignedSphereHomeomorph q := by
  apply Subtype.ext
  exact (TauCeti.LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply
    unlinkAlignedAmbientEquiv q).trans
      (unlinkAlignedSphereHomeomorph_coe q).symm

/-- The old point-set homeomorphism is exactly the homeomorphism underlying the new
diffeomorphism. -/
theorem unlinkAlignedSphereDiffeomorph_toHomeomorph :
    unlinkAlignedSphereDiffeomorph.toHomeomorph = unlinkAlignedSphereHomeomorph := by
  apply Homeomorph.ext
  exact unlinkAlignedSphereDiffeomorph_apply

/-- The aligned one-handle face is smooth up to the boundary of its closed-ball model. -/
theorem contMDiff_unlinkAlignedOneHandleSphereMap :
    ContMDiff oneHandlePieceModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      unlinkAlignedOneHandleSphereMap := by
  have h := unlinkAlignedSphereDiffeomorph.contMDiff.comp
    contMDiff_oneHandleSphereMap
  exact h.congr fun x ↦
    (unlinkAlignedSphereDiffeomorph_apply (oneHandleSphereMap x)).symm

/-- The aligned cap face is smooth up to the boundary of its closed-ball model. -/
theorem contMDiff_unlinkAlignedCapSphereMap :
    ContMDiff capPieceModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      unlinkAlignedCapSphereMap := by
  have h := unlinkAlignedSphereDiffeomorph.contMDiff.comp
    contMDiff_sphereHandleCapMap
  exact h.congr fun x ↦
    (unlinkAlignedSphereDiffeomorph_apply (sphereHandleCapMap x)).symm

end SplittingSpheres
