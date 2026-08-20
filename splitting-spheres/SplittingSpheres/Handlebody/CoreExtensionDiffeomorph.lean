/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.OneHandleCoreSupport

/-!
# Smooth direct extensions from core-supported one-handle diffeomorphisms

The locality theorem in `OneHandleCoreSupport.lean` reduces smoothness of a direct spherical
extension to smoothness on the inner one-handle band.  Here we apply that reduction separately to
a core-supported diffeomorphism and its inverse, and bundle the resulting maps as a genuine smooth
self-diffeomorphism of the literal four-sphere.

Both inner-band smoothness statements remain explicit hypotheses.  In particular, this file does
not infer smoothness across the handle seam from the topological extension alone.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace SplittingSpheres

/-- Bundle a core-supported direct extension as a smooth sphere diffeomorphism once smoothness on
the inner band has been supplied for both the map and its inverse. -/
def oneHandleCoreExtensionDiffeomorph
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho)
    (hforward : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (directCappedOneHandleExtensionSphere f.1) sphereHandleInnerBand)
    (hinverse : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (directCappedOneHandleExtensionSphere (f⁻¹).1) sphereHandleInnerBand) :
    Sphere 4 ≃ₘ^∞⟮
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)),
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))⟯ Sphere 4 where
  toEquiv := (directCappedOneHandleExtensionSphere f.1).toEquiv
  contMDiff_toFun :=
    contMDiff_directCappedOneHandleExtensionSphere_of_innerBand hrho f hforward
  contMDiff_invFun := by
    have h := contMDiff_directCappedOneHandleExtensionSphere_of_innerBand
      hrho (f⁻¹) hinverse
    rw [directCappedOneHandleExtensionSphere_inv f] at h
    exact h

@[simp]
theorem oneHandleCoreExtensionDiffeomorph_apply
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho)
    (hforward : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (directCappedOneHandleExtensionSphere f.1) sphereHandleInnerBand)
    (hinverse : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (directCappedOneHandleExtensionSphere (f⁻¹).1) sphereHandleInnerBand)
    (q : Sphere 4) :
    oneHandleCoreExtensionDiffeomorph hrho f hforward hinverse q =
      directCappedOneHandleExtensionSphere f.1 q :=
  rfl

/-- The inverse bundled diffeomorphism is exactly the direct extension of the inverse
core-supported diffeomorphism. -/
@[simp]
theorem oneHandleCoreExtensionDiffeomorph_symm_apply
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho)
    (hforward : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (directCappedOneHandleExtensionSphere f.1) sphereHandleInnerBand)
    (hinverse : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (directCappedOneHandleExtensionSphere (f⁻¹).1) sphereHandleInnerBand)
    (q : Sphere 4) :
    (oneHandleCoreExtensionDiffeomorph hrho f hforward hinverse).symm q =
      directCappedOneHandleExtensionSphere (f⁻¹).1 q := by
  change (directCappedOneHandleExtensionSphere f.1).symm q = _
  rw [← directCappedOneHandleExtensionSphere_inv f]

/-- Forgetting smoothness recovers the original direct extension homeomorphism exactly. -/
@[simp]
theorem oneHandleCoreExtensionDiffeomorph_toHomeomorph
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho)
    (hforward : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (directCappedOneHandleExtensionSphere f.1) sphereHandleInnerBand)
    (hinverse : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (directCappedOneHandleExtensionSphere (f⁻¹).1) sphereHandleInnerBand) :
    (oneHandleCoreExtensionDiffeomorph hrho f hforward hinverse).toHomeomorph =
      directCappedOneHandleExtensionSphere f.1 := by
  apply Homeomorph.ext
  intro q
  rfl

/-- The bundled diffeomorphism is the identity throughout the open outer band. -/
theorem oneHandleCoreExtensionDiffeomorph_eq_on_outerBand
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho)
    (hforward : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (directCappedOneHandleExtensionSphere f.1) sphereHandleInnerBand)
    (hinverse : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (directCappedOneHandleExtensionSphere (f⁻¹).1) sphereHandleInnerBand)
    (q : sphereHandleOuterBand rho) :
    oneHandleCoreExtensionDiffeomorph hrho f hforward hinverse q.1 = q.1 :=
  directCappedOneHandleExtensionSphere_eq_on_outerBand f q

/-- The inverse bundled diffeomorphism is also the identity throughout the open outer band. -/
theorem oneHandleCoreExtensionDiffeomorph_symm_eq_on_outerBand
    {rho : ℝ} (hrho : rho < 1)
    (f : OneHandleCoreSupportedRelativeDiff rho)
    (hforward : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (directCappedOneHandleExtensionSphere f.1) sphereHandleInnerBand)
    (hinverse : ContMDiffOn
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (directCappedOneHandleExtensionSphere (f⁻¹).1) sphereHandleInnerBand)
    (q : sphereHandleOuterBand rho) :
    (oneHandleCoreExtensionDiffeomorph hrho f hforward hinverse).symm q.1 = q.1 := by
  rw [oneHandleCoreExtensionDiffeomorph_symm_apply]
  exact directCappedOneHandleExtensionSphere_eq_on_outerBand (f⁻¹) q

end SplittingSpheres
