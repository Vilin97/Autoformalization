/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.RelativeDiffeomorph
public import SplittingSpheres.Foundations.TopologicalPushoutExtension
public import SplittingSpheres.Handlebody.ProductBoundaryAttachment

/-!
# Extending a boundary-relative one-handle diffeomorphism over its cap

A smooth self-diffeomorphism of `S¹ × B³` which fixes its model boundary pointwise has an
underlying homeomorphism fixing the attaching copy of `S¹ × S²`.  The topological pushout
extension therefore gives a self-homeomorphism of the capped one-handle, equal to the identity on
the cap.  Conjugating by the previously constructed homeomorphism identifies this extension with a
self-homeomorphism of the project's literal `Sphere 4`.

This file deliberately records only the topological extension.  It does not claim that the
pushout extension or its conjugate is smooth; that requires smooth collar and gluing control.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace SplittingSpheres

/-- Smooth self-diffeomorphisms of the compact one-handle which fix its model boundary
pointwise. -/
abbrev OneHandleBoundaryRelativeDiff :=
  TauCeti.RelativeDiff (I := oneHandlePieceModel) OneHandlePiece ∞
    (oneHandlePieceModel.boundary OneHandlePiece)

/-- The underlying self-homeomorphism of a boundary-relative one-handle diffeomorphism. -/
def oneHandleBoundaryRelativeHomeomorph
    (f : OneHandleBoundaryRelativeDiff) : OneHandlePiece ≃ₜ OneHandlePiece :=
  (f.1).toHomeomorph

@[simp]
theorem oneHandleBoundaryRelativeHomeomorph_apply
    (f : OneHandleBoundaryRelativeDiff) (x : OneHandlePiece) :
    oneHandleBoundaryRelativeHomeomorph f x = f.1 x :=
  rfl

/-- Boundary-relative diffeomorphisms fix the literal attaching map pointwise. -/
theorem oneHandleBoundaryRelativeHomeomorph_fixes_attachment
    (f : OneHandleBoundaryRelativeDiff) (z : OneHandleCapBoundary) :
    oneHandleBoundaryRelativeHomeomorph f (oneHandleBoundaryInclusion z) =
      oneHandleBoundaryInclusion z := by
  change f.1 (oneHandleBoundaryInclusion z) = oneHandleBoundaryInclusion z
  apply TauCeti.RelativeDiff.apply_eq f
  rw [oneHandleBoundaryInclusion_eq_homeomorph]
  exact (oneHandlePieceBoundaryHomeomorph.symm z).2

/-- Extend a boundary-relative one-handle diffeomorphism over the cap by the identity. -/
def cappedOneHandleExtension (f : OneHandleBoundaryRelativeDiff) :
    CappedOneHandle ≃ₜ CappedOneHandle :=
  topologicalPushoutLeftExtension oneHandleBoundaryInclusion capBoundaryInclusion
    (oneHandleBoundaryRelativeHomeomorph f)
    (oneHandleBoundaryRelativeHomeomorph_fixes_attachment f)

/-- On the one-handle piece, the capped extension is the original diffeomorphism. -/
@[simp]
theorem cappedOneHandleExtension_inl
    (f : OneHandleBoundaryRelativeDiff) (x : OneHandlePiece) :
    cappedOneHandleExtension f (cappedOneHandleInl x) =
      cappedOneHandleInl (f.1 x) :=
  topologicalPushoutLeftExtension_inl
    oneHandleBoundaryInclusion capBoundaryInclusion
    (oneHandleBoundaryRelativeHomeomorph f)
    (oneHandleBoundaryRelativeHomeomorph_fixes_attachment f) x

/-- On the cap piece, the capped extension is the identity. -/
@[simp]
theorem cappedOneHandleExtension_inr
    (f : OneHandleBoundaryRelativeDiff) (x : CapPiece) :
    cappedOneHandleExtension f (cappedOneHandleInr x) = cappedOneHandleInr x :=
  topologicalPushoutLeftExtension_inr
    oneHandleBoundaryInclusion capBoundaryInclusion
    (oneHandleBoundaryRelativeHomeomorph f)
    (oneHandleBoundaryRelativeHomeomorph_fixes_attachment f) x

/-- The extension fixes every point in the image of the cap piece. -/
theorem cappedOneHandleExtension_eq_of_mem_cap_range
    (f : OneHandleBoundaryRelativeDiff) {x : CappedOneHandle}
    (hx : x ∈ range cappedOneHandleInr) : cappedOneHandleExtension f x = x := by
  obtain ⟨y, rfl⟩ := hx
  exact cappedOneHandleExtension_inr f y

/-- Capping carries the identity relative diffeomorphism to the identity homeomorphism. -/
@[simp]
theorem cappedOneHandleExtension_one :
    cappedOneHandleExtension (1 : OneHandleBoundaryRelativeDiff) = 1 := by
  ext z
  rcases topologicalPushout_jointly_surjective
      oneHandleBoundaryInclusion capBoundaryInclusion z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · rw [cappedOneHandleExtension_inl]
    rfl
  · rw [cappedOneHandleExtension_inr]
    rfl

/-- Capping respects the composition convention on relative diffeomorphisms. -/
@[simp]
theorem cappedOneHandleExtension_mul
    (f g : OneHandleBoundaryRelativeDiff) :
    cappedOneHandleExtension (f * g) =
      cappedOneHandleExtension f * cappedOneHandleExtension g := by
  ext z
  rcases topologicalPushout_jointly_surjective
      oneHandleBoundaryInclusion capBoundaryInclusion z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · simp only [Homeomorph.mul_apply, cappedOneHandleExtension_inl]
    apply congr_arg cappedOneHandleInl
    rfl
  · simp only [Homeomorph.mul_apply, cappedOneHandleExtension_inr]

/-- Extending by the identity on the cap is a group homomorphism on underlying
homeomorphisms. -/
def cappedOneHandleExtensionHom :
    OneHandleBoundaryRelativeDiff →* (CappedOneHandle ≃ₜ CappedOneHandle) where
  toFun := cappedOneHandleExtension
  map_one' := cappedOneHandleExtension_one
  map_mul' := cappedOneHandleExtension_mul

/-- Capping is faithful: the extension retains the entire map on the injectively embedded
one-handle piece. -/
theorem cappedOneHandleExtensionHom_injective :
    Function.Injective cappedOneHandleExtensionHom := by
  intro f g h
  change cappedOneHandleExtension f = cappedOneHandleExtension g at h
  apply Subtype.ext
  apply Diffeomorph.ext
  intro x
  apply cappedOneHandleInl_injective
  have hx := congrArg
    (fun e : CappedOneHandle ≃ₜ CappedOneHandle ↦ e (cappedOneHandleInl x)) h
  simpa only [MonoidHom.coe_mk, OneHom.coe_mk, cappedOneHandleExtension_inl] using hx

/-- Transport the capped extension to the literal standard four-sphere. -/
def cappedOneHandleExtensionSphere (f : OneHandleBoundaryRelativeDiff) :
    Sphere 4 ≃ₜ Sphere 4 :=
  (cappedOneHandleHomeomorphSphere.symm.trans (cappedOneHandleExtension f)).trans
    cappedOneHandleHomeomorphSphere

/-- Exact action of the sphere extension on the embedded one-handle piece. -/
@[simp]
theorem cappedOneHandleExtensionSphere_inl
    (f : OneHandleBoundaryRelativeDiff) (x : OneHandlePiece) :
    cappedOneHandleExtensionSphere f
        (cappedOneHandleHomeomorphSphere (cappedOneHandleInl x)) =
      cappedOneHandleHomeomorphSphere (cappedOneHandleInl (f.1 x)) := by
  change cappedOneHandleHomeomorphSphere
      (cappedOneHandleExtension f
        (cappedOneHandleHomeomorphSphere.symm
          (cappedOneHandleHomeomorphSphere (cappedOneHandleInl x)))) = _
  rw [cappedOneHandleHomeomorphSphere.symm_apply_apply,
    cappedOneHandleExtension_inl]

/-- Exact action of the sphere extension on the embedded cap piece. -/
@[simp]
theorem cappedOneHandleExtensionSphere_inr
    (f : OneHandleBoundaryRelativeDiff) (x : CapPiece) :
    cappedOneHandleExtensionSphere f
        (cappedOneHandleHomeomorphSphere (cappedOneHandleInr x)) =
      cappedOneHandleHomeomorphSphere (cappedOneHandleInr x) := by
  change cappedOneHandleHomeomorphSphere
      (cappedOneHandleExtension f
        (cappedOneHandleHomeomorphSphere.symm
          (cappedOneHandleHomeomorphSphere (cappedOneHandleInr x)))) = _
  rw [cappedOneHandleHomeomorphSphere.symm_apply_apply,
    cappedOneHandleExtension_inr]

/-- The transported extension fixes the entire image of the cap piece pointwise. -/
theorem cappedOneHandleExtensionSphere_eq_of_mem_cap_range
    (f : OneHandleBoundaryRelativeDiff) {x : Sphere 4}
    (hx : x ∈ range (fun y : CapPiece ↦
      cappedOneHandleHomeomorphSphere (cappedOneHandleInr y))) :
    cappedOneHandleExtensionSphere f x = x := by
  obtain ⟨y, rfl⟩ := hx
  exact cappedOneHandleExtensionSphere_inr f y

/-- Transporting the identity extension to the standard sphere remains the identity. -/
@[simp]
theorem cappedOneHandleExtensionSphere_one :
    cappedOneHandleExtensionSphere (1 : OneHandleBoundaryRelativeDiff) = 1 := by
  ext x
  simp [cappedOneHandleExtensionSphere]

/-- Transporting capped extensions to the standard sphere preserves composition. -/
@[simp]
theorem cappedOneHandleExtensionSphere_mul
    (f g : OneHandleBoundaryRelativeDiff) :
    cappedOneHandleExtensionSphere (f * g) =
      cappedOneHandleExtensionSphere f * cappedOneHandleExtensionSphere g := by
  ext x
  simp [cappedOneHandleExtensionSphere, cappedOneHandleExtension_mul,
    Homeomorph.mul_apply]

/-- The topological extension to the literal standard sphere as a group homomorphism. -/
def cappedOneHandleExtensionSphereHom :
    OneHandleBoundaryRelativeDiff →* (Sphere 4 ≃ₜ Sphere 4) where
  toFun := cappedOneHandleExtensionSphere
  map_one' := cappedOneHandleExtensionSphere_one
  map_mul' := cappedOneHandleExtensionSphere_mul

/-- Conjugating the faithful capped extension to the standard sphere remains faithful. -/
theorem cappedOneHandleExtensionSphereHom_injective :
    Function.Injective cappedOneHandleExtensionSphereHom := by
  intro f g h
  change cappedOneHandleExtensionSphere f = cappedOneHandleExtensionSphere g at h
  apply Subtype.ext
  apply Diffeomorph.ext
  intro x
  apply cappedOneHandleInl_injective
  apply cappedOneHandleHomeomorphSphere.injective
  have hx := congrArg
    (fun e : Sphere 4 ≃ₜ Sphere 4 ↦
      e (cappedOneHandleHomeomorphSphere (cappedOneHandleInl x))) h
  simpa only [MonoidHom.coe_mk, OneHom.coe_mk,
    cappedOneHandleExtensionSphere_inl] using hx

end SplittingSpheres
