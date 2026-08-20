/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.PartialSphereSpinAnnulus

/-!
# Reversing the attaching end of the annular partial sphere spin

The basic annular partial-spin theorem attaches `S¹ × B³` to the `t = 0` end of the
literal annulus.  The normalized neck decomposition uses the opposite convention: its lifted
seams lie on the `t = 1` end.  This file conjugates the established theorem by the central
symmetry of the unit interval.

Everything here is a point-set homeomorphism.  No smooth gluing or connected-sum statement is
made.
-/

@[expose] public section

noncomputable section

open Topology
open scoped unitInterval

namespace SplittingSpheres

/-- The one end of the literal annulus, parametrized by its circle coordinate. -/
def partialSphereSpinAnnulusOne : C(Sphere 1, PartialSphereSpinAnnulus) where
  toFun u := (u, 1)
  continuous_toFun := continuous_id.prodMk continuous_const

@[simp]
theorem partialSphereSpinAnnulusOne_apply (u : Sphere 1) :
    partialSphereSpinAnnulusOne u = (u, 1) :=
  rfl

/-- Reverse the unit-interval coordinate of the literal annulus. -/
def partialSphereSpinAnnulusReverseHomeomorph :
    PartialSphereSpinAnnulus ≃ₜ PartialSphereSpinAnnulus :=
  (Homeomorph.refl (Sphere 1)).prodCongr unitInterval.symmHomeomorph

@[simp]
theorem partialSphereSpinAnnulusReverseHomeomorph_apply
    (x : PartialSphereSpinAnnulus) :
    partialSphereSpinAnnulusReverseHomeomorph x = (x.1, unitInterval.symm x.2) :=
  rfl

@[simp]
theorem partialSphereSpinAnnulusReverseHomeomorph_symm_apply
    (x : PartialSphereSpinAnnulus) :
    partialSphereSpinAnnulusReverseHomeomorph.symm x =
      (x.1, unitInterval.symm x.2) :=
  rfl

@[simp]
theorem partialSphereSpinAnnulusReverseHomeomorph_one (u : Sphere 1) :
    partialSphereSpinAnnulusReverseHomeomorph (partialSphereSpinAnnulusOne u) =
      partialSphereSpinAnnulusOuter u := by
  rw [partialSphereSpinAnnulusOne_apply,
    partialSphereSpinAnnulusReverseHomeomorph_apply,
    unitInterval.symm_one, partialSphereSpinAnnulusOuter_apply]

@[simp]
theorem partialSphereSpinAnnulusReverseHomeomorph_zero (u : Sphere 1) :
    partialSphereSpinAnnulusReverseHomeomorph (partialSphereSpinAnnulusOuter u) =
      partialSphereSpinAnnulusOne u := by
  rw [partialSphereSpinAnnulusOuter_apply,
    partialSphereSpinAnnulusReverseHomeomorph_apply,
    unitInterval.symm_zero, partialSphereSpinAnnulusOne_apply]

/-- Reversing the annulus coordinate identifies the partial spin attached at `t = 1` with the
partial spin attached at `t = 0`. -/
def partialSphereSpinAnnulusOneToOuterHomeomorph :
    PartialSphereSpin partialSphereSpinAnnulusOne ≃ₜ
      PartialSphereSpin partialSphereSpinAnnulusOuter :=
  partialSphereSpinCongr
    partialSphereSpinAnnulusOne partialSphereSpinAnnulusOuter
    partialSphereSpinAnnulusReverseHomeomorph
    partialSphereSpinAnnulusReverseHomeomorph_one

@[simp]
theorem partialSphereSpinAnnulusOneToOuterHomeomorph_inl
    (x : OneHandlePiece) :
    partialSphereSpinAnnulusOneToOuterHomeomorph
        (partialSphereSpinInl partialSphereSpinAnnulusOne x) =
      partialSphereSpinInl partialSphereSpinAnnulusOuter x :=
  partialSphereSpinCongr_inl _ _ _ _ x

@[simp]
theorem partialSphereSpinAnnulusOneToOuterHomeomorph_inr
    (x : PartialSphereSpinAnnulus × Sphere 2) :
    partialSphereSpinAnnulusOneToOuterHomeomorph
        (partialSphereSpinInr partialSphereSpinAnnulusOne x) =
      partialSphereSpinInr partialSphereSpinAnnulusOuter
        (partialSphereSpinAnnulusReverseHomeomorph x.1, x.2) :=
  partialSphereSpinCongr_inr _ _ _ _ x

/-- The partial `S²`-spin attached to the `t = 1` end of the literal annulus is the compact
one-handle `S¹ × B³`. -/
def partialSphereSpinAnnulusOneHomeomorphOneHandle :
    PartialSphereSpin partialSphereSpinAnnulusOne ≃ₜ OneHandlePiece :=
  partialSphereSpinAnnulusOneToOuterHomeomorph.trans
    partialSphereSpinAnnulusHomeomorphOneHandle

@[simp]
theorem partialSphereSpinAnnulusOneHomeomorphOneHandle_inl
    (x : OneHandlePiece) :
    partialSphereSpinAnnulusOneHomeomorphOneHandle
        (partialSphereSpinInl partialSphereSpinAnnulusOne x) =
      partialSphereSpinAnnulusOneHandleMap x := by
  rw [partialSphereSpinAnnulusOneHomeomorphOneHandle,
    Homeomorph.trans_apply,
    partialSphereSpinAnnulusOneToOuterHomeomorph_inl,
    partialSphereSpinAnnulusHomeomorphOneHandle_inl]

@[simp]
theorem partialSphereSpinAnnulusOneHomeomorphOneHandle_inr
    (x : PartialSphereSpinAnnulus × Sphere 2) :
    partialSphereSpinAnnulusOneHomeomorphOneHandle
        (partialSphereSpinInr partialSphereSpinAnnulusOne x) =
      partialSphereSpinAnnulusShellMap
        (partialSphereSpinAnnulusReverseHomeomorph x.1, x.2) := by
  rw [partialSphereSpinAnnulusOneHomeomorphOneHandle,
    Homeomorph.trans_apply,
    partialSphereSpinAnnulusOneToOuterHomeomorph_inr,
    partialSphereSpinAnnulusHomeomorphOneHandle_inr]

/-- The unglued `t = 0` annulus end becomes the ordinary boundary of the resulting
one-handle. -/
@[simp]
theorem partialSphereSpinAnnulusOneHomeomorphOneHandle_zeroBoundary
    (x : OneHandleCapBoundary) :
    partialSphereSpinAnnulusOneHomeomorphOneHandle
        (partialSphereSpinInr partialSphereSpinAnnulusOne ((x.1, 0), x.2)) =
      oneHandleBoundaryInclusion x := by
  rw [partialSphereSpinAnnulusOneHomeomorphOneHandle_inr,
    partialSphereSpinAnnulusReverseHomeomorph_apply,
    unitInterval.symm_zero,
    partialSphereSpinAnnulusShellMap_one]

end SplittingSpheres
