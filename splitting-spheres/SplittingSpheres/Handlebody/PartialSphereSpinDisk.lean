/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.PartialSphereSpin
public import SplittingSpheres.Handlebody.ProductBoundaryAttachment

/-!
# The partial sphere spin of a disk

The standard boundary circle of the closed two-ball gives a partial `S²`-spin whose two
pieces and attaching maps are exactly the usual `S¹ × B³` and `D² × S²` cap attachment.
Consequently this partial spin is homeomorphic to the standard four-sphere.

This is a point-set pushout calculation.  It does not equip the pushout with a smooth structure
or assert that the displayed homeomorphism is a diffeomorphism.
-/

@[expose] public section

noncomputable section

open Metric Topology

namespace SplittingSpheres

/-- The standard boundary-circle inclusion into the closed Euclidean two-ball. -/
def partialSphereSpinDiskOuter : C(Sphere 1, EuclideanClosedBall 2) where
  toFun u := ⟨u.1, sphere_subset_closedBall u.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem partialSphereSpinDiskOuter_apply (u : Sphere 1) :
    partialSphereSpinDiskOuter u = ⟨u.1, sphere_subset_closedBall u.2⟩ :=
  rfl

/-- On the common boundary, the partial-spin attachment for the standard disk is exactly the
coordinate cap attachment. -/
@[simp]
theorem partialSphereSpinBoundaryInclusion_diskOuter
    (x : OneHandleCapBoundary) :
    partialSphereSpinBoundaryInclusion partialSphereSpinDiskOuter x =
      capBoundaryInclusion x :=
  rfl

/-- The partial `S²`-spin of the standard closed two-disk. -/
abbrev DiskPartialSphereSpin : Type :=
  PartialSphereSpin partialSphereSpinDiskOuter

/-- The disk partial spin is the capped one-handle pushout, with all coordinates unchanged. -/
def diskPartialSphereSpinHomeomorphCappedOneHandle :
    DiskPartialSphereSpin ≃ₜ CappedOneHandle :=
  topologicalPushoutCongr
    oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion partialSphereSpinDiskOuter)
    oneHandleBoundaryInclusion capBoundaryInclusion
    (Homeomorph.refl OneHandleCapBoundary)
    (Homeomorph.refl OneHandlePiece)
    (Homeomorph.refl CapPiece)
    (fun _ ↦ rfl)
    (fun x ↦ partialSphereSpinBoundaryInclusion_diskOuter x)

@[simp]
theorem diskPartialSphereSpinHomeomorphCappedOneHandle_inl
    (x : OneHandlePiece) :
    diskPartialSphereSpinHomeomorphCappedOneHandle
        (partialSphereSpinInl partialSphereSpinDiskOuter x) =
      cappedOneHandleInl x :=
  topologicalPushoutCongr_inl
    oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion partialSphereSpinDiskOuter)
    oneHandleBoundaryInclusion capBoundaryInclusion
    (Homeomorph.refl OneHandleCapBoundary)
    (Homeomorph.refl OneHandlePiece)
    (Homeomorph.refl CapPiece)
    (fun _ ↦ rfl)
    (fun x ↦ partialSphereSpinBoundaryInclusion_diskOuter x) x

@[simp]
theorem diskPartialSphereSpinHomeomorphCappedOneHandle_inr
    (x : EuclideanClosedBall 2 × Sphere 2) :
    diskPartialSphereSpinHomeomorphCappedOneHandle
        (partialSphereSpinInr partialSphereSpinDiskOuter x) =
      cappedOneHandleInr x :=
  topologicalPushoutCongr_inr
    oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion partialSphereSpinDiskOuter)
    oneHandleBoundaryInclusion capBoundaryInclusion
    (Homeomorph.refl OneHandleCapBoundary)
    (Homeomorph.refl OneHandlePiece)
    (Homeomorph.refl CapPiece)
    (fun _ ↦ rfl)
    (fun x ↦ partialSphereSpinBoundaryInclusion_diskOuter x) x

/-- The partial `S²`-spin of a disk is homeomorphic to the standard four-sphere. -/
def diskPartialSphereSpinHomeomorphSphere :
    DiskPartialSphereSpin ≃ₜ Sphere 4 :=
  diskPartialSphereSpinHomeomorphCappedOneHandle.trans
    cappedOneHandleHomeomorphSphere

@[simp]
theorem diskPartialSphereSpinHomeomorphSphere_inl (x : OneHandlePiece) :
    diskPartialSphereSpinHomeomorphSphere
        (partialSphereSpinInl partialSphereSpinDiskOuter x) =
      cappedOneHandleHomeomorphSphere (cappedOneHandleInl x) := by
  rw [diskPartialSphereSpinHomeomorphSphere, Homeomorph.trans_apply,
    diskPartialSphereSpinHomeomorphCappedOneHandle_inl]

@[simp]
theorem diskPartialSphereSpinHomeomorphSphere_inr
    (x : EuclideanClosedBall 2 × Sphere 2) :
    diskPartialSphereSpinHomeomorphSphere
        (partialSphereSpinInr partialSphereSpinDiskOuter x) =
      cappedOneHandleHomeomorphSphere (cappedOneHandleInr x) := by
  rw [diskPartialSphereSpinHomeomorphSphere, Homeomorph.trans_apply,
    diskPartialSphereSpinHomeomorphCappedOneHandle_inr]

end SplittingSpheres
