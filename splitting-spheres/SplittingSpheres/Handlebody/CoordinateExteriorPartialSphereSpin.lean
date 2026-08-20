/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarOuterBoundary
public import SplittingSpheres.Handlebody.PartialSphereSpin

/-!
# The cyclic exterior cover as a partial sphere spin

The lifted outer boundary of the planar power pullback is now an explicit circle, and the
trivialized cap attaching map is exactly its product with `id : S² → S²`.  Consequently the
previous lifted-piece pushout is literally homeomorphic to the partial `S²`-spin of the planar
pullback.  Composing with the earlier pushout and base-change homeomorphisms identifies this
partial spin with both the pushout model and the radius-`1/8` closed-exterior power pullback.

This is an exact point-set homeomorphism.  It does not classify the planar pullback as a compact
surface, identify an interior connected sum, or assert smooth compatibility of the glued
atlases.
-/

@[expose] public section

noncomputable section

open Topology

namespace SplittingSpheres

/-- The lifted outer circle, bundled as a continuous map. -/
def coordinateUnlinkExteriorPlanarOuterLiftContinuousMap
    (m : ℕ) [NeZero m] :
    C(Sphere 1, CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :=
  ⟨coordinateUnlinkExteriorPlanarOuterLift m,
    continuous_coordinateUnlinkExteriorPlanarOuterLift m⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterLiftContinuousMap_apply
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m u =
      coordinateUnlinkExteriorPlanarOuterLift m u :=
  rfl

/-- The partial spin of the explicit planar power pullback. -/
abbrev CoordinateUnlinkExteriorPartialSphereSpin
    (m : ℕ) [NeZero m] : Type :=
  PartialSphereSpin (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m)

/-- The previously trivialized lifted-piece pushout and the partial-spin definition have
identical pieces and propositionally identical attaching maps. -/
def coordinateUnlinkExteriorTrivializedPushoutPartialSphereSpinHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorTrivializedPowerPullbackPushout m ≃ₜ
      CoordinateUnlinkExteriorPartialSphereSpin m :=
  topologicalPushoutCongr
    oneHandleBoundaryInclusion
    (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m)
    oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion
      (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m))
    (Homeomorph.refl OneHandleCapBoundary)
    (Homeomorph.refl OneHandlePiece)
    (Homeomorph.refl
      (CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2))
    (fun _ ↦ rfl)
    (fun x ↦ coordinateUnlinkExteriorTrivializedCapBoundaryInclusion_eq_outerLift
      m x.1 x.2)

@[simp]
theorem coordinateUnlinkExteriorTrivializedPushoutPartialSphereSpinHomeomorph_inl
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    coordinateUnlinkExteriorTrivializedPushoutPartialSphereSpinHomeomorph m
        (topologicalPushoutInl oneHandleBoundaryInclusion
          (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m) x) =
      partialSphereSpinInl
        (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m) x :=
  topologicalPushoutCongr_inl
    oneHandleBoundaryInclusion
    (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m)
    oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion
      (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m))
    (Homeomorph.refl OneHandleCapBoundary)
    (Homeomorph.refl OneHandlePiece)
    (Homeomorph.refl
      (CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2))
    (fun _ ↦ rfl)
    (fun x ↦ coordinateUnlinkExteriorTrivializedCapBoundaryInclusion_eq_outerLift
      m x.1 x.2) x

@[simp]
theorem coordinateUnlinkExteriorTrivializedPushoutPartialSphereSpinHomeomorph_inr
    (m : ℕ) [NeZero m]
    (y : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2) :
    coordinateUnlinkExteriorTrivializedPushoutPartialSphereSpinHomeomorph m
        (topologicalPushoutInr oneHandleBoundaryInclusion
          (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m) y) =
      partialSphereSpinInr
        (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m) y :=
  topologicalPushoutCongr_inr
    oneHandleBoundaryInclusion
    (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m)
    oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion
      (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m))
    (Homeomorph.refl OneHandleCapBoundary)
    (Homeomorph.refl OneHandlePiece)
    (Homeomorph.refl
      (CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2))
    (fun _ ↦ rfl)
    (fun x ↦ coordinateUnlinkExteriorTrivializedCapBoundaryInclusion_eq_outerLift
      m x.1 x.2) y

@[simp]
theorem coordinateUnlinkExteriorTrivializedPushoutPartialSphereSpinHomeomorph_symm_inl
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    (coordinateUnlinkExteriorTrivializedPushoutPartialSphereSpinHomeomorph m).symm
        (partialSphereSpinInl
          (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m) x) =
      topologicalPushoutInl oneHandleBoundaryInclusion
        (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m) x :=
  topologicalPushoutCongr_symm_inl
    oneHandleBoundaryInclusion
    (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m)
    oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion
      (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m))
    (Homeomorph.refl OneHandleCapBoundary)
    (Homeomorph.refl OneHandlePiece)
    (Homeomorph.refl
      (CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2))
    (fun _ ↦ rfl)
    (fun x ↦ coordinateUnlinkExteriorTrivializedCapBoundaryInclusion_eq_outerLift
      m x.1 x.2) x

@[simp]
theorem coordinateUnlinkExteriorTrivializedPushoutPartialSphereSpinHomeomorph_symm_inr
    (m : ℕ) [NeZero m]
    (y : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2) :
    (coordinateUnlinkExteriorTrivializedPushoutPartialSphereSpinHomeomorph m).symm
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m) y) =
      topologicalPushoutInr oneHandleBoundaryInclusion
        (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m) y :=
  topologicalPushoutCongr_symm_inr
    oneHandleBoundaryInclusion
    (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m)
    oneHandleBoundaryInclusion
    (partialSphereSpinBoundaryInclusion
      (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m))
    (Homeomorph.refl OneHandleCapBoundary)
    (Homeomorph.refl OneHandlePiece)
    (Homeomorph.refl
      (CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2))
    (fun _ ↦ rfl)
    (fun x ↦ coordinateUnlinkExteriorTrivializedCapBoundaryInclusion_eq_outerLift
      m x.1 x.2) y

/-- The partial spin is homeomorphic to the global power pullback over the exterior pushout. -/
def coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPartialSphereSpin m ≃ₜ
      CoordinateUnlinkExteriorPushoutPowerPullback m :=
  (coordinateUnlinkExteriorTrivializedPushoutPartialSphereSpinHomeomorph m).symm.trans
    (coordinateUnlinkExteriorTrivializedPowerPullbackPushoutHomeomorph m)

@[simp]
theorem coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph_inl
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph m
        (partialSphereSpinInl
          (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m) x) =
      coordinateUnlinkExteriorOneHandlePowerPullbackToPushout m
        (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m x) := by
  rw [coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph,
    Homeomorph.trans_apply,
    coordinateUnlinkExteriorTrivializedPushoutPartialSphereSpinHomeomorph_symm_inl]
  exact coordinateUnlinkExteriorTrivializedPowerPullbackPushoutHomeomorph_inl m x

@[simp]
theorem coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph_inr
    (m : ℕ) [NeZero m]
    (y : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2) :
    coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m) y) =
      coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout m
        ((coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m).symm y) := by
  rw [coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph,
    Homeomorph.trans_apply,
    coordinateUnlinkExteriorTrivializedPushoutPartialSphereSpinHomeomorph_symm_inr]
  exact coordinateUnlinkExteriorTrivializedPowerPullbackPushoutHomeomorph_inr m y

/-- Final point-set identification with the literal radius-`1/8` closed-exterior power
pullback. -/
def coordinateUnlinkExteriorPartialSphereSpinHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPartialSphereSpin m ≃ₜ
      CoordinateUnlinkExteriorEighthPowerPullback m :=
  (coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph m).trans
    (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m)

@[simp]
theorem coordinateUnlinkExteriorPartialSphereSpinHomeomorph_proj
    (m : ℕ) [NeZero m] (z : CoordinateUnlinkExteriorPartialSphereSpin m) :
    coordinateUnlinkExteriorEighthPowerPullbackProj m
        (coordinateUnlinkExteriorPartialSphereSpinHomeomorph m z) =
      coordinateUnlinkExteriorOneEighthHomeomorph
        (coordinateUnlinkExteriorPushoutPowerPullbackProj m
          (coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph m z)) :=
  coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_proj m _

end SplittingSpheres
