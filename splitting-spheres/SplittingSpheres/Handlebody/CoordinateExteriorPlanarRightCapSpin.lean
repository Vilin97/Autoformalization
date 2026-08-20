/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPartialSphereSpin
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarRightFilling
public import SplittingSpheres.Handlebody.PartialSphereSpinFilling

/-!
# Spinning the right filling of the planar flower

The planar power pullback is first transported to its explicit flower coordinate.  Filling the
right hole of that flower by its literal closed disk and then taking the partial `S²`-spin is
homeomorphic to first taking the partial spin of the unfilled flower and then attaching the
product of the filling disk with `S²`.

Everything here is an instance of functoriality and associativity for topological pushouts.
In particular, no smooth, manifold, connected-sum, or surface-classification claim is made.
-/

@[expose] public section

noncomputable section

open Topology

namespace SplittingSpheres

/-! ## The outer circle in flower coordinates -/

/-- The original lifted outer circle, transported from the planar pullback into the explicit
flower coordinate. -/
def coordinateUnlinkExteriorPlanarFlowerOuter
    (m : ℕ) [NeZero m] : C(Sphere 1, CoordinateUnlinkExteriorPlanarFlower m) where
  toFun u :=
    coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m
      (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m u)
  continuous_toFun := by
    let e :=
      coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m
    exact e.continuous.comp
      (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m).continuous

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerOuter_apply
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarFlowerOuter m u =
      coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m
        (coordinateUnlinkExteriorPlanarOuterLift m u) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerOuter_val
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    (coordinateUnlinkExteriorPlanarFlowerOuter m u).1 =
      (coordinateUnlinkExteriorPlanarOuterLift m u).1.2 :=
  rfl

/-- The retained outer circle in the concrete right-filled flower. -/
def coordinateUnlinkExteriorPlanarRightFilledOuter
    (m : ℕ) [NeZero m] :
    C(Sphere 1, CoordinateUnlinkExteriorPlanarRightFilledFlower m) :=
  (coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m).comp
    (coordinateUnlinkExteriorPlanarFlowerOuter m)

@[simp]
theorem coordinateUnlinkExteriorPlanarRightFilledOuter_apply
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarRightFilledOuter m u =
      coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m
        (coordinateUnlinkExteriorPlanarFlowerOuter m u) :=
  rfl

/-! ## The original pullback spin in flower coordinates -/

/-- The partial spin of the planar flower along its transported outer circle. -/
abbrev CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin
    (m : ℕ) [NeZero m] : Type :=
  PartialSphereSpin (coordinateUnlinkExteriorPlanarFlowerOuter m)

/-- Coordinate change from the original planar-pullback partial spin to the flower partial
spin.  It is the identity on the one-handle piece and the existing planar homeomorphism on the
planar factor. -/
def coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPartialSphereSpin m ≃ₜ
      CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m :=
  partialSphereSpinCongr
    (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m)
    (coordinateUnlinkExteriorPlanarFlowerOuter m)
    (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m)
    (fun _ ↦ rfl)

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph_oneHandle
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph m
        (partialSphereSpinInl
          (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m) x) =
      partialSphereSpinInl (coordinateUnlinkExteriorPlanarFlowerOuter m) x :=
  by
    unfold coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph
    exact partialSphereSpinCongr_inl _ _ _ _ x

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph_planar
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m)
    (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarOuterLiftContinuousMap m) (z, s)) =
      partialSphereSpinInr (coordinateUnlinkExteriorPlanarFlowerOuter m)
        (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m z, s) :=
  by
    unfold coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph
    exact partialSphereSpinCongr_inr _ _ _ _ (z, s)

/-! ## Replacing the planar pushout by the concrete filled flower -/

/-- The right-filled flower expressed as the planar pushout used by the generic filling API. -/
abbrev CoordinateUnlinkExteriorPlanarRightCapPlanarPushout
    (m : ℕ) [NeZero m] : Type :=
  PartialSphereSpinSimultaneousPlanarFilling
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m)

/-- The retained outer circle in the right-filling planar pushout. -/
abbrev coordinateUnlinkExteriorPlanarRightCapPushoutOuter
    (m : ℕ) [NeZero m] :
    C(Sphere 1, CoordinateUnlinkExteriorPlanarRightCapPlanarPushout m) :=
  partialSphereSpinSimultaneousFilledOuter
    (coordinateUnlinkExteriorPlanarFlowerOuter m)
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m)

/-- The existing planar pushout homeomorphism carries the retained outer circle to the natural
outer circle in the concrete right-filled flower. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarRightFilledPushoutHomeomorph_outer
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarRightFilledPushoutHomeomorph m
        (coordinateUnlinkExteriorPlanarRightCapPushoutOuter m u) =
      coordinateUnlinkExteriorPlanarRightFilledOuter m u := by
  simp [coordinateUnlinkExteriorPlanarRightCapPushoutOuter,
    coordinateUnlinkExteriorPlanarRightFilledOuter]

/-- Partial-spin congruence induced by the planar right-filling pushout homeomorphism. -/
def coordinateUnlinkExteriorPlanarRightFilledSpinCongr
    (m : ℕ) [NeZero m] :
    PartialSphereSpin (coordinateUnlinkExteriorPlanarRightCapPushoutOuter m) ≃ₜ
      PartialSphereSpin (coordinateUnlinkExteriorPlanarRightFilledOuter m) :=
  partialSphereSpinCongr
    (coordinateUnlinkExteriorPlanarRightCapPushoutOuter m)
    (coordinateUnlinkExteriorPlanarRightFilledOuter m)
    (coordinateUnlinkExteriorPlanarRightFilledPushoutHomeomorph m)
    (coordinateUnlinkExteriorPlanarRightFilledPushoutHomeomorph_outer m)

@[simp]
theorem coordinateUnlinkExteriorPlanarRightFilledSpinCongr_oneHandle
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    coordinateUnlinkExteriorPlanarRightFilledSpinCongr m
        (partialSphereSpinInl
          (coordinateUnlinkExteriorPlanarRightCapPushoutOuter m) x) =
      partialSphereSpinInl (coordinateUnlinkExteriorPlanarRightFilledOuter m) x :=
  partialSphereSpinCongr_inl _ _ _ _ x

@[simp]
theorem coordinateUnlinkExteriorPlanarRightFilledSpinCongr_flower
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarFlower m) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarRightFilledSpinCongr m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarRightCapPushoutOuter m)
          (partialSphereSpinSimultaneousPlanarFillingInl
            (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
            (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m) z, s)) =
      partialSphereSpinInr (coordinateUnlinkExteriorPlanarRightFilledOuter m)
        (coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m z, s) := by
  rw [coordinateUnlinkExteriorPlanarRightFilledSpinCongr,
    partialSphereSpinCongr_inr]
  simp

@[simp]
theorem coordinateUnlinkExteriorPlanarRightFilledSpinCongr_disk
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarRightFillingDisk m) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarRightFilledSpinCongr m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarRightCapPushoutOuter m)
          (partialSphereSpinSimultaneousPlanarFillingInr
            (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
            (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m) z, s)) =
      partialSphereSpinInr (coordinateUnlinkExteriorPlanarRightFilledOuter m)
        (coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower m z, s) := by
  rw [coordinateUnlinkExteriorPlanarRightFilledSpinCongr,
    partialSphereSpinCongr_inr]
  simp

@[simp]
theorem coordinateUnlinkExteriorPlanarRightFilledSpinCongr_symm_oneHandle
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    (coordinateUnlinkExteriorPlanarRightFilledSpinCongr m).symm
        (partialSphereSpinInl (coordinateUnlinkExteriorPlanarRightFilledOuter m) x) =
      partialSphereSpinInl
        (coordinateUnlinkExteriorPlanarRightCapPushoutOuter m) x := by
  apply (coordinateUnlinkExteriorPlanarRightFilledSpinCongr m).injective
  rw [(coordinateUnlinkExteriorPlanarRightFilledSpinCongr m).apply_symm_apply]
  exact (coordinateUnlinkExteriorPlanarRightFilledSpinCongr_oneHandle m x).symm

@[simp]
theorem coordinateUnlinkExteriorPlanarRightFilledSpinCongr_symm_flower
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarFlower m) (s : Sphere 2) :
    (coordinateUnlinkExteriorPlanarRightFilledSpinCongr m).symm
        (partialSphereSpinInr (coordinateUnlinkExteriorPlanarRightFilledOuter m)
          (coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m z, s)) =
      partialSphereSpinInr
        (coordinateUnlinkExteriorPlanarRightCapPushoutOuter m)
        (partialSphereSpinSimultaneousPlanarFillingInl
          (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
          (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m) z, s) := by
  apply (coordinateUnlinkExteriorPlanarRightFilledSpinCongr m).injective
  rw [(coordinateUnlinkExteriorPlanarRightFilledSpinCongr m).apply_symm_apply]
  exact (coordinateUnlinkExteriorPlanarRightFilledSpinCongr_flower m z s).symm

@[simp]
theorem coordinateUnlinkExteriorPlanarRightFilledSpinCongr_symm_disk
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarRightFillingDisk m) (s : Sphere 2) :
    (coordinateUnlinkExteriorPlanarRightFilledSpinCongr m).symm
        (partialSphereSpinInr (coordinateUnlinkExteriorPlanarRightFilledOuter m)
          (coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower m z, s)) =
      partialSphereSpinInr
        (coordinateUnlinkExteriorPlanarRightCapPushoutOuter m)
        (partialSphereSpinSimultaneousPlanarFillingInr
          (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
          (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m) z, s) := by
  apply (coordinateUnlinkExteriorPlanarRightFilledSpinCongr m).injective
  rw [(coordinateUnlinkExteriorPlanarRightFilledSpinCongr m).apply_symm_apply]
  exact (coordinateUnlinkExteriorPlanarRightFilledSpinCongr_disk m z s).symm

/-! ## Spinning after the right cap -/

/-- The result of attaching the right filling disk times `S²` to the partial spin of the
unfilled planar flower. -/
abbrev CoordinateUnlinkExteriorPlanarRightCapSpin
    (m : ℕ) [NeZero m] : Type :=
  PartialSphereSpinSimultaneousCappedSecond
    (coordinateUnlinkExteriorPlanarFlowerOuter m)
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m)

/-- Taking the partial spin after filling the right hole is homeomorphic to attaching the
corresponding filling-disk product to the partial spin of the original flower. -/
def coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph
    (m : ℕ) [NeZero m] :
    PartialSphereSpin (coordinateUnlinkExteriorPlanarRightFilledOuter m) ≃ₜ
      CoordinateUnlinkExteriorPlanarRightCapSpin m :=
  (coordinateUnlinkExteriorPlanarRightFilledSpinCongr m).symm.trans <|
    partialSphereSpinSimultaneousFillingHomeomorph
      (coordinateUnlinkExteriorPlanarFlowerOuter m)
      (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
      (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m)

@[simp]
theorem coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph_oneHandle
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph m
        (partialSphereSpinInl (coordinateUnlinkExteriorPlanarRightFilledOuter m) x) =
      partialSphereSpinSimultaneousCappedSecondInl
        (coordinateUnlinkExteriorPlanarFlowerOuter m)
        (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
        (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m)
        (partialSphereSpinInl (coordinateUnlinkExteriorPlanarFlowerOuter m) x) := by
  rw [coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph,
    Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarRightFilledSpinCongr_symm_oneHandle]
  exact partialSphereSpinSimultaneousFillingHomeomorph_oneHandle _ _ _ x

@[simp]
theorem coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph_flower
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarFlower m) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph m
        (partialSphereSpinInr (coordinateUnlinkExteriorPlanarRightFilledOuter m)
          (coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower m z, s)) =
      partialSphereSpinSimultaneousCappedSecondInl
        (coordinateUnlinkExteriorPlanarFlowerOuter m)
        (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
        (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m)
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarFlowerOuter m) (z, s)) := by
  rw [coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph,
    Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarRightFilledSpinCongr_symm_flower]
  exact partialSphereSpinSimultaneousFillingHomeomorph_planar _ _ _ z s

@[simp]
theorem coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph_disk
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarRightFillingDisk m) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph m
        (partialSphereSpinInr (coordinateUnlinkExteriorPlanarRightFilledOuter m)
          (coordinateUnlinkExteriorPlanarRightFillingDiskToFilledFlower m z, s)) =
      partialSphereSpinSimultaneousCappedSecondInr
        (coordinateUnlinkExteriorPlanarFlowerOuter m)
        (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
        (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m) (z, s) := by
  rw [coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph,
    Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarRightFilledSpinCongr_symm_disk]
  exact partialSphereSpinSimultaneousFillingHomeomorph_filling _ _ _ z s

end SplittingSpheres
