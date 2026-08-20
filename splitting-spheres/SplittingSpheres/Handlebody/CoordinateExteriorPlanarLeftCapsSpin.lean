/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarAllFilling
public import SplittingSpheres.Handlebody.PartialSphereSpinFilling

/-!
# Simultaneously capping the lifted left boundary circles

The point-set pushout which attaches all labelled left lobe disks to the right-filled flower was
identified with the polynomial outer disk.  This file combines that identification with the
generic partial-spin filling theorem.  Thus the partial spin of the filled outer disk is
homeomorphic to attaching the labelled family of `disk × S²` caps to the partial spin of the
right-filled flower.

The construction is parameterized by an arbitrary retained outer circle in the right-filled
flower.  A later module supplies the concrete lifted outer circle and identifies the resulting
outer-disk parameterization.  No manifold, smoothness, or connected-sum assertion is made here.
-/

@[expose] public section

noncomputable section

open Topology

namespace SplittingSpheres

/-- The outer circle induced in the polynomial outer disk after all left lobes are filled. -/
def coordinateUnlinkExteriorPlanarAllFilledOuter
    (m : ℕ) [NeZero m]
    (outer : C(Sphere 1, CoordinateUnlinkExteriorPlanarRightFilledFlower m)) :
    C(Sphere 1, ↑(coordinateUnlinkExteriorPlanarOuterDiskSet m)) :=
  ⟨fun u ↦ coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m
      (partialSphereSpinSimultaneousPlanarFillingInl
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m) (outer u)),
    (coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m).continuous.comp <|
      (partialSphereSpinSimultaneousPlanarFillingInl
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m)).continuous.comp
          outer.continuous⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarAllFilledOuter_apply
    (m : ℕ) [NeZero m]
    (outer : C(Sphere 1, CoordinateUnlinkExteriorPlanarRightFilledFlower m))
    (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarAllFilledOuter m outer u =
      coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk m (outer u) := by
  exact coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph_inl m (outer u)

/-- Filling all left lobes before spinning is the same as attaching all labelled product caps
after spinning.  The source has already been transported from the planar filling pushout to the
literal polynomial outer disk. -/
def coordinateUnlinkExteriorPlanarLeftCapsSpinHomeomorph
    (m : ℕ) [NeZero m]
    (outer : C(Sphere 1, CoordinateUnlinkExteriorPlanarRightFilledFlower m)) :
    PartialSphereSpin (coordinateUnlinkExteriorPlanarAllFilledOuter m outer) ≃ₜ
      PartialSphereSpinSimultaneousCappedSecond outer
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m) :=
  (partialSphereSpinCongr
    (coordinateUnlinkExteriorPlanarAllFilledOuter m outer)
    (partialSphereSpinSimultaneousFilledOuter outer
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m))
    (coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m).symm
    (fun u ↦ by
      change (coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m).symm
          (coordinateUnlinkExteriorPlanarAllFilledOuter m outer u) =
        partialSphereSpinSimultaneousPlanarFillingInl
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m) (outer u)
      rw [coordinateUnlinkExteriorPlanarAllFilledOuter_apply,
        ← coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph_inl,
        (coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m).symm_apply_apply])).trans
    (partialSphereSpinSimultaneousFillingHomeomorph outer
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m))

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftCapsSpinHomeomorph_oneHandle
    (m : ℕ) [NeZero m]
    (outer : C(Sphere 1, CoordinateUnlinkExteriorPlanarRightFilledFlower m))
    (x : OneHandlePiece) :
    coordinateUnlinkExteriorPlanarLeftCapsSpinHomeomorph m outer
        (partialSphereSpinInl
          (coordinateUnlinkExteriorPlanarAllFilledOuter m outer) x) =
      partialSphereSpinSimultaneousCappedSecondInl outer
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m)
        (partialSphereSpinInl outer x) := by
  simp [coordinateUnlinkExteriorPlanarLeftCapsSpinHomeomorph]

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftCapsSpinHomeomorph_oldPiece
    (m : ℕ) [NeZero m]
    (outer : C(Sphere 1, CoordinateUnlinkExteriorPlanarRightFilledFlower m))
    (p : CoordinateUnlinkExteriorPlanarRightFilledFlower m) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarLeftCapsSpinHomeomorph m outer
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarAllFilledOuter m outer)
          (coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk m p, s)) =
      partialSphereSpinSimultaneousCappedSecondInl outer
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m)
        (partialSphereSpinInr outer (p, s)) := by
  rw [coordinateUnlinkExteriorPlanarLeftCapsSpinHomeomorph,
    Homeomorph.trans_apply]
  have hinr := partialSphereSpinCongr_inr
    (coordinateUnlinkExteriorPlanarAllFilledOuter m outer)
    (partialSphereSpinSimultaneousFilledOuter outer
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m))
    (coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m).symm
    (fun u ↦ by
      change (coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m).symm
          (coordinateUnlinkExteriorPlanarAllFilledOuter m outer u) =
        partialSphereSpinSimultaneousPlanarFillingInl
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m) (outer u)
      rw [coordinateUnlinkExteriorPlanarAllFilledOuter_apply,
        ← coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph_inl,
        (coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m).symm_apply_apply])
    (coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk m p, s)
  rw [hinr]
  change partialSphereSpinSimultaneousFillingHomeomorph outer
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m)
      (partialSphereSpinInr
        (partialSphereSpinSimultaneousFilledOuter outer
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m))
        ((coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m).symm
          (coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk m p), s)) = _
  rw [← coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph_inl,
    (coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m).symm_apply_apply]
  exact partialSphereSpinSimultaneousFillingHomeomorph_planar outer
    (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
    (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m) p s

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftCapsSpinHomeomorph_filling
    (m : ℕ) [NeZero m]
    (outer : C(Sphere 1, CoordinateUnlinkExteriorPlanarRightFilledFlower m))
    (d : CoordinateUnlinkExteriorPlanarLeftFillingDisks m) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarLeftCapsSpinHomeomorph m outer
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarAllFilledOuter m outer)
          (coordinateUnlinkExteriorPlanarLeftFillingDisksToOuterDisk m d, s)) =
      partialSphereSpinSimultaneousCappedSecondInr outer
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m) (d, s) := by
  rw [coordinateUnlinkExteriorPlanarLeftCapsSpinHomeomorph,
    Homeomorph.trans_apply]
  have hinr := partialSphereSpinCongr_inr
    (coordinateUnlinkExteriorPlanarAllFilledOuter m outer)
    (partialSphereSpinSimultaneousFilledOuter outer
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m))
    (coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m).symm
    (fun u ↦ by
      change (coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m).symm
          (coordinateUnlinkExteriorPlanarAllFilledOuter m outer u) =
        partialSphereSpinSimultaneousPlanarFillingInl
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m) (outer u)
      rw [coordinateUnlinkExteriorPlanarAllFilledOuter_apply,
        ← coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph_inl,
        (coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m).symm_apply_apply])
    (coordinateUnlinkExteriorPlanarLeftFillingDisksToOuterDisk m d, s)
  rw [hinr]
  change partialSphereSpinSimultaneousFillingHomeomorph outer
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m)
      (partialSphereSpinInr
        (partialSphereSpinSimultaneousFilledOuter outer
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m))
        ((coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m).symm
          (coordinateUnlinkExteriorPlanarLeftFillingDisksToOuterDisk m d), s)) = _
  rw [← coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph_inr,
    (coordinateUnlinkExteriorPlanarAllFilledPushoutHomeomorph m).symm_apply_apply]
  exact partialSphereSpinSimultaneousFillingHomeomorph_filling outer
    (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
    (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m) d s

end SplittingSpheres
