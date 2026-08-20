/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarLeftCapsSpin
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarOuterDiskSpin
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarRightCapSpin
public import SplittingSpheres.Foundations.TopologicalPushoutCongr

/-!
# Completely capping the lifted planar partial sphere spin

The retained outer circle obtained after first filling the right hole and then all labelled
left holes is literally the outer circle of the polynomial disk.  Consequently, the space
obtained by attaching all labelled left `disk × S²` caps to the partial spin of the
right-filled flower is homeomorphic to `S⁴`.

Together with `coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph`, this identifies both
stages of the explicit capping construction: the right cap replaces the right hole of the
original flower, and the simultaneous labelled caps replace all remaining left holes.  The
result here is point-set topological; no smooth gluing or connected-sum assertion is made.
-/

@[expose] public section

noncomputable section

open Topology

namespace SplittingSpheres

/-- Filling all inner holes preserves the original lifted outer circle exactly. -/
theorem coordinateUnlinkExteriorPlanarAllFilledOuter_rightFilledOuter
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarAllFilledOuter m
        (coordinateUnlinkExteriorPlanarRightFilledOuter m) =
      coordinateUnlinkExteriorPlanarOuterDiskOuter m := by
  ext u
  rw [coordinateUnlinkExteriorPlanarAllFilledOuter_apply,
    coordinateUnlinkExteriorPlanarRightFilledFlowerToOuterDisk_coe,
    coordinateUnlinkExteriorPlanarRightFilledOuter_apply,
    coordinateUnlinkExteriorPlanarFlowerToRightFilledFlower_coe,
    coordinateUnlinkExteriorPlanarFlowerOuter_val,
    coordinateUnlinkExteriorPlanarOuterDiskOuter_apply,
    coordinateUnlinkExteriorPlanarOuterBoundaryToDisk_coe,
    coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph_coe]

/-- Attaching all left caps to the partial spin of the right-filled flower gives `S⁴`. -/
def coordinateUnlinkExteriorPlanarLeftCapsHomeomorphSphere
    (m : ℕ) [NeZero m] :
    PartialSphereSpinSimultaneousCappedSecond
        (coordinateUnlinkExteriorPlanarRightFilledOuter m)
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m) ≃ₜ
      Sphere 4 :=
  by
    let h := (coordinateUnlinkExteriorPlanarLeftCapsSpinHomeomorph m
      (coordinateUnlinkExteriorPlanarRightFilledOuter m)).symm
    rw [coordinateUnlinkExteriorPlanarAllFilledOuter_rightFilledOuter m] at h
    exact h.trans <|
      coordinateUnlinkExteriorPlanarOuterDiskPartialSpinHomeomorphSphere m

/-! ## A literal two-stage cap attachment -/

/-- The spun labelled left attaching circles, transported through the homeomorphism which
realizes the right filling as a product cap attachment. -/
def coordinateUnlinkExteriorPlanarLeftBoundaryToRightCapSpin
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarLeftFillingBoundaries m × Sphere 2,
      CoordinateUnlinkExteriorPlanarRightCapSpin m) :=
  (⟨coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph m,
    (coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph m).continuous⟩ :
      C(PartialSphereSpin (coordinateUnlinkExteriorPlanarRightFilledOuter m),
        CoordinateUnlinkExteriorPlanarRightCapSpin m)).comp <|
    partialSphereSpinSimultaneousInnerBoundaryInclusion
      (coordinateUnlinkExteriorPlanarRightFilledOuter m)
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftBoundaryToRightCapSpin_apply
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarLeftFillingBoundaries m × Sphere 2) :
    coordinateUnlinkExteriorPlanarLeftBoundaryToRightCapSpin m x =
      coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarRightFilledOuter m)
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m x.1,
            x.2)) :=
  rfl

/-- The literal two-stage capped space: its left piece already results from attaching the right
cap to the original flower spin, and the outer pushout attaches every labelled left cap. -/
abbrev CoordinateUnlinkExteriorPlanarCompleteCapping
    (m : ℕ) [NeZero m] : Type :=
  TopologicalPushout
    (coordinateUnlinkExteriorPlanarLeftBoundaryToRightCapSpin m)
    (partialSphereSpinSimultaneousFillBoundaryInclusion
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m))

/-- Include the right-cap stage into the completely capped space. -/
abbrev coordinateUnlinkExteriorPlanarCompleteCappingInl
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarRightCapSpin m,
      CoordinateUnlinkExteriorPlanarCompleteCapping m) :=
  topologicalPushoutInl
    (coordinateUnlinkExteriorPlanarLeftBoundaryToRightCapSpin m)
    (partialSphereSpinSimultaneousFillBoundaryInclusion
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m))

/-- Include all labelled left product caps into the completely capped space. -/
abbrev coordinateUnlinkExteriorPlanarCompleteCappingInr
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarLeftFillingDisks m × Sphere 2,
      CoordinateUnlinkExteriorPlanarCompleteCapping m) :=
  topologicalPushoutInr
    (coordinateUnlinkExteriorPlanarLeftBoundaryToRightCapSpin m)
    (partialSphereSpinSimultaneousFillBoundaryInclusion
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m))

/-- Transporting the left-capping pushout through the right-cap homeomorphism exposes both cap
stages as literal successive pushouts. -/
def coordinateUnlinkExteriorPlanarLeftCapsToCompleteCappingHomeomorph
    (m : ℕ) [NeZero m] :
    PartialSphereSpinSimultaneousCappedSecond
        (coordinateUnlinkExteriorPlanarRightFilledOuter m)
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
        (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m) ≃ₜ
      CoordinateUnlinkExteriorPlanarCompleteCapping m :=
  topologicalPushoutCongr
    (partialSphereSpinSimultaneousInnerBoundaryInclusion
      (coordinateUnlinkExteriorPlanarRightFilledOuter m)
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m))
    (partialSphereSpinSimultaneousFillBoundaryInclusion
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m))
    (coordinateUnlinkExteriorPlanarLeftBoundaryToRightCapSpin m)
    (partialSphereSpinSimultaneousFillBoundaryInclusion
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m))
    (Homeomorph.refl _)
    (coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph m)
    (Homeomorph.refl _)
    (fun _ ↦ rfl)
    (fun _ ↦ rfl)

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftCapsToCompleteCappingHomeomorph_old
    (m : ℕ) [NeZero m]
    (z : PartialSphereSpin (coordinateUnlinkExteriorPlanarRightFilledOuter m)) :
    coordinateUnlinkExteriorPlanarLeftCapsToCompleteCappingHomeomorph m
        (partialSphereSpinSimultaneousCappedSecondInl
          (coordinateUnlinkExteriorPlanarRightFilledOuter m)
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m) z) =
      coordinateUnlinkExteriorPlanarCompleteCappingInl m
        (coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph m z) := by
  apply topologicalPushoutCongr_inl

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftCapsToCompleteCappingHomeomorph_leftCaps
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarLeftFillingDisks m × Sphere 2) :
    coordinateUnlinkExteriorPlanarLeftCapsToCompleteCappingHomeomorph m
        (partialSphereSpinSimultaneousCappedSecondInr
          (coordinateUnlinkExteriorPlanarRightFilledOuter m)
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)
          (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m) z) =
      coordinateUnlinkExteriorPlanarCompleteCappingInr m z := by
  apply topologicalPushoutCongr_inr

/-- The literal two-stage attachment of the right cap and every labelled left cap is a
four-sphere. -/
def coordinateUnlinkExteriorPlanarCompleteCappingHomeomorphSphere
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarCompleteCapping m ≃ₜ Sphere 4 :=
  (coordinateUnlinkExteriorPlanarLeftCapsToCompleteCappingHomeomorph m).symm.trans
    (coordinateUnlinkExteriorPlanarLeftCapsHomeomorphSphere m)

end SplittingSpheres
