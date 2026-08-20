/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutEmbedding
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarCompleteCapping

/-!
# Recovering the cyclic partial spin by deleting the off-boundary cap pieces

The completely capped model is a nested pair of pushouts.  This file names the subsets of the
right cap and all labelled left caps which lie off their attaching boundaries, and identifies
the original flower partial spin with the complement of those subsets in the completely capped
space.  Their concrete strict metric descriptions are proved in
`CoordinateExteriorPlanarCapLabels`.

After composing with the established homeomorphism of the complete capping with `S⁴`, this
gives an exact complement model for the cyclic exterior cover.  It does not yet assert that the
cap cocores form a standard unlink or identify the complement with an interior connected sum.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-! ## The original spun piece and the two off-boundary cap subsets -/

/-- Include the original flower partial spin into the right-cap stage. -/
abbrev coordinateUnlinkExteriorPlanarFlowerSpinToRightCapSpin
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m,
      CoordinateUnlinkExteriorPlanarRightCapSpin m) :=
  partialSphereSpinSimultaneousCappedSecondInl
    (coordinateUnlinkExteriorPlanarFlowerOuter m)
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m)

/-- Include the right filling disk times `S²` into the right-cap stage. -/
abbrev coordinateUnlinkExteriorPlanarRightCapToRightCapSpin
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarRightFillingDisk m × Sphere 2,
      CoordinateUnlinkExteriorPlanarRightCapSpin m) :=
  partialSphereSpinSimultaneousCappedSecondInr
    (coordinateUnlinkExteriorPlanarFlowerOuter m)
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m)

/-- Points of the right product cap which do not lie on its attaching boundary. -/
def coordinateUnlinkExteriorPlanarRightCapInteriorSource
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorPlanarRightFillingDisk m × Sphere 2) :=
  (range (partialSphereSpinSimultaneousFillBoundaryInclusion
    (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m)))ᶜ

/-- The off-attaching-boundary part of the right cap, as a subset of the right-cap pushout. -/
def coordinateUnlinkExteriorPlanarRightCapInteriorInRightCapSpin
    (m : ℕ) [NeZero m] : Set (CoordinateUnlinkExteriorPlanarRightCapSpin m) :=
  coordinateUnlinkExteriorPlanarRightCapToRightCapSpin m ''
    coordinateUnlinkExteriorPlanarRightCapInteriorSource m

/-- The off-boundary right-cap subset transported into the completely capped nested pushout. -/
def coordinateUnlinkExteriorPlanarRightCapInterior
    (m : ℕ) [NeZero m] : Set (CoordinateUnlinkExteriorPlanarCompleteCapping m) :=
  coordinateUnlinkExteriorPlanarCompleteCappingInl m ''
    coordinateUnlinkExteriorPlanarRightCapInteriorInRightCapSpin m

/-- Points of the labelled left product caps which do not lie on their attaching boundary. -/
def coordinateUnlinkExteriorPlanarLeftCapsInteriorSource
    (m : ℕ) [NeZero m] :
    Set (CoordinateUnlinkExteriorPlanarLeftFillingDisks m × Sphere 2) :=
  (range (partialSphereSpinSimultaneousFillBoundaryInclusion
    (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m)))ᶜ

/-- The union of all off-boundary labelled-left-cap subsets in the completely capped pushout. -/
def coordinateUnlinkExteriorPlanarLeftCapsInterior
    (m : ℕ) [NeZero m] : Set (CoordinateUnlinkExteriorPlanarCompleteCapping m) :=
  coordinateUnlinkExteriorPlanarCompleteCappingInr m ''
    coordinateUnlinkExteriorPlanarLeftCapsInteriorSource m

/-- The union of the one right and all labelled left off-boundary cap subsets. -/
def coordinateUnlinkExteriorPlanarCapInteriors
    (m : ℕ) [NeZero m] : Set (CoordinateUnlinkExteriorPlanarCompleteCapping m) :=
  coordinateUnlinkExteriorPlanarRightCapInterior m ∪
    coordinateUnlinkExteriorPlanarLeftCapsInterior m

/-- Include the original flower partial spin through both successive cap-attachment pushouts. -/
def coordinateUnlinkExteriorPlanarFlowerSpinToCompleteCapping
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m,
      CoordinateUnlinkExteriorPlanarCompleteCapping m) :=
  (coordinateUnlinkExteriorPlanarCompleteCappingInl m).comp
    (coordinateUnlinkExteriorPlanarFlowerSpinToRightCapSpin m)

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerSpinToCompleteCapping_apply
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) :
    coordinateUnlinkExteriorPlanarFlowerSpinToCompleteCapping m z =
      coordinateUnlinkExteriorPlanarCompleteCappingInl m
        (coordinateUnlinkExteriorPlanarFlowerSpinToRightCapSpin m z) :=
  rfl

/-! ## Injectivity of all attaching and piece maps -/

theorem injective_coordinateUnlinkExteriorPlanarRightCapInnerBoundary
    (m : ℕ) [NeZero m] :
    Injective (partialSphereSpinSimultaneousInnerBoundaryInclusion
      (coordinateUnlinkExteriorPlanarFlowerOuter m)
      (coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)) :=
  injective_partialSphereSpinSimultaneousInnerBoundaryInclusion _ _
    (injective_coordinateUnlinkExteriorPlanarRightFillingBoundaryToFlower m)

theorem injective_coordinateUnlinkExteriorPlanarRightCapFillBoundary
    (m : ℕ) [NeZero m] :
    Injective (partialSphereSpinSimultaneousFillBoundaryInclusion
      (coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m)) :=
  injective_partialSphereSpinSimultaneousFillBoundaryInclusion _
    (injective_coordinateUnlinkExteriorPlanarRightFillingBoundaryToDisk m)

theorem injective_coordinateUnlinkExteriorPlanarLeftCapsInnerBoundary
    (m : ℕ) [NeZero m] :
    Injective (partialSphereSpinSimultaneousInnerBoundaryInclusion
      (coordinateUnlinkExteriorPlanarRightFilledOuter m)
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)) :=
  injective_partialSphereSpinSimultaneousInnerBoundaryInclusion _ _
    (injective_coordinateUnlinkExteriorPlanarLeftFillingBoundariesToRightFilledFlower m)

theorem injective_coordinateUnlinkExteriorPlanarLeftBoundaryToRightCapSpin
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarLeftBoundaryToRightCapSpin m) :=
  (coordinateUnlinkExteriorPlanarRightCapSpinHomeomorph m).injective.comp
    (injective_coordinateUnlinkExteriorPlanarLeftCapsInnerBoundary m)

theorem injective_coordinateUnlinkExteriorPlanarLeftCapsFillBoundary
    (m : ℕ) [NeZero m] :
    Injective (partialSphereSpinSimultaneousFillBoundaryInclusion
      (coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m)) :=
  injective_partialSphereSpinSimultaneousFillBoundaryInclusion _
    (injective_coordinateUnlinkExteriorPlanarLeftFillingBoundariesToDisks m)

theorem injective_coordinateUnlinkExteriorPlanarFlowerSpinToRightCapSpin
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarFlowerSpinToRightCapSpin m) :=
  topologicalPushoutInl_injective _ _
    (injective_coordinateUnlinkExteriorPlanarRightCapFillBoundary m)

theorem injective_coordinateUnlinkExteriorPlanarCompleteCappingInl
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarCompleteCappingInl m) :=
  topologicalPushoutInl_injective _ _
    (injective_coordinateUnlinkExteriorPlanarLeftCapsFillBoundary m)

theorem injective_coordinateUnlinkExteriorPlanarFlowerSpinToCompleteCapping
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarFlowerSpinToCompleteCapping m) :=
  (injective_coordinateUnlinkExteriorPlanarCompleteCappingInl m).comp
    (injective_coordinateUnlinkExteriorPlanarFlowerSpinToRightCapSpin m)

/-! ## Exact complement identities -/

/-- Deleting the off-attaching-boundary right-cap piece from the first pushout leaves exactly
the original flower partial spin. -/
theorem range_coordinateUnlinkExteriorPlanarFlowerSpinToRightCapSpin
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarFlowerSpinToRightCapSpin m) =
      (coordinateUnlinkExteriorPlanarRightCapInteriorInRightCapSpin m)ᶜ := by
  exact range_topologicalPushoutInl_eq_compl_image_inr_compl_range _ _
    (injective_coordinateUnlinkExteriorPlanarRightCapInnerBoundary m)

/-- Deleting all off-attaching-boundary left-cap pieces from the second pushout leaves exactly
the right-cap stage. -/
theorem range_coordinateUnlinkExteriorPlanarCompleteCappingInl
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarCompleteCappingInl m) =
      (coordinateUnlinkExteriorPlanarLeftCapsInterior m)ᶜ := by
  exact range_topologicalPushoutInl_eq_compl_image_inr_compl_range _ _
    (injective_coordinateUnlinkExteriorPlanarLeftBoundaryToRightCapSpin m)

/-- In the nested completely capped space, the original flower partial spin is exactly the
complement of the union of the right and all labelled left off-boundary cap subsets. -/
theorem range_coordinateUnlinkExteriorPlanarFlowerSpinToCompleteCapping
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarFlowerSpinToCompleteCapping m) =
      (coordinateUnlinkExteriorPlanarCapInteriors m)ᶜ := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    intro hz
    rcases hz with hright | hleft
    · rcases hright with ⟨y, hy, hyeq⟩
      have hyx : y = coordinateUnlinkExteriorPlanarFlowerSpinToRightCapSpin m x :=
        injective_coordinateUnlinkExteriorPlanarCompleteCappingInl m hyeq
      have hxrange : coordinateUnlinkExteriorPlanarFlowerSpinToRightCapSpin m x ∈
          range (coordinateUnlinkExteriorPlanarFlowerSpinToRightCapSpin m) := ⟨x, rfl⟩
      rw [range_coordinateUnlinkExteriorPlanarFlowerSpinToRightCapSpin m] at hxrange
      exact hxrange (hyx ▸ hy)
    · have hxrange : coordinateUnlinkExteriorPlanarFlowerSpinToCompleteCapping m x ∈
          range (coordinateUnlinkExteriorPlanarCompleteCappingInl m) :=
        ⟨coordinateUnlinkExteriorPlanarFlowerSpinToRightCapSpin m x, rfl⟩
      rw [range_coordinateUnlinkExteriorPlanarCompleteCappingInl m] at hxrange
      exact hxrange hleft
  · intro hz
    have hzleft : z ∈ (coordinateUnlinkExteriorPlanarLeftCapsInterior m)ᶜ := by
      intro hleft
      exact hz (Or.inr hleft)
    rw [← range_coordinateUnlinkExteriorPlanarCompleteCappingInl m] at hzleft
    obtain ⟨y, rfl⟩ := hzleft
    have hyright : y ∈
        (coordinateUnlinkExteriorPlanarRightCapInteriorInRightCapSpin m)ᶜ := by
      intro hright
      exact hz (Or.inl ⟨y, hright, rfl⟩)
    rw [← range_coordinateUnlinkExteriorPlanarFlowerSpinToRightCapSpin m] at hyright
    obtain ⟨x, rfl⟩ := hyright
    exact ⟨x, rfl⟩

/-! ## Homeomorphisms onto the cap complement -/

/-- The original flower partial spin is homeomorphic to the literal complement of the
off-boundary cap subsets in the completely capped nested pushout. -/
def coordinateUnlinkExteriorPlanarFlowerSpinCapComplementHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarCapInteriors m)ᶜ := by
  letI : CompactSpace (CoordinateUnlinkExteriorPlanarFlower m) :=
    compactSpace_coordinateUnlinkExteriorPlanarFlower m
  letI : CompactSpace (CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) :=
    partialSphereSpinCompactSpace (coordinateUnlinkExteriorPlanarFlowerOuter m)
  letI : T2Space (CoordinateUnlinkExteriorPlanarCompleteCapping m) :=
    (coordinateUnlinkExteriorPlanarCompleteCappingHomeomorphSphere m).symm.t2Space
  let hclosed : IsClosedEmbedding
      (coordinateUnlinkExteriorPlanarFlowerSpinToCompleteCapping m) :=
    (coordinateUnlinkExteriorPlanarFlowerSpinToCompleteCapping m).continuous.isClosedEmbedding
      (injective_coordinateUnlinkExteriorPlanarFlowerSpinToCompleteCapping m)
  exact hclosed.isEmbedding.toHomeomorph.trans <|
    Homeomorph.setCongr
      (range_coordinateUnlinkExteriorPlanarFlowerSpinToCompleteCapping m)

/-- The off-boundary cap subsets transported to the standard four-sphere supplied by the
complete-capping homeomorphism. -/
def coordinateUnlinkExteriorPlanarCapInteriorsSphere
    (m : ℕ) [NeZero m] : Set (Sphere 4) :=
  coordinateUnlinkExteriorPlanarCompleteCappingHomeomorphSphere m ''
    coordinateUnlinkExteriorPlanarCapInteriors m

/-- The original flower partial spin is the complement in `S⁴` of the transported
off-boundary cap subsets. -/
def coordinateUnlinkExteriorPlanarFlowerSpinCapComplementHomeomorphSphere
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarCapInteriorsSphere m)ᶜ :=
  (coordinateUnlinkExteriorPlanarFlowerSpinCapComplementHomeomorph m).trans <|
    (coordinateUnlinkExteriorPlanarCompleteCappingHomeomorphSphere m).image
        (coordinateUnlinkExteriorPlanarCapInteriors m)ᶜ |>.trans <|
      Homeomorph.setCongr <|
        (coordinateUnlinkExteriorPlanarCompleteCappingHomeomorphSphere m).image_compl
          (coordinateUnlinkExteriorPlanarCapInteriors m)

/-- The explicit partial-spin model of the cyclic cover is the same cap complement in `S⁴`. -/
def coordinateUnlinkExteriorPartialSphereSpinCapComplementHomeomorphSphere
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPartialSphereSpin m ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarCapInteriorsSphere m)ᶜ :=
  (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph m).trans
    (coordinateUnlinkExteriorPlanarFlowerSpinCapComplementHomeomorphSphere m)

/-- The literal radius-`1/8` cyclic exterior power pullback is homeomorphic to the complement in
`S⁴` of exactly the displayed off-attaching-boundary right and labelled-left cap subsets. -/
def coordinateUnlinkExteriorEighthPowerPullbackCapComplementHomeomorphSphere
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorEighthPowerPullback m ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarCapInteriorsSphere m)ᶜ :=
  (coordinateUnlinkExteriorPartialSphereSpinHomeomorph m).symm.trans
    (coordinateUnlinkExteriorPartialSphereSpinCapComplementHomeomorphSphere m)

end SplittingSpheres
