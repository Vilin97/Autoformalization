/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPowerTrivializedPushout

/-!
# The lifted outer boundary of the planar power pullback

The lifted attaching boundary has already been trivialized as `S¹ × S²`.  Its map into the
punctured-cap product has an `S²` coordinate which is literally unchanged.  In this file we
extract the remaining planar circle, prove that the attaching map is its product with the
identity of `S²`, and identify it with the exact part of the planar pullback lying over the
displayed outer boundary of the punctured normal disk.

Everything is point-set topology.  In particular, no claim about induced boundary orientation
or about the other boundary components of the planar pullback is made.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-- A fixed point of `Sphere 2`, used only to extract the planar factor from the already
trivialized product attaching map. -/
def coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint : Sphere 2 :=
  Classical.choice <| by
    obtain ⟨s⟩ :=
      (NormedSpace.sphere_nonempty
        (E := EuclideanSpace ℝ (Fin 3)) (x := 0) (r := 1) |>.mpr zero_le_one).to_subtype
    exact ⟨s⟩

/-- The lifted outer circle in the planar power pullback.  Its power coordinate is exactly the
one selected by the existing boundary-cover trivialization. -/
def coordinateUnlinkExteriorPlanarOuterLift
    (m : ℕ) [NeZero m]
    (u : Sphere 1) : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m :=
  (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m
    (u, coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint)).1

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterLift_proj
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarOuterLift m u) =
      coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary
        (unlinkUnitCirclePow m u) :=
  coordinateUnlinkExteriorTrivializedCapBoundaryInclusion_planarBase m
    (u, coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint)

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterLift_powerCoordinate
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    (coordinateUnlinkExteriorPlanarOuterLift m u).1.2 =
      (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m
        (u, coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint)).1.2 :=
  coordinateUnlinkExteriorTrivializedCapBoundaryInclusion_powerCoordinate m
    (u, coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint)

theorem continuous_coordinateUnlinkExteriorPlanarOuterLift
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarOuterLift m) := by
  exact continuous_fst.comp <|
    (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m).continuous.comp
      (continuous_id.prodMk continuous_const)

/-- On the attaching boundary, the selected power coordinate is independent of the `S²`
coordinate. -/
theorem coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph_powerCoordinate_eq
    (m : ℕ) [NeZero m] (u : Sphere 1) (s t : Sphere 2) :
    (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m (u, s)).1.2 =
      (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m (u, t)).1.2 := by
  rw [coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph_apply,
    coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph_apply]
  change coordinateUnlinkExteriorOneHandleTrivializationPowerCoordinate m
      (oneHandleBoundaryInclusion (u, s)) =
    coordinateUnlinkExteriorOneHandleTrivializationPowerCoordinate m
      (oneHandleBoundaryInclusion (u, t))
  apply Subtype.ext
  simp [coordinateUnlinkExteriorOneHandleTrivializationPowerCoordinate,
    coordinateUnlinkExteriorOneHandleBasePowerMap,
    coordinateUnlinkExteriorOneHandleResidual, oneHandleBoundaryInclusion_apply,
    mem_sphere_zero_iff_norm.mp s.2, mem_sphere_zero_iff_norm.mp t.2]

/-- The whole lifted cap attaching map is the product of the planar outer lift with the identity
on `S²`. -/
@[simp]
theorem coordinateUnlinkExteriorTrivializedCapBoundaryInclusion_eq_outerLift
    (m : ℕ) [NeZero m] (u : Sphere 1) (s : Sphere 2) :
    coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m (u, s) =
      (coordinateUnlinkExteriorPlanarOuterLift m u, s) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · exact (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion_planarBase m (u, s)).trans
        (coordinateUnlinkExteriorPlanarOuterLift_proj m u).symm
    · exact coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph_powerCoordinate_eq
        m u s coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint
  · exact coordinateUnlinkExteriorTrivializedCapBoundaryInclusion_sphereCoordinate m (u, s)

/-! ## The outer-boundary restricted pullback -/

theorem injective_coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary :
    Injective coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary := by
  intro u v huv
  apply Subtype.ext
  exact congrArg (fun a : CoordinateUnlinkExteriorPuncturedNormalDisk ↦ a.1.1) huv

/-- The displayed outer boundary is a topological embedding. -/
theorem isEmbedding_coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary :
    IsEmbedding coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary :=
  continuous_coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary.isClosedEmbedding
    injective_coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary |>.isEmbedding

/-- The one-handle and planar character formulas agree on their displayed common boundary. -/
theorem coordinateUnlinkExteriorBoundaryCharacter_eq_planarOuterBoundary
    (u : Sphere 1) (s : Sphere 2) :
    ((coordinateUnlinkExteriorPushoutRightNormalMap ∘
          coordinateUnlinkExteriorPushoutOneHandleInclusion) ∘
        oneHandleBoundaryInclusion) (u, s) =
      coordinateUnlinkExteriorPuncturedNormalDiskCharacter
        (coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary u) := by
  have hpush := congrArg coordinateUnlinkExteriorPushoutRightNormalMap
    (topologicalPushout_condition oneHandleBoundaryInclusion
      (unlinkPuncturedCapBoundaryInclusion
        oneEighth_lt_sphereHandleRadius_sub_half) (u, s))
  rw [coordinateUnlinkExteriorPushoutRightNormalMap_puncturedCap_eq_planar] at hpush
  exact hpush.trans <| congrArg coordinateUnlinkExteriorPuncturedNormalDiskCharacter <| by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The raw power pullback restricted to the displayed planar outer boundary. -/
abbrev CoordinateUnlinkExteriorPlanarOuterBoundaryPowerPullback (m : ℕ) : Type :=
  TopologicalCoverPullback (nonzeroComplexPow m)
    (coordinateUnlinkExteriorPuncturedNormalDiskCharacter ∘
      coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary)

/-- The outer-boundary lift, before including it into the whole planar pullback. -/
def coordinateUnlinkExteriorPlanarOuterBoundaryLift
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    CoordinateUnlinkExteriorPlanarOuterBoundaryPowerPullback m :=
  ⟨(unlinkUnitCirclePow m u,
      (coordinateUnlinkExteriorPlanarOuterLift m u).1.2), by
    rw [Function.comp_apply, ← coordinateUnlinkExteriorPlanarOuterLift_proj]
    exact (coordinateUnlinkExteriorPlanarOuterLift m u).2⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterBoundaryLift_proj
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    topologicalCoverPullbackProj (nonzeroComplexPow m)
        (coordinateUnlinkExteriorPuncturedNormalDiskCharacter ∘
          coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary)
        (coordinateUnlinkExteriorPlanarOuterBoundaryLift m u) =
      unlinkUnitCirclePow m u :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterBoundaryLift_powerCoordinate
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    (coordinateUnlinkExteriorPlanarOuterBoundaryLift m u).1.2 =
      (coordinateUnlinkExteriorPlanarOuterLift m u).1.2 :=
  rfl

theorem continuous_coordinateUnlinkExteriorPlanarOuterBoundaryLift
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarOuterBoundaryLift m) := by
  apply Continuous.subtype_mk
  exact (continuous_unlinkUnitCirclePow m).prodMk <|
    (continuous_snd.comp <|
      continuous_subtype_val.comp
        (continuous_coordinateUnlinkExteriorPlanarOuterLift m))

/-- Retag a point of the outer-boundary pullback as a point of the common-boundary pullback,
using the fixed `S²` coordinate. -/
def coordinateUnlinkExteriorPlanarOuterBoundaryToBoundaryPullback
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarOuterBoundaryPowerPullback m) :
    CoordinateUnlinkExteriorBoundaryPowerPullback m :=
  ⟨((z.1.1, coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint), z.1.2), by
    rw [coordinateUnlinkExteriorBoundaryCharacter_eq_planarOuterBoundary]
    exact z.2⟩

theorem continuous_coordinateUnlinkExteriorPlanarOuterBoundaryToBoundaryPullback
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarOuterBoundaryToBoundaryPullback m) := by
  apply Continuous.subtype_mk
  exact ((continuous_fst.comp continuous_subtype_val).prodMk continuous_const).prodMk
    (continuous_snd.comp continuous_subtype_val)

/-- Recover the circle parameter by applying the inverse boundary trivialization. -/
def coordinateUnlinkExteriorPlanarOuterBoundaryLiftInverse
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarOuterBoundaryPowerPullback m) : Sphere 1 :=
  ((coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m).symm
    (coordinateUnlinkExteriorPlanarOuterBoundaryToBoundaryPullback m z)).1

theorem continuous_coordinateUnlinkExteriorPlanarOuterBoundaryLiftInverse
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarOuterBoundaryLiftInverse m) :=
  continuous_fst.comp <|
    (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m).symm.continuous.comp
      (continuous_coordinateUnlinkExteriorPlanarOuterBoundaryToBoundaryPullback m)

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterBoundaryToBoundaryPullback_lift
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarOuterBoundaryToBoundaryPullback m
        (coordinateUnlinkExteriorPlanarOuterBoundaryLift m u) =
      coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m
        (u, coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact coordinateUnlinkExteriorPlanarOuterLift_powerCoordinate m u

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterBoundaryLiftInverse_lift
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarOuterBoundaryLiftInverse m
        (coordinateUnlinkExteriorPlanarOuterBoundaryLift m u) = u := by
  rw [coordinateUnlinkExteriorPlanarOuterBoundaryLiftInverse,
    coordinateUnlinkExteriorPlanarOuterBoundaryToBoundaryPullback_lift,
    (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m).symm_apply_apply]

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterBoundaryLift_liftInverse
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarOuterBoundaryPowerPullback m) :
    coordinateUnlinkExteriorPlanarOuterBoundaryLift m
        (coordinateUnlinkExteriorPlanarOuterBoundaryLiftInverse m z) = z := by
  let b := coordinateUnlinkExteriorPlanarOuterBoundaryToBoundaryPullback m z
  let x := (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m).symm b
  have hx : coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m x = b :=
    (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m).apply_symm_apply b
  change coordinateUnlinkExteriorPlanarOuterBoundaryLift m x.1 = z
  apply Subtype.ext
  apply Prod.ext
  · have hbase := congrArg
      (fun w : CoordinateUnlinkExteriorBoundaryPowerPullback m ↦ w.1.1.1) hx
    exact hbase
  · have hfiber := congrArg
      (fun w : CoordinateUnlinkExteriorBoundaryPowerPullback m ↦ w.1.2) hx
    calc
      (coordinateUnlinkExteriorPlanarOuterBoundaryLift m x.1).1.2 =
          (coordinateUnlinkExteriorPlanarOuterLift m x.1).1.2 := rfl
      _ = (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m
          (x.1, coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint)).1.2 :=
        coordinateUnlinkExteriorPlanarOuterLift_powerCoordinate m x.1
      _ = (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m x).1.2 :=
        coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph_powerCoordinate_eq
          m x.1 coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint x.2
      _ = z.1.2 := hfiber

/-- The explicit lift trivializes the whole pullback over the displayed outer boundary. -/
def coordinateUnlinkExteriorPlanarOuterBoundaryLiftHomeomorph
    (m : ℕ) [NeZero m] :
    Sphere 1 ≃ₜ CoordinateUnlinkExteriorPlanarOuterBoundaryPowerPullback m where
  toFun := coordinateUnlinkExteriorPlanarOuterBoundaryLift m
  invFun := coordinateUnlinkExteriorPlanarOuterBoundaryLiftInverse m
  left_inv := coordinateUnlinkExteriorPlanarOuterBoundaryLiftInverse_lift m
  right_inv := coordinateUnlinkExteriorPlanarOuterBoundaryLift_liftInverse m
  continuous_toFun := continuous_coordinateUnlinkExteriorPlanarOuterBoundaryLift m
  continuous_invFun := continuous_coordinateUnlinkExteriorPlanarOuterBoundaryLiftInverse m

/-! ## Exact image in the whole planar pullback -/

/-- The exact part of the planar pullback lying above the range of the displayed outer
boundary. -/
def coordinateUnlinkExteriorPlanarOuterBoundaryCarrier (m : ℕ) :
    Set (CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :=
  topologicalCoverPullbackRestrictionRange (nonzeroComplexPow m)
    coordinateUnlinkExteriorPuncturedNormalDiskCharacter
    coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary

@[simp]
theorem mem_coordinateUnlinkExteriorPlanarOuterBoundaryCarrier
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    z ∈ coordinateUnlinkExteriorPlanarOuterBoundaryCarrier m ↔
      coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj m z ∈
        Set.range coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary :=
  Iff.rfl

/-- The outer lift is a homeomorphism onto the exact projection-preimage of the displayed
outer-boundary range. -/
def coordinateUnlinkExteriorPlanarOuterBoundaryHomeomorph
    (m : ℕ) [NeZero m] :
    Sphere 1 ≃ₜ coordinateUnlinkExteriorPlanarOuterBoundaryCarrier m :=
  (coordinateUnlinkExteriorPlanarOuterBoundaryLiftHomeomorph m).trans <|
    topologicalCoverPullbackRestrictionRangeHomeomorph
      (nonzeroComplexPow m)
      coordinateUnlinkExteriorPuncturedNormalDiskCharacter
      coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary
      isEmbedding_coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterBoundaryHomeomorph_apply_coe
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    ((coordinateUnlinkExteriorPlanarOuterBoundaryHomeomorph m u :
        coordinateUnlinkExteriorPlanarOuterBoundaryCarrier m) :
      CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) =
      coordinateUnlinkExteriorPlanarOuterLift m u := by
  apply Subtype.ext
  apply Prod.ext
  · exact (coordinateUnlinkExteriorPlanarOuterLift_proj m u).symm
  · rfl

/-- The planar outer lift is injective. -/
theorem injective_coordinateUnlinkExteriorPlanarOuterLift
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarOuterLift m) := by
  intro u v huv
  apply (coordinateUnlinkExteriorPlanarOuterBoundaryHomeomorph m).injective
  apply Subtype.ext
  simpa using huv

/-- The planar outer lift is a topological embedding. -/
theorem isEmbedding_coordinateUnlinkExteriorPlanarOuterLift
    (m : ℕ) [NeZero m] :
    IsEmbedding (coordinateUnlinkExteriorPlanarOuterLift m) :=
  (continuous_coordinateUnlinkExteriorPlanarOuterLift m).isClosedEmbedding
    (injective_coordinateUnlinkExteriorPlanarOuterLift m) |>.isEmbedding

/-- Set-level form of the exact outer-boundary image identification. -/
theorem range_coordinateUnlinkExteriorPlanarOuterLift
    (m : ℕ) [NeZero m] :
    Set.range (coordinateUnlinkExteriorPlanarOuterLift m) =
      coordinateUnlinkExteriorPlanarOuterBoundaryCarrier m := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact (coordinateUnlinkExteriorPlanarOuterBoundaryHomeomorph m u).2
  · intro hz
    let z' : coordinateUnlinkExteriorPlanarOuterBoundaryCarrier m := ⟨z, hz⟩
    refine ⟨(coordinateUnlinkExteriorPlanarOuterBoundaryHomeomorph m).symm z', ?_⟩
    have h := congrArg Subtype.val
      ((coordinateUnlinkExteriorPlanarOuterBoundaryHomeomorph m).apply_symm_apply z')
    rw [coordinateUnlinkExteriorPlanarOuterBoundaryHomeomorph_apply_coe] at h
    exact h

end SplittingSpheres
