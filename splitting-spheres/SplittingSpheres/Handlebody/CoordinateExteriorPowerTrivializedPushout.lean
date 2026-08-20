/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutCongr
public import SplittingSpheres.Handlebody.CoordinateExteriorBoundaryCover
public import SplittingSpheres.Handlebody.CoordinateExteriorPowerPushoutHomeomorph
public import SplittingSpheres.Handlebody.CoordinateExteriorPuncturedCapProduct

/-!
# The exterior power cover as a pushout of trivialized pieces

The lifted one-handle is explicitly another `S¹ × B³`, the lifted attaching boundary is another
`S¹ × S²`, and the lifted punctured cap is a planar power pullback times `S²`.  Transporting the
three parts of the already proved total-space pushout along those homeomorphisms gives a literal
pushout of these trivialized pieces, homeomorphic to the global exterior power pullback.

The remaining geometric problem is now isolated in the planar power pullback and its outer
boundary inclusion.  No surface-classification, graph-thickening, or smooth claim is made here.
-/

@[expose] public section

noncomputable section

open Function Topology

namespace SplittingSpheres

/-- The outer unit-circle boundary of the punctured normal disk.  Its membership proof is
obtained from the already established retained cap boundary; the underlying coordinate is
literally `u`. -/
def coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary
    (u : Sphere 1) : CoordinateUnlinkExteriorPuncturedNormalDisk :=
  ⟨⟨u.1, Metric.sphere_subset_closedBall u.2⟩, by
    let s : Sphere 2 := Classical.choice <| by
      obtain ⟨s⟩ :=
        (NormedSpace.sphere_nonempty
          (E := EuclideanSpace ℝ (Fin 3)) (x := 0) (r := 1) |>.mpr zero_le_one).to_subtype
      exact ⟨s⟩
    let z : UnlinkPuncturedCap (1 / 8 : ℝ) :=
      unlinkPuncturedCapBoundaryInclusion
        oneEighth_lt_sphereHandleRadius_sub_half (u, s)
    have hz :=
      (coordinateUnlinkExteriorPuncturedCapProductHomeomorph z).1.2
    exact hz⟩

@[simp]
theorem coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary_val
    (u : Sphere 1) :
    (coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary u).1.1 = u.1 :=
  rfl

theorem continuous_coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary :
    Continuous coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary :=
  ((continuous_subtype_val : Continuous fun u : Sphere 1 ↦ u.1).subtype_mk _).subtype_mk _

/-- On the outer boundary, the planar character is the displayed circle of radius
`sphereHandleRadius` centered at `-1/2`. -/
@[simp]
theorem coordinateUnlinkExteriorPuncturedNormalDiskCharacter_outerBoundary
    (u : Sphere 1) :
    (coordinateUnlinkExteriorPuncturedNormalDiskCharacter
        (coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary u) : ℂ) =
      (sphereHandleRadius : ℂ) * unlinkUnitCircleComplex u - (1 / 2 : ℂ) := by
  rw [coordinateUnlinkExteriorPuncturedNormalDiskCharacter_coe]
  simp [unlinkUnitCircleComplex, unlinkNormalPlaneToComplex,
    standardUnlinkNormalCenter, standardUnlinkHeight,
    Complex.equivRealProdCLM_symm_apply]
  ring

/-- The attaching map from the trivialized lifted boundary into the product decomposition of the
lifted punctured cap. -/
def coordinateUnlinkExteriorTrivializedCapBoundaryInclusion
    (m : ℕ) [NeZero m] :
    C(OneHandleCapBoundary,
      CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2) where
  toFun x :=
    coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m
      (coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m
        (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m x))
  continuous_toFun :=
    (coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m).continuous.comp
      ((continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m).comp
        (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m).continuous)

@[simp]
theorem coordinateUnlinkExteriorTrivializedCapBoundaryInclusion_planarBase
    (m : ℕ) [NeZero m] (x : OneHandleCapBoundary) :
    coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj m
        (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m x).1 =
      coordinateUnlinkExteriorPuncturedNormalDiskOuterBoundary
        (unlinkUnitCirclePow m x.1) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

@[simp]
theorem coordinateUnlinkExteriorTrivializedCapBoundaryInclusion_powerCoordinate
    (m : ℕ) [NeZero m] (x : OneHandleCapBoundary) :
    (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m x).1.1.2 =
      (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m x).1.2 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorTrivializedCapBoundaryInclusion_sphereCoordinate
    (m : ℕ) [NeZero m] (x : OneHandleCapBoundary) :
    (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m x).2 = x.2 :=
  rfl

/-- The total-space pushout after trivializing the lifted boundary and both lifted pieces. -/
abbrev CoordinateUnlinkExteriorTrivializedPowerPullbackPushout
    (m : ℕ) [NeZero m] : Type :=
  TopologicalPushout oneHandleBoundaryInclusion
    (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m)

theorem coordinateUnlinkExteriorPowerPullback_trivialized_left_compatibility
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m).symm
        (coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m z) =
      oneHandleBoundaryInclusion
        ((coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m).symm z) :=
  (oneHandleBoundaryInclusion_boundaryPowerPullbackHomeomorph_symm m z).symm

theorem coordinateUnlinkExteriorPowerPullback_trivialized_right_compatibility
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m
        (coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m z) =
      coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m
        ((coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m).symm z) := by
  change coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m
      (coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m z) =
    coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m
      (coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m
        (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m
          ((coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m).symm z)))
  rw [(coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m).apply_symm_apply]

/-- Transport the proved pushout of restricted pullbacks to the diagram of explicit trivialized
pieces. -/
def coordinateUnlinkExteriorPowerPullbackPushoutTrivialization
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPowerPullbackPushout m ≃ₜ
      CoordinateUnlinkExteriorTrivializedPowerPullbackPushout m :=
  topologicalPushoutCongr
    ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m,
      continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m⟩
    ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m,
      continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m⟩
    oneHandleBoundaryInclusion
    (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m)
    (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m).symm
    (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m).symm
    (coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m)
    (coordinateUnlinkExteriorPowerPullback_trivialized_left_compatibility m)
    (coordinateUnlinkExteriorPowerPullback_trivialized_right_compatibility m)

/-- The trivialized lifted-piece pushout is the global power pullback over the coordinate
exterior pushout. -/
def coordinateUnlinkExteriorTrivializedPowerPullbackPushoutHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorTrivializedPowerPullbackPushout m ≃ₜ
      CoordinateUnlinkExteriorPushoutPowerPullback m :=
  (coordinateUnlinkExteriorPowerPullbackPushoutTrivialization m).symm.trans
    (coordinateUnlinkExteriorPowerPullbackPushoutHomeomorph m)

@[simp]
theorem coordinateUnlinkExteriorTrivializedPowerPullbackPushoutHomeomorph_inl
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    coordinateUnlinkExteriorTrivializedPowerPullbackPushoutHomeomorph m
        (topologicalPushoutInl oneHandleBoundaryInclusion
          (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m) x) =
      coordinateUnlinkExteriorOneHandlePowerPullbackToPushout m
        (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m x) := by
  change coordinateUnlinkExteriorPowerPullbackPushoutHomeomorph m
      ((coordinateUnlinkExteriorPowerPullbackPushoutTrivialization m).symm
        (topologicalPushoutInl oneHandleBoundaryInclusion
          (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m) x)) = _
  rw [show
    (coordinateUnlinkExteriorPowerPullbackPushoutTrivialization m).symm
        (topologicalPushoutInl oneHandleBoundaryInclusion
          (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m) x) =
      topologicalPushoutInl
        ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m,
          continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m⟩
        ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m,
          continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m⟩
        (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m x) by
      exact topologicalPushoutCongr_symm_inl
        ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m,
          continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m⟩
        ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m,
          continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m⟩
        oneHandleBoundaryInclusion
        (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m)
        (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m).symm
        (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m).symm
        (coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m)
        (coordinateUnlinkExteriorPowerPullback_trivialized_left_compatibility m)
        (coordinateUnlinkExteriorPowerPullback_trivialized_right_compatibility m) x]
  exact coordinateUnlinkExteriorPowerPullbackPushoutHomeomorph_inl m _

@[simp]
theorem coordinateUnlinkExteriorTrivializedPowerPullbackPushoutHomeomorph_inr
    (m : ℕ) [NeZero m]
    (y : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m × Sphere 2) :
    coordinateUnlinkExteriorTrivializedPowerPullbackPushoutHomeomorph m
        (topologicalPushoutInr oneHandleBoundaryInclusion
          (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m) y) =
      coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout m
        ((coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m).symm y) := by
  change coordinateUnlinkExteriorPowerPullbackPushoutHomeomorph m
      ((coordinateUnlinkExteriorPowerPullbackPushoutTrivialization m).symm
        (topologicalPushoutInr oneHandleBoundaryInclusion
          (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m) y)) = _
  rw [show
    (coordinateUnlinkExteriorPowerPullbackPushoutTrivialization m).symm
        (topologicalPushoutInr oneHandleBoundaryInclusion
          (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m) y) =
      topologicalPushoutInr
        ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m,
          continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m⟩
        ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m,
          continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m⟩
        ((coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m).symm y) by
      exact topologicalPushoutCongr_symm_inr
        ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m,
          continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m⟩
        ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m,
          continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m⟩
        oneHandleBoundaryInclusion
        (coordinateUnlinkExteriorTrivializedCapBoundaryInclusion m)
        (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m).symm
        (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m).symm
        (coordinateUnlinkExteriorPuncturedCapPowerPullbackProductHomeomorph m)
        (coordinateUnlinkExteriorPowerPullback_trivialized_left_compatibility m)
        (coordinateUnlinkExteriorPowerPullback_trivialized_right_compatibility m) y]
  exact coordinateUnlinkExteriorPowerPullbackPushoutHomeomorph_inr m _

end SplittingSpheres
