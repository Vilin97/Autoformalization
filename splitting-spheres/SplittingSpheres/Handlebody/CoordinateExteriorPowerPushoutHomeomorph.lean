/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPowerCompactness

/-!
# Gluing the coordinate-exterior power cover

For nonzero degree, the pushout of the two restricted power pullbacks is compact.  Composing its
canonical continuous bijection with the established base-change homeomorphism lands in the
Hausdorff literal-exterior pullback, so compact-to-Hausdorff recognition upgrades the bijection
to a homeomorphism.  Transporting back gives the desired homeomorphism onto the global pullback
over the exterior pushout.

No smooth structure on any of these topological pushouts is asserted.
-/

@[expose] public section

noncomputable section

open Function Topology

namespace SplittingSpheres

/-- The underlying equivalence from the glued piece pullbacks to the literal closed-exterior
pullback. -/
def coordinateUnlinkExteriorPowerPullbackPushoutExteriorEquiv (m : ℕ) :
    CoordinateUnlinkExteriorPowerPullbackPushout m ≃
      CoordinateUnlinkExteriorEighthPowerPullback m :=
  (coordinateUnlinkExteriorPowerPullbackPushoutEquiv m).trans
    (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).toEquiv

@[simp]
theorem coordinateUnlinkExteriorPowerPullbackPushoutExteriorEquiv_apply
    (m : ℕ) (z : CoordinateUnlinkExteriorPowerPullbackPushout m) :
    coordinateUnlinkExteriorPowerPullbackPushoutExteriorEquiv m z =
      coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m
        (coordinateUnlinkExteriorPowerPullbackPushoutDesc m z) :=
  rfl

/-- The glued piece pullbacks are homeomorphic to the literal closed-exterior pullback. -/
def coordinateUnlinkExteriorPowerPullbackPushoutExteriorHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPowerPullbackPushout m ≃ₜ
      CoordinateUnlinkExteriorEighthPowerPullback m := by
  let _ := compactSpace_coordinateUnlinkExteriorPowerPullbackPushout m
  exact Continuous.homeoOfEquivCompactToT2
    (f := coordinateUnlinkExteriorPowerPullbackPushoutExteriorEquiv m)
    ((coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).continuous.comp
      (continuous_coordinateUnlinkExteriorPowerPullbackPushoutEquiv m))

@[simp]
theorem coordinateUnlinkExteriorPowerPullbackPushoutExteriorHomeomorph_apply
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPowerPullbackPushout m) :
    coordinateUnlinkExteriorPowerPullbackPushoutExteriorHomeomorph m z =
      coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m
        (coordinateUnlinkExteriorPowerPullbackPushoutDesc m z) :=
  rfl

/-- The topological pushout of the restricted piece pullbacks is the global power pullback over
the exterior pushout. -/
def coordinateUnlinkExteriorPowerPullbackPushoutHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPowerPullbackPushout m ≃ₜ
      CoordinateUnlinkExteriorPushoutPowerPullback m :=
  (coordinateUnlinkExteriorPowerPullbackPushoutExteriorHomeomorph m).trans
    (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).symm

@[simp]
theorem coordinateUnlinkExteriorPowerPullbackPushoutHomeomorph_apply
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPowerPullbackPushout m) :
    coordinateUnlinkExteriorPowerPullbackPushoutHomeomorph m z =
      coordinateUnlinkExteriorPowerPullbackPushoutDesc m z := by
  simp [coordinateUnlinkExteriorPowerPullbackPushoutHomeomorph]

@[simp]
theorem coordinateUnlinkExteriorPowerPullbackPushoutHomeomorph_inl
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    coordinateUnlinkExteriorPowerPullbackPushoutHomeomorph m
        (topologicalPushoutInl
          ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m,
            continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m⟩
          ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m,
            continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m⟩ z) =
      coordinateUnlinkExteriorOneHandlePowerPullbackToPushout m z := by
  rw [coordinateUnlinkExteriorPowerPullbackPushoutHomeomorph_apply,
    coordinateUnlinkExteriorPowerPullbackPushoutDesc_inl]

@[simp]
theorem coordinateUnlinkExteriorPowerPullbackPushoutHomeomorph_inr
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPuncturedCapPowerPullback m) :
    coordinateUnlinkExteriorPowerPullbackPushoutHomeomorph m
        (topologicalPushoutInr
          ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m,
            continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m⟩
          ⟨coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m,
            continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToPuncturedCap m⟩ z) =
      coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout m z := by
  rw [coordinateUnlinkExteriorPowerPullbackPushoutHomeomorph_apply,
    coordinateUnlinkExteriorPowerPullbackPushoutDesc_inr]

end SplittingSpheres
