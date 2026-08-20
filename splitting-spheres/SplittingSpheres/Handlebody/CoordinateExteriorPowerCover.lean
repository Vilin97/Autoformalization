/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalCoverPullbackBaseHomeomorph
public import SplittingSpheres.Geometry.UnlinkExteriorPowerDeck
public import SplittingSpheres.Handlebody.CoordinateUnlinkExteriorDecomposition

/-!
# The power cover on the coordinate-exterior pushout

The radius-`1/8` coordinate exterior is already recognized as a pushout of the whole one-handle
piece and a punctured cap.  Pulling the nonzero-complex power map back along the transported
right-normal coordinate gives an explicit cover of that pushout.  Its total space is canonically
homeomorphic to the closed-exterior power pullback, so every nonzero-degree fiber has exactly
`m` points.

This remains point-set topology.  In particular, it neither equips the punctured-cap pushout with
a smooth boundary atlas nor identifies the total space with a graph-thickened handlebody.
-/

@[expose] public section

noncomputable section

open Function Topology

namespace SplittingSpheres

/-- The right-normal coordinate transported to the concrete radius-`1/8` exterior pushout. -/
def coordinateUnlinkExteriorPushoutRightNormalMap :
    CoordinateUnlinkExteriorPushout oneEighth_lt_sphereHandleRadius_sub_half →
      {z : ℂ // z ≠ 0} :=
  coordinateUnlinkExteriorEighthRightNormalMap ∘
    coordinateUnlinkExteriorOneEighthHomeomorph

theorem continuous_coordinateUnlinkExteriorPushoutRightNormalMap :
    Continuous coordinateUnlinkExteriorPushoutRightNormalMap :=
  continuous_coordinateUnlinkExteriorEighthRightNormalMap.comp
    coordinateUnlinkExteriorOneEighthHomeomorph.continuous

/-- The raw power-map pullback over the topological exterior pushout. -/
abbrev CoordinateUnlinkExteriorPushoutPowerPullback (m : ℕ) :=
  TopologicalCoverPullback (nonzeroComplexPow m)
    coordinateUnlinkExteriorPushoutRightNormalMap

/-- Projection of the power pullback over the exterior pushout. -/
def coordinateUnlinkExteriorPushoutPowerPullbackProj (m : ℕ) :
    CoordinateUnlinkExteriorPushoutPowerPullback m →
      CoordinateUnlinkExteriorPushout oneEighth_lt_sphereHandleRadius_sub_half :=
  topologicalCoverPullbackProj (nonzeroComplexPow m)
    coordinateUnlinkExteriorPushoutRightNormalMap

@[simp]
theorem coordinateUnlinkExteriorPushoutPowerPullbackProj_apply (m : ℕ)
    (z : CoordinateUnlinkExteriorPushoutPowerPullback m) :
    coordinateUnlinkExteriorPushoutPowerPullbackProj m z = z.1.1 :=
  rfl

/-- Changing the pushout base coordinate by the established exterior homeomorphism gives the
literal closed-exterior power pullback. -/
def coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph (m : ℕ) :
    CoordinateUnlinkExteriorPushoutPowerPullback m ≃ₜ
      CoordinateUnlinkExteriorEighthPowerPullback m :=
  topologicalCoverPullbackBaseHomeomorph (nonzeroComplexPow m)
    coordinateUnlinkExteriorEighthRightNormalMap
    coordinateUnlinkExteriorOneEighthHomeomorph

@[simp]
theorem coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_proj
    (m : ℕ) (z : CoordinateUnlinkExteriorPushoutPowerPullback m) :
    coordinateUnlinkExteriorEighthPowerPullbackProj m
        (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m z) =
      coordinateUnlinkExteriorOneEighthHomeomorph
        (coordinateUnlinkExteriorPushoutPowerPullbackProj m z) :=
  rfl

/-- For nonzero degree, the power pullback over the exterior pushout is a topological cover. -/
theorem isCoveringMap_coordinateUnlinkExteriorPushoutPowerPullbackProj
    (m : ℕ) [NeZero m] :
    IsCoveringMap (coordinateUnlinkExteriorPushoutPowerPullbackProj m) :=
  SplittingSpheres.IsCoveringMap.pullback
    (isCoveringMap_nonzeroComplexPow m)
    continuous_coordinateUnlinkExteriorPushoutRightNormalMap

/-- Every fiber of the nonzero-degree pushout cover has exactly `m` points. -/
theorem natCard_coordinateUnlinkExteriorPushoutPowerPullbackProj_fiber
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPushout oneEighth_lt_sphereHandleRadius_sub_half) :
    Nat.card (coordinateUnlinkExteriorPushoutPowerPullbackProj m ⁻¹' {x}) = m := by
  calc
    Nat.card (coordinateUnlinkExteriorPushoutPowerPullbackProj m ⁻¹' {x}) =
        Nat.card (nonzeroComplexPow m ⁻¹'
          {coordinateUnlinkExteriorPushoutRightNormalMap x}) :=
      Nat.card_congr (topologicalCoverPullbackFiberEquiv
        (nonzeroComplexPow m) coordinateUnlinkExteriorPushoutRightNormalMap x)
    _ = m := natCard_nonzeroComplexPow_fiber m _

end SplittingSpheres
