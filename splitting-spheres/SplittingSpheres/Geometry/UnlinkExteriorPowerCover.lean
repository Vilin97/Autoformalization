/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkCyclicCover

/-!
# The power cover over the compact coordinate exterior

The handlebody decomposition uses the closed radius-`1/8` coordinate exterior, whereas the
smooth isotopy relation naturally lives in the strict link complement.  This file constructs the
same power-map pullback directly over the closed exterior.  It is a topological covering with
exactly `m` points in every fiber for `m ≠ 0`; no manifold-with-boundary structure on the base or
total space is asserted.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-- The right-normal complex coordinate on the closed radius-`1/8` coordinate exterior. -/
def coordinateUnlinkExteriorEighthRightNormalMap :
    ↑(coordinateUnlinkExterior (1 / 8 : ℝ)) → {z : ℂ // z ≠ 0} :=
  standardUnlinkRightNormalMap ∘ coordinateUnlinkExteriorToComplement (by norm_num)

@[simp]
theorem coordinateUnlinkExteriorEighthRightNormalMap_coe
    (x : ↑(coordinateUnlinkExterior (1 / 8 : ℝ))) :
    (coordinateUnlinkExteriorEighthRightNormalMap x : ℂ) =
      standardUnlinkRightDisplacementComplex x.1 :=
  rfl

theorem continuous_coordinateUnlinkExteriorEighthRightNormalMap :
    Continuous coordinateUnlinkExteriorEighthRightNormalMap :=
  continuous_standardUnlinkRightNormalMap.comp
    (continuous_coordinateUnlinkExteriorToComplement (by norm_num))

/-- The raw power-map pullback over the closed radius-`1/8` exterior. -/
abbrev CoordinateUnlinkExteriorEighthPowerPullback (m : ℕ) :=
  TopologicalCoverPullback (nonzeroComplexPow m)
    coordinateUnlinkExteriorEighthRightNormalMap

/-- Projection of the closed-exterior power pullback. -/
def coordinateUnlinkExteriorEighthPowerPullbackProj (m : ℕ) :
    CoordinateUnlinkExteriorEighthPowerPullback m →
      ↑(coordinateUnlinkExterior (1 / 8 : ℝ)) :=
  topologicalCoverPullbackProj (nonzeroComplexPow m)
    coordinateUnlinkExteriorEighthRightNormalMap

@[simp]
theorem coordinateUnlinkExteriorEighthPowerPullbackProj_apply (m : ℕ)
    (z : CoordinateUnlinkExteriorEighthPowerPullback m) :
    coordinateUnlinkExteriorEighthPowerPullbackProj m z = z.1.1 :=
  rfl

/-- For nonzero degree, the closed-exterior power pullback is a topological covering. -/
theorem isCoveringMap_coordinateUnlinkExteriorEighthPowerPullbackProj
    (m : ℕ) [NeZero m] :
    IsCoveringMap (coordinateUnlinkExteriorEighthPowerPullbackProj m) :=
  SplittingSpheres.IsCoveringMap.pullback
    (isCoveringMap_nonzeroComplexPow m)
    continuous_coordinateUnlinkExteriorEighthRightNormalMap

/-- Every fiber of the nonzero-degree closed-exterior power cover has exactly `m` points. -/
theorem natCard_coordinateUnlinkExteriorEighthPowerPullbackProj_fiber
    (m : ℕ) [NeZero m] (x : ↑(coordinateUnlinkExterior (1 / 8 : ℝ))) :
    Nat.card (coordinateUnlinkExteriorEighthPowerPullbackProj m ⁻¹' {x}) = m := by
  calc
    Nat.card (coordinateUnlinkExteriorEighthPowerPullbackProj m ⁻¹' {x}) =
        Nat.card (nonzeroComplexPow m ⁻¹'
          {coordinateUnlinkExteriorEighthRightNormalMap x}) :=
      Nat.card_congr (topologicalCoverPullbackFiberEquiv
        (nonzeroComplexPow m) coordinateUnlinkExteriorEighthRightNormalMap x)
    _ = m := natCard_nonzeroComplexPow_fiber m _

end SplittingSpheres
