/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothCoverPullbackAtlas
public import SplittingSpheres.Geometry.UnlinkComplementExteriorPowerHomeomorph

/-!
# The smooth power cover of the strict closed-tube exterior

For nonzero degree, the literal power pullback over the complement of the two closed radius-
`1 / 8` tubes is a topological covering.  Pulling back the inherited open-submanifold atlas of
the base gives the total space a smooth four-manifold atlas for which the projection is a smooth
cover.

This file only constructs that atlas and records the projection properties.  It does not claim
that any previously constructed radial homeomorphism is smooth.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Manifold

namespace SplittingSpheres

/-- The literal strict-exterior power-pullback projection is a covering map in nonzero degree. -/
theorem isCoveringMap_standardUnlinkClosedTubeExteriorPowerPullbackProj
    (m : ℕ) [NeZero m] :
    IsCoveringMap (standardUnlinkClosedTubeExteriorPowerPullbackProj m) :=
  SplittingSpheres.IsCoveringMap.pullback
    (isCoveringMap_nonzeroComplexPow m)
    continuous_standardUnlinkClosedTubeExteriorRightNormalMap

/-- The smooth atlas on the strict-exterior power pullback, pulled back along its projection. -/
abbrev standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace
    (m : ℕ) [NeZero m] :
    ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
  SplittingSpheres.IsCoveringMap.pullbackChartedSpace
    (isCoveringMap_standardUnlinkClosedTubeExteriorPowerPullbackProj m)

/-- The pulled-back atlas makes the strict-exterior power pullback a smooth four-manifold. -/
theorem isManifold_standardUnlinkClosedTubeExteriorPowerPullback
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    IsManifold (𝓡 4) ∞ (StandardUnlinkClosedTubeExteriorPowerPullback m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
    standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
  exact SplittingSpheres.IsCoveringMap.isManifold_pullbackChartedSpace
    (𝓡 4) ∞
      (isCoveringMap_standardUnlinkClosedTubeExteriorPowerPullbackProj m)

/-- The strict-exterior power-pullback projection is a local diffeomorphism. -/
theorem isLocalDiffeomorph_standardUnlinkClosedTubeExteriorPowerPullbackProj
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
    IsLocalDiffeomorph (𝓡 4) (𝓡 4) ∞
      (standardUnlinkClosedTubeExteriorPowerPullbackProj m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
    standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞
      (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
    isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
  exact SplittingSpheres.IsCoveringMap.isLocalDiffeomorph_pullbackChartedSpace
    (𝓡 4) ∞
      (isCoveringMap_standardUnlinkClosedTubeExteriorPowerPullbackProj m)

/-- The strict-exterior power-pullback projection is smooth. -/
theorem contMDiff_standardUnlinkClosedTubeExteriorPowerPullbackProj
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
    ContMDiff (𝓡 4) (𝓡 4) ∞
      (standardUnlinkClosedTubeExteriorPowerPullbackProj m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
    standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞
      (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
    isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
  exact
    (isLocalDiffeomorph_standardUnlinkClosedTubeExteriorPowerPullbackProj m).contMDiff

/-- The strict-exterior power-pullback projection is a smooth covering map. -/
theorem smoothCover_standardUnlinkClosedTubeExteriorPowerPullbackProj
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
    SmoothCover (𝓡 4) (𝓡 4) ∞
      (standardUnlinkClosedTubeExteriorPowerPullbackProj m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
    standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞
      (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
    isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
  exact SplittingSpheres.IsCoveringMap.smoothCover_pullbackChartedSpace
    (𝓡 4) ∞
      (isCoveringMap_standardUnlinkClosedTubeExteriorPowerPullbackProj m)

end SplittingSpheres
