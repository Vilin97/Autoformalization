/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import SplittingSpheres.Foundations.SmoothCoverPullbackAtlas
public import SplittingSpheres.Geometry.CoordinateUnlinkExteriorSmoothAtlas
public import SplittingSpheres.Geometry.UnlinkExteriorPowerCover

/-!
# The smooth power cover of the coordinate unlink exterior

The power pullback over the literal radius-`1 / 8` coordinate unlink exterior is a topological
covering of the smooth manifold with corners constructed in
`CoordinateUnlinkExteriorSmoothAtlas`. Pulling back that atlas along the covering projection
makes the total space a smooth four-manifold with corners. In this atlas the projection is a
local diffeomorphism and a smooth covering map, and the model boundary is exactly the inverse
image of the two radial boundary faces downstairs.

This file asserts only the pulled-back smooth structure and its formal consequences. It makes no
claim about radial collars, complements, capping pushouts, or compatibility with other atlases on
the total space.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Manifold

namespace SplittingSpheres

/-- The atlas on the exterior power pullback obtained from its actual covering projection. -/
abbrev coordinateUnlinkExteriorEighthPowerPullbackChartedSpace
    (m : ℕ) [NeZero m] :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) := by
  letI := coordinateUnlinkExteriorEighthChartedSpace
  exact SplittingSpheres.IsCoveringMap.pullbackChartedSpace
    (isCoveringMap_coordinateUnlinkExteriorEighthPowerPullbackProj m)

/-- The pulled-back atlas makes the exterior power pullback a smooth four-manifold with
corners. -/
theorem isManifold_coordinateUnlinkExteriorEighthPowerPullback
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact SplittingSpheres.IsCoveringMap.isManifold_pullbackChartedSpace
    coordinateUnlinkExteriorModel ∞
      (isCoveringMap_coordinateUnlinkExteriorEighthPowerPullbackProj m)

/-- The exterior power-pullback projection is a local diffeomorphism for the pulled-back
atlas. -/
theorem isLocalDiffeomorph_coordinateUnlinkExteriorEighthPowerPullbackProj
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorEighthPowerPullbackProj m) := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  exact SplittingSpheres.IsCoveringMap.isLocalDiffeomorph_pullbackChartedSpace
    coordinateUnlinkExteriorModel ∞
      (isCoveringMap_coordinateUnlinkExteriorEighthPowerPullbackProj m)

/-- The exterior power-pullback projection is smooth for the pulled-back atlas. -/
theorem contMDiff_coordinateUnlinkExteriorEighthPowerPullbackProj
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    ContMDiff coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorEighthPowerPullbackProj m) := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  exact
    (isLocalDiffeomorph_coordinateUnlinkExteriorEighthPowerPullbackProj m).contMDiff

/-- The exterior power-pullback projection is a smooth covering map. -/
theorem smoothCover_coordinateUnlinkExteriorEighthPowerPullbackProj
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    SmoothCover coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorEighthPowerPullbackProj m) := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  exact SplittingSpheres.IsCoveringMap.smoothCover_pullbackChartedSpace
    coordinateUnlinkExteriorModel ∞
      (isCoveringMap_coordinateUnlinkExteriorEighthPowerPullbackProj m)

/-- The model boundary upstairs is exactly the projection preimage of the two radial faces. -/
theorem coordinateUnlinkExteriorEighthPowerPullback_boundary
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      isManifold_coordinateUnlinkExteriorEighthPowerPullback m
    coordinateUnlinkExteriorModel.boundary
        (CoordinateUnlinkExteriorEighthPowerPullback m) =
      coordinateUnlinkExteriorEighthPowerPullbackProj m ⁻¹'
        coordinateUnlinkExteriorEighthRadialBoundary := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  rw [← coordinateUnlinkExteriorEighth_boundary]
  exact
    ((isLocalDiffeomorph_coordinateUnlinkExteriorEighthPowerPullbackProj m)
      |>.preimage_boundary (by simp)).symm

end SplittingSpheres
