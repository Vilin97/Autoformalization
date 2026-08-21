/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import SplittingSpheres.Foundations.SmoothCoverPullbackAtlas
public import SplittingSpheres.Handlebody.CoordinateExteriorPowerPieceCover

/-!
# The smooth power cover over the coordinate-exterior one-handle

The restricted power pullback over the literal `S¹ × B³` one-handle is a topological covering
of an already constructed manifold with corners.  Pulling back the one-handle atlas along its
covering projection makes the total space an honest smooth four-manifold with corners.  In this
atlas the projection is a local diffeomorphism and a smooth covering map, and its model boundary
is exactly the inverse image of the one-handle model boundary.

This file concerns only the restricted one-handle pullback.  It makes no smoothness assertion
about the punctured-cap pullback, the planar flower, any topological pushout, or the global closed
coordinate exterior.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Manifold

namespace SplittingSpheres

/-- The atlas on the restricted one-handle power pullback obtained from the actual covering
projection to `S¹ × B³`. -/
abbrev coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace
    (m : ℕ) [NeZero m] :
    ChartedSpace OneHandleModelSpace
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
  SplittingSpheres.IsCoveringMap.pullbackChartedSpace
    (isCoveringMap_coordinateUnlinkExteriorOneHandlePowerPullbackProj m)

/-- The pulled-back atlas makes the restricted total space a smooth four-manifold with corners. -/
theorem isManifold_coordinateUnlinkExteriorOneHandlePowerPullback
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    IsManifold oneHandlePieceModel ∞
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) := by
  let _ : ChartedSpace OneHandleModelSpace
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
  exact SplittingSpheres.IsCoveringMap.isManifold_pullbackChartedSpace
    oneHandlePieceModel ∞
      (isCoveringMap_coordinateUnlinkExteriorOneHandlePowerPullbackProj m)

/-- The covering projection is a local diffeomorphism for the pulled-back atlas. -/
theorem isLocalDiffeomorph_coordinateUnlinkExteriorOneHandlePowerPullbackProj
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    letI : IsManifold oneHandlePieceModel ∞
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
    IsLocalDiffeomorph oneHandlePieceModel oneHandlePieceModel ∞
      (coordinateUnlinkExteriorOneHandlePowerPullbackProj m) := by
  let _ : ChartedSpace OneHandleModelSpace
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
  let _ : IsManifold oneHandlePieceModel ∞
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
  exact SplittingSpheres.IsCoveringMap.isLocalDiffeomorph_pullbackChartedSpace
    oneHandlePieceModel ∞
      (isCoveringMap_coordinateUnlinkExteriorOneHandlePowerPullbackProj m)

/-- The covering projection is smooth for the pulled-back atlas. -/
theorem contMDiff_coordinateUnlinkExteriorOneHandlePowerPullbackProj
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    letI : IsManifold oneHandlePieceModel ∞
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
    ContMDiff oneHandlePieceModel oneHandlePieceModel ∞
      (coordinateUnlinkExteriorOneHandlePowerPullbackProj m) := by
  let _ : ChartedSpace OneHandleModelSpace
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
  let _ : IsManifold oneHandlePieceModel ∞
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
  exact
    (isLocalDiffeomorph_coordinateUnlinkExteriorOneHandlePowerPullbackProj m).contMDiff

/-- The restricted projection is a smooth covering map. -/
theorem smoothCover_coordinateUnlinkExteriorOneHandlePowerPullbackProj
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    letI : IsManifold oneHandlePieceModel ∞
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
    SmoothCover oneHandlePieceModel oneHandlePieceModel ∞
      (coordinateUnlinkExteriorOneHandlePowerPullbackProj m) := by
  let _ : ChartedSpace OneHandleModelSpace
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
  let _ : IsManifold oneHandlePieceModel ∞
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
  exact SplittingSpheres.IsCoveringMap.smoothCover_pullbackChartedSpace
    oneHandlePieceModel ∞
      (isCoveringMap_coordinateUnlinkExteriorOneHandlePowerPullbackProj m)

/-- The model boundary upstairs is exactly the inverse image of the one-handle model boundary. -/
theorem coordinateUnlinkExteriorOneHandlePowerPullbackModel_boundary
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    letI : IsManifold oneHandlePieceModel ∞
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
    oneHandlePieceModel.boundary
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) =
      coordinateUnlinkExteriorOneHandlePowerPullbackProj m ⁻¹'
        oneHandlePieceModel.boundary OneHandlePiece := by
  let _ : ChartedSpace OneHandleModelSpace
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
  let _ : IsManifold oneHandlePieceModel ∞
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    isManifold_coordinateUnlinkExteriorOneHandlePowerPullback m
  exact
    ((isLocalDiffeomorph_coordinateUnlinkExteriorOneHandlePowerPullbackProj m)
      |>.preimage_boundary (by simp)).symm

end SplittingSpheres
