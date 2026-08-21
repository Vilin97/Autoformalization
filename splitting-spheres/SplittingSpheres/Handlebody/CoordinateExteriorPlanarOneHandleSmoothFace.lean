/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.CoordinateUnlinkExteriorPowerInteriorDiffeomorph
public import SplittingSpheres.Handlebody.AlignedSphereHandleSmoothness
public import SplittingSpheres.Handlebody.CoordinateExteriorOneHandlePowerPullbackDiffeomorph
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckStrictCorePieces

/-!
# The smooth one-handle face of the planar exterior model

The one-handle coprojection of the planar-flower partial spin has a literal image in the compact
coordinate-exterior power pullback.  This file lifts that image to the strict interior and proves
that both maps are smooth for the existing direct atlases.  Smoothness is detected through the
compact power-pullback projection: its base map is the smooth aligned one-handle sphere map after
the explicit circle power map.  Thus no selected residual-root branch is differentiated and no
atlas is transported through the planar-neck homeomorphism.

After the smooth one-handle pullback trivialization, this literal face is exactly the canonical
restricted-pullback inclusion into the compact pullback.  This file deliberately does not extend
the face across the planar annular shell, construct a rounded embedded four-ball or its signed
collar, or identify the complement of such a ball.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace SplittingSpheres

variable (m : ℕ) [NeZero m]

/-- The literal transported one-handle face in compact power-cover coordinates. -/
def coordinateUnlinkExteriorPlanarTransportedOneHandleMap
    (x : OneHandlePiece) : CoordinateUnlinkExteriorEighthPowerPullback m :=
  coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
    (partialSphereSpinInl
      (coordinateUnlinkExteriorPlanarFlowerOuter m) x)

private theorem continuous_coordinateUnlinkExteriorPlanarTransportedOneHandleMap :
    Continuous (coordinateUnlinkExteriorPlanarTransportedOneHandleMap m) := by
  exact (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).continuous.comp
    (partialSphereSpinInl
      (coordinateUnlinkExteriorPlanarFlowerOuter m)).continuous

/-- The transported one-handle face, lifted to the strict compact-cover interior. -/
def coordinateUnlinkExteriorPlanarTransportedOneHandleStrictMap
    (x : OneHandlePiece) :
    CoordinateUnlinkExteriorEighthPowerPullbackStrict m :=
  ⟨coordinateUnlinkExteriorPlanarTransportedOneHandleMap m x,
    coordinateUnlinkExteriorPlanarNeckTransport_oneHandle_mem_strict m x⟩

private theorem continuous_coordinateUnlinkExteriorPlanarTransportedOneHandleStrictMap :
    Continuous (coordinateUnlinkExteriorPlanarTransportedOneHandleStrictMap m) := by
  exact (continuous_coordinateUnlinkExteriorPlanarTransportedOneHandleMap m).subtype_mk _

private def coordinateUnlinkExteriorPlanarTransportedOneHandleBaseInteriorMap
    (x : OneHandlePiece) : CoordinateUnlinkExteriorEighthInterior :=
  coordinateUnlinkExteriorEighthPowerPullbackStrictProj m
    (coordinateUnlinkExteriorPlanarTransportedOneHandleStrictMap m x)

private theorem continuous_coordinateUnlinkExteriorPlanarTransportedOneHandleBaseInteriorMap :
    Continuous
      (coordinateUnlinkExteriorPlanarTransportedOneHandleBaseInteriorMap m) := by
  have hproj : Continuous
      (coordinateUnlinkExteriorEighthPowerPullbackProj m) :=
    continuous_fst.comp continuous_subtype_val
  exact (hproj.comp
      (continuous_coordinateUnlinkExteriorPlanarTransportedOneHandleMap m)).subtype_mk _

private theorem coordinateUnlinkExteriorPlanarTransportedOneHandleBaseInteriorMap_sphere
    (x : OneHandlePiece) :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    (coordinateUnlinkExteriorEighthInteriorSphereDiffeomorph
      (coordinateUnlinkExteriorPlanarTransportedOneHandleBaseInteriorMap m x) : Sphere 4) =
      unlinkAlignedOneHandleSphereMap
        (coordinateUnlinkExteriorOneHandleBasePowerMap m x) := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  rw [coordinateUnlinkExteriorEighthInteriorSphereDiffeomorph_apply_coe]
  exact congrArg Subtype.val
    (coordinateUnlinkExteriorPlanarNeckTransport_oneHandle_proj_closed m x)

private theorem contMDiff_coordinateUnlinkExteriorPlanarTransportedOneHandleBaseInteriorMap :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    ContMDiff oneHandlePieceModel coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarTransportedOneHandleBaseInteriorMap m) := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  apply contMDiff_of_comp_isLocalDiffeomorph
    oneHandlePieceModel coordinateUnlinkExteriorModel (𝓡 4)
    coordinateUnlinkExteriorEighthInteriorSphereDiffeomorph.isLocalDiffeomorph
    (continuous_coordinateUnlinkExteriorPlanarTransportedOneHandleBaseInteriorMap m)
  rw [← ContMDiff.subtypeVal_comp_iff standardUnlinkClosedTubeExteriorOpens]
  have h := contMDiff_unlinkAlignedOneHandleSphereMap.comp
    (isLocalDiffeomorph_coordinateUnlinkExteriorOneHandleBasePowerMap m).contMDiff
  exact h.congr fun x ↦ by
    simpa only [Function.comp_apply] using
      coordinateUnlinkExteriorPlanarTransportedOneHandleBaseInteriorMap_sphere m x

/-- The strict lift of the literal one-handle face is smooth for the direct compact-cover
atlas. -/
theorem contMDiff_coordinateUnlinkExteriorPlanarTransportedOneHandleStrictMap :
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
    ContMDiff oneHandlePieceModel coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarTransportedOneHandleStrictMap m) := by
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
  apply contMDiff_of_comp_isLocalDiffeomorph
    oneHandlePieceModel coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    (isLocalDiffeomorph_coordinateUnlinkExteriorEighthPowerPullbackStrictProj m)
    (continuous_coordinateUnlinkExteriorPlanarTransportedOneHandleStrictMap m)
  convert
    (contMDiff_coordinateUnlinkExteriorPlanarTransportedOneHandleBaseInteriorMap m) using 1
  funext x
  rfl

/-- The literal one-handle face is smooth as a map into the compact power pullback. -/
theorem contMDiff_coordinateUnlinkExteriorPlanarTransportedOneHandleMap :
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
    ContMDiff oneHandlePieceModel coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarTransportedOneHandleMap m) := by
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
  exact (contMDiff_subtype_val.comp
    (contMDiff_coordinateUnlinkExteriorPlanarTransportedOneHandleStrictMap m)).congr
      fun _ ↦ rfl

private theorem coordinateUnlinkExteriorPlanarTransportedOneHandleMap_eq_canonical
    (x : OneHandlePiece) :
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarTransportedOneHandleMap m x =
      coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m
        (coordinateUnlinkExteriorOneHandlePowerPullbackToPushout m
          (coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph m x)) := by
  let _ : ChartedSpace OneHandleModelSpace
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
  rw [coordinateUnlinkExteriorPlanarTransportedOneHandleMap,
    coordinateUnlinkExteriorPlanarNeckTransportHomeomorph,
    Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph_symm_oneHandle,
    coordinateUnlinkExteriorPartialSphereSpinHomeomorph,
    Homeomorph.trans_apply,
    coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph_inl,
    coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph_apply]

/-- In smooth restricted-pullback coordinates, the literal transported face is exactly the
canonical inclusion into the compact power pullback. -/
theorem coordinateUnlinkExteriorPlanarTransportedOneHandleMap_symm_eq_canonical
    (z : CoordinateUnlinkExteriorOneHandlePowerPullback m) :
    letI : ChartedSpace OneHandleModelSpace
        (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
      coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarTransportedOneHandleMap m
        ((coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph m).symm z) =
      coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m
        (coordinateUnlinkExteriorOneHandlePowerPullbackToPushout m z) := by
  let _ : ChartedSpace OneHandleModelSpace
      (CoordinateUnlinkExteriorOneHandlePowerPullback m) :=
    coordinateUnlinkExteriorOneHandlePowerPullbackChartedSpace m
  rw [coordinateUnlinkExteriorPlanarTransportedOneHandleMap_eq_canonical,
    (coordinateUnlinkExteriorOneHandlePowerPullbackDiffeomorph m).apply_symm_apply]

end SplittingSpheres
