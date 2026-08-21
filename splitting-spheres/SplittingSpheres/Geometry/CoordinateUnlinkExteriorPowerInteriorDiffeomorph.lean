/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.DiffeomorphOverLocalDiffeomorph
public import SplittingSpheres.Geometry.CoordinateUnlinkExteriorInteriorDiffeomorph
public import SplittingSpheres.Geometry.CoordinateUnlinkExteriorPowerSmoothCover
public import SplittingSpheres.Geometry.UnlinkClosedTubeExteriorPowerSmoothCover

/-!
# The strict interior of the smooth coordinate-exterior power cover

The literal power pullback over the complement of the two closed radius-`1 / 8` tubes is
point-set homeomorphic to the inverse-image open subset of the compact coordinate-exterior
power pullback.  This file proves that the same homeomorphism is a diffeomorphism for the actual
pulled-back atlases.

The proof restricts the compact-cover projection to the corresponding open subsets.  That
restriction is a local diffeomorphism, and the total-space homeomorphism covers the intrinsic
identity diffeomorphism between the two base presentations.  Smoothness in both directions is
therefore detected through the two projections.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Manifold

namespace SplittingSpheres

/-- Project the strict open part of the compact power cover to the strict interior of its base. -/
def coordinateUnlinkExteriorEighthPowerPullbackStrictProj
    (m : ℕ) (z : CoordinateUnlinkExteriorEighthPowerPullbackStrict m) :
    CoordinateUnlinkExteriorEighthInterior :=
  restrictToOpens (coordinateUnlinkExteriorEighthPowerPullbackProj m)
    (coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m)
    coordinateUnlinkExteriorEighthInteriorOpens (fun z ↦ z.2) z

@[simp]
theorem coordinateUnlinkExteriorEighthPowerPullbackStrictProj_coe
    (m : ℕ) (z : CoordinateUnlinkExteriorEighthPowerPullbackStrict m) :
    (coordinateUnlinkExteriorEighthPowerPullbackStrictProj m z :
        CoordinateUnlinkExteriorEighth) =
      coordinateUnlinkExteriorEighthPowerPullbackProj m z.1 :=
  rfl

/-- The restricted compact-cover projection remains a local diffeomorphism. -/
theorem isLocalDiffeomorph_coordinateUnlinkExteriorEighthPowerPullbackStrictProj
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
      (coordinateUnlinkExteriorEighthPowerPullbackStrictProj m) := by
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
  change IsLocalDiffeomorph coordinateUnlinkExteriorModel
    coordinateUnlinkExteriorModel ∞
      (restrictToOpens (coordinateUnlinkExteriorEighthPowerPullbackProj m)
        (coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m)
        coordinateUnlinkExteriorEighthInteriorOpens (fun z ↦ z.2))
  exact isLocalDiffeomorph_restrictToOpens coordinateUnlinkExteriorModel
    coordinateUnlinkExteriorModel
    (coordinateUnlinkExteriorEighthPowerPullbackProj m)
    (coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m)
    coordinateUnlinkExteriorEighthInteriorOpens
    (fun z ↦ z.2)
    (isLocalDiffeomorph_coordinateUnlinkExteriorEighthPowerPullbackProj m)

/-- The literal strict-exterior power pullback is diffeomorphic to the exact strict open subset
of the compact coordinate-exterior power cover. -/
def standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictDiffeomorph
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
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
    StandardUnlinkClosedTubeExteriorPowerPullback m
      ≃ₘ^∞⟮𝓡 4, coordinateUnlinkExteriorModel⟯
        CoordinateUnlinkExteriorEighthPowerPullbackStrict m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
    standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞
      (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
    isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
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
  apply diffeomorphOfHomeomorphOverDiffeomorph
    (𝓡 4) coordinateUnlinkExteriorModel
    (standardUnlinkClosedTubeExteriorPowerPullbackProj m)
    (coordinateUnlinkExteriorEighthPowerPullbackStrictProj m)
    (isLocalDiffeomorph_standardUnlinkClosedTubeExteriorPowerPullbackProj m)
    (isLocalDiffeomorph_coordinateUnlinkExteriorEighthPowerPullbackStrictProj m)
    coordinateUnlinkExteriorEighthInteriorSphereDiffeomorph.symm
    (standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph m)
  intro z
  apply Subtype.ext
  rfl

@[simp]
theorem standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictDiffeomorph_apply
    (m : ℕ) [NeZero m]
    (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictDiffeomorph m z =
      standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph m z :=
  rfl

@[simp]
theorem standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictDiffeomorph_symm_apply
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorEighthPowerPullbackStrict m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
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
    (standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictDiffeomorph m).symm z =
      (standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph m).symm z :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorEighthPowerPullbackStrictProj_strictDiffeomorph
    (m : ℕ) [NeZero m]
    (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
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
    coordinateUnlinkExteriorEighthPowerPullbackStrictProj m
          (standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictDiffeomorph m z) =
        coordinateUnlinkExteriorEighthInteriorSphereDiffeomorph.symm
          (standardUnlinkClosedTubeExteriorPowerPullbackProj m z) := by
  apply Subtype.ext
  rfl

end SplittingSpheres
