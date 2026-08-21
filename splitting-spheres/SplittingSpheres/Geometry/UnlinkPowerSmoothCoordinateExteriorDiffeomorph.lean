/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkPowerSmoothExteriorDiffeomorph
public import SplittingSpheres.Geometry.CoordinateUnlinkExteriorPowerInteriorDiffeomorph

/-!
# Smooth transport to the strict coordinate exterior

The smooth transport from the unlink power pullback to the strict tube exterior composes with
the intrinsic coordinate-exterior identification.  The result is a diffeomorphism onto the
exact strict open subset of the compact coordinate-exterior power pullback.
-/

@[expose] public section

noncomputable section

open Function Set
open scoped ContDiff Manifold

namespace SplittingSpheres

/-- The unlink power pullback is diffeomorphic to the strict coordinate-exterior pullback. -/
def standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    StandardUnlinkPowerPullback m
      ≃ₘ^∞⟮modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)),
          coordinateUnlinkExteriorModel⟯
        CoordinateUnlinkExteriorEighthPowerPullbackStrict m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
    standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
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
  exact (standardUnlinkPowerPullbackSmoothExteriorDiffeomorph m).trans
    (standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictDiffeomorph m)

/-- Forgetting smoothness gives the composite of the two underlying homeomorphisms. -/
@[simp]
theorem standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_toHomeomorph
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m).toHomeomorph =
      (standardUnlinkPowerPullbackSmoothExteriorHomeomorph m).trans
        (standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph m) :=
  rfl

/-- The forward map is the composite of the two underlying homeomorphisms. -/
@[simp]
theorem standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_apply
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m z =
      standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph m
        (standardUnlinkPowerPullbackSmoothExteriorHomeomorph m z) :=
  rfl

/-- The inverse map is the reverse composite of the underlying homeomorphisms. -/
@[simp]
theorem standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_symm_apply
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorEighthPowerPullbackStrict m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m).symm z =
      (standardUnlinkPowerPullbackSmoothExteriorHomeomorph m).symm
        ((standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph m).symm z) :=
  rfl

/-- The coordinate-exterior base is the included smooth tube-exterior base. -/
@[simp]
theorem standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_apply_base
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m z).1.1.1 =
      standardUnlinkClosedTubeExteriorToCoordinateExterior
        (standardUnlinkComplementSmoothExteriorDiffeomorph z.1.1) :=
  rfl

/-- The full compact-cover projection records the included smooth tube-exterior base. -/
@[simp]
theorem
    coordinateUnlinkExteriorEighthPowerPullbackProj_coordinateExteriorStrictDiffeomorph
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorEighthPowerPullbackProj m
        (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m z).1 =
      standardUnlinkClosedTubeExteriorToCoordinateExterior
        (standardUnlinkComplementSmoothExteriorDiffeomorph
          (standardUnlinkPowerPullbackProj m z)) :=
  rfl

/-- The strict projection covers the composite intrinsic base diffeomorphism. -/
@[simp]
theorem
    coordinateUnlinkExteriorEighthPowerPullbackStrictProj_coordinateExteriorStrictDiffeomorph
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorEighthPowerPullbackStrictProj m
        (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m z) =
      coordinateUnlinkExteriorEighthInteriorSphereDiffeomorph.symm
        (standardUnlinkComplementSmoothExteriorDiffeomorph
          (standardUnlinkPowerPullbackProj m z)) := by
  apply Subtype.ext
  rfl

/-- The coordinate-exterior power coordinate is the gauge-corrected source coordinate. -/
@[simp]
theorem
    standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_apply_powerCoordinate
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m z).1.1.2.1 =
      standardUnlinkComplementSmoothExteriorPowerGauge m z.1.1 * z.1.2.1 :=
  rfl

/-- The smooth coordinate transport sends each labelled equatorial lift to its strict lift. -/
theorem
    standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_equatorUnlinkPowerLift
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m
        (equatorUnlinkPowerLift m a x) =
      standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph m
        (equatorUnlinkClosedTubeExteriorPowerLift m a x) := by
  rw [standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_apply]
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · exact standardUnlinkComplementSmoothExteriorDiffeomorph_equator x
  · apply Subtype.ext
    change standardUnlinkComplementSmoothExteriorPowerGauge m
        (equatorUnlinkComplementMap x) * equatorUnlinkPowerRootTranslate m a x =
      equatorUnlinkPowerRootTranslate m a x
    rw [standardUnlinkComplementSmoothExteriorPowerGauge_equator, one_mul]

/-- Coercing the equatorial identity gives its literal compact-pullback point. -/
theorem
    standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_equatorUnlinkPowerLift_coe
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m
        (equatorUnlinkPowerLift m a x)).1 =
      standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior m
        (equatorUnlinkClosedTubeExteriorPowerLift m a x) := by
  exact congrArg Subtype.val
    (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_equatorUnlinkPowerLift
      m a x)

/-- The image of each labelled equatorial lift is exactly its strict-coordinate range. -/
theorem
    standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_equatorUnlinkPowerLift_range
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m ''
        range (equatorUnlinkPowerLift m a) =
      range (fun x ↦
        standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph m
          (equatorUnlinkClosedTubeExteriorPowerLift m a x)) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x,
      (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_equatorUnlinkPowerLift
        m a x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨equatorUnlinkPowerLift m a x, ⟨x, rfl⟩,
      standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_equatorUnlinkPowerLift
        m a x⟩

end SplittingSpheres
