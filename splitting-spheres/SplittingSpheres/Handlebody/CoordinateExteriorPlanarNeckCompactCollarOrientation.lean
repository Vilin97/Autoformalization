/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCoordinateCaps

/-!
# Canonical orientation of the smooth compact planar-neck collar

The smooth compact collar was previously normalized by a noncomputable per-label reflection.
An explicit negative-time point at time `-1/8` lies outside both closed quarter tubes, where the
old point-set and new smooth exterior transports fix both the base and power coordinate.  The
coordinate-cap orientation theorem therefore puts that point on the compact global left side.
Together with the existing opposite-half alternative, this forces every raw collar to have the
chosen negative-left and positive-right orientation.

Consequently the orientation flag is false, the selected source homeomorphism is the identity,
and the oriented collar is literally the raw smooth collar.  The resulting open-side, seam, and
closed-cut membership laws are exact pointwise sign characterizations.

This file does not identify the entire compact cut carriers with inverse images of closed
coordinate hemispheres.  Such a comparison must additionally control the old radial transport
throughout the strict interior and extend the result to the ambient radial boundary.  It also
makes no smoothness assertion about the old normalized planar annuli.
-/

@[expose] public section

open Function Metric Set Topology TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

private def rawOrientationWitnessTime : EquatorCollarInterval :=
  ⟨-(1 / 8 : ℝ), by constructor <;> norm_num⟩

private theorem rawOrientationWitness_not_mem_closedTubes_quarter
    (x : Sphere 3) :
    equatorCollarSphereMap (x, rawOrientationWitnessTime) ∉
      standardUnlinkClosedTubes (1 / 4 : ℝ) := by
  intro h
  rcases h with h | h
  · have hle :
        ‖standardUnlinkNormalProjection
              (equatorCollarSphereMap (x, rawOrientationWitnessTime)) -
            standardUnlinkNormalCenter 0‖ ≤ 1 / 4 := by
      simpa only [standardUnlinkClosedTube, mem_preimage, mem_closedBall,
        dist_eq_norm] using h
    have hsq := EuclideanSpace.real_norm_sq_eq
      (standardUnlinkNormalProjection
          (equatorCollarSphereMap (x, rawOrientationWitnessTime)) -
        standardUnlinkNormalCenter 0)
    have hsqle :
        ‖standardUnlinkNormalProjection
              (equatorCollarSphereMap (x, rawOrientationWitnessTime)) -
            standardUnlinkNormalCenter 0‖ ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by norm_num)).2 hle
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsq
    simp [standardUnlinkNormalProjection, standardUnlinkNormalCenter,
      standardUnlinkHeight, rawOrientationWitnessTime,
      equatorCollarSphereMap, equatorCollarAmbientMap] at hsq hsqle
    norm_num at hsq hsqle
    nlinarith [sq_nonneg
      (equatorCollarScale (-(1 / 8 : ℝ)) * x.1 3),
      norm_nonneg
        (standardUnlinkNormalProjection
          (equatorCollarSphereMap (x, rawOrientationWitnessTime)) -
        standardUnlinkNormalCenter 0)]
  · have hle :
        ‖standardUnlinkNormalProjection
              (equatorCollarSphereMap (x, rawOrientationWitnessTime)) -
            standardUnlinkNormalCenter 1‖ ≤ 1 / 4 := by
      simpa only [standardUnlinkClosedTube, mem_preimage, mem_closedBall,
        dist_eq_norm] using h
    have hsq := EuclideanSpace.real_norm_sq_eq
      (standardUnlinkNormalProjection
          (equatorCollarSphereMap (x, rawOrientationWitnessTime)) -
        standardUnlinkNormalCenter 1)
    have hsqle :
        ‖standardUnlinkNormalProjection
              (equatorCollarSphereMap (x, rawOrientationWitnessTime)) -
            standardUnlinkNormalCenter 1‖ ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by norm_num)).2 hle
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsq
    simp [standardUnlinkNormalProjection, standardUnlinkNormalCenter,
      standardUnlinkHeight, rawOrientationWitnessTime,
      equatorCollarSphereMap, equatorCollarAmbientMap] at hsq hsqle
    norm_num at hsq hsqle
    nlinarith [sq_nonneg
      (equatorCollarScale (-(1 / 8 : ℝ)) * x.1 3),
      norm_nonneg
        (standardUnlinkNormalProjection
          (equatorCollarSphereMap (x, rawOrientationWitnessTime)) -
        standardUnlinkNormalCenter 1)]

private theorem rawOrientationWitness_powerExterior_eq
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    standardUnlinkPowerPullbackExteriorHomeomorph m
        (equatorUnlinkPowerCollarLift m a
          (x, rawOrientationWitnessTime)) =
      standardUnlinkPowerPullbackSmoothExteriorHomeomorph m
        (equatorUnlinkPowerCollarLift m a
          (x, rawOrientationWitnessTime)) := by
  let z := equatorUnlinkPowerCollarLift m a
    (x, rawOrientationWitnessTime)
  have hnot : (standardUnlinkPowerPullbackProj m z).1 ∉
      standardUnlinkClosedTubes (1 / 4 : ℝ) := by
    change equatorCollarSphereMap (x, rawOrientationWitnessTime) ∉
      standardUnlinkClosedTubes (1 / 4 : ℝ)
    exact rawOrientationWitness_not_mem_closedTubes_quarter x
  have hold :
      (standardUnlinkComplementExteriorHomeomorph
          (standardUnlinkPowerPullbackProj m z) : Sphere 4) =
        (standardUnlinkPowerPullbackProj m z).1 :=
    standardUnlinkComplementExteriorHomeomorph_eq_self_of_not_mem_closedTubes_quarter
      _ hnot
  have hsmooth :
      (standardUnlinkComplementSmoothExteriorDiffeomorph
          (standardUnlinkPowerPullbackProj m z) : Sphere 4) =
        (standardUnlinkPowerPullbackProj m z).1 :=
    standardUnlinkComplementSmoothExteriorDiffeomorph_eq_self_of_not_mem_closedTubes_quarter
      _ hnot
  have hgold :
      standardUnlinkComplementExteriorPowerGauge m
          (standardUnlinkPowerPullbackProj m z) = 1 :=
    standardUnlinkComplementExteriorPowerGauge_eq_one_of_fixed m _ hold
  have hgsmooth :
      standardUnlinkComplementSmoothExteriorPowerGauge m
          (standardUnlinkPowerPullbackProj m z) = 1 :=
    standardUnlinkComplementSmoothExteriorPowerGauge_eq_one_of_fixed m _ hsmooth
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact hold.trans hsmooth.symm
  · apply Subtype.ext
    change
      standardUnlinkComplementExteriorPowerGauge m z.1.1 * z.1.2.1 =
        standardUnlinkComplementSmoothExteriorPowerGauge m z.1.1 * z.1.2.1
    change standardUnlinkComplementExteriorPowerGauge m z.1.1 = 1 at hgold
    change standardUnlinkComplementSmoothExteriorPowerGauge m z.1.1 = 1 at hgsmooth
    rw [hgold, hgsmooth]

private theorem rawOrientationWitness_strictTransport_eq
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m
        (equatorUnlinkPowerCollarLift m a
          (x, rawOrientationWitnessTime)) =
      standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m
        (equatorUnlinkPowerCollarLift m a
          (x, rawOrientationWitnessTime)) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  rw [coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph,
    Homeomorph.trans_apply,
    standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_apply]
  congr 1
  exact rawOrientationWitness_powerExterior_eq m a x

private theorem compactNeckStarHomeomorph_rawOrientationWitness
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
        (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a
          (x, rawOrientationWitnessTime)) =
      coordinateUnlinkExteriorPlanarFullCoverToNeckStar m
        (equatorUnlinkPowerCollarLift m
          (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m)
          (x, rawOrientationWitnessTime)) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  change
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
        ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm
          (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m
            (equatorUnlinkPowerCollarLift m
              (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m)
              (x, rawOrientationWitnessTime))).1) =
      coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
        ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm
          (coordinateUnlinkExteriorPlanarFullCoverStrictHomeomorph m
            (equatorUnlinkPowerCollarLift m
              (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m)
              (x, rawOrientationWitnessTime))).1)
  rw [rawOrientationWitness_strictTransport_eq]

private theorem rawOrientationWitness_mem_compactLeft
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a
        (x, rawOrientationWitnessTime) ∈
      coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let z := equatorUnlinkPowerCollarLift m
    (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m)
    (x, rawOrientationWitnessTime)
  have hzLeft : z ∈
      coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam m := by
    rw [
      coordinateUnlinkExteriorPlanarFullCoverGlobalLeftOffSeam_eq_preimage_coordinateOpenCap_zero,
      mem_preimage, mem_coordinateOpenCap_zero]
    change rawOrientationWitnessTime.1 < 0
    norm_num [rawOrientationWitnessTime]
  change coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
      (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a
        (x, rawOrientationWitnessTime)) ∈
    coordinateUnlinkExteriorPlanarNeckStarLeftOffSeam m
  rw [compactNeckStarHomeomorph_rawOrientationWitness]
  exact hzLeft

/-- The raw compact collar already sends negative time to the global left side and positive time
to the global right side. -/
theorem coordinateUnlinkExteriorPlanarCompactCollarRawForward_holds
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarCompactCollarRawForward m a := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  rcases coordinateUnlinkExteriorPlanarCompactCollarHalfImages_opposite_side_choice m a with
    hforward | hreverse
  · exact hforward
  · exfalso
    let x : Sphere 3 := ⟨Classical.choose
        (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 4))
          (x := 0) (r := 1) |>.2 (by norm_num)),
      Classical.choose_spec
        (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 4))
          (x := 0) (r := 1) |>.2 (by norm_num))⟩
    let p : Sphere 3 × EquatorCollarInterval :=
      (x, rawOrientationWitnessTime)
    have hpNeg : p ∈
        coordinateUnlinkExteriorPlanarCompactCollarNegativeHalf := by
      change rawOrientationWitnessTime.1 < 0
      norm_num [rawOrientationWitnessTime]
    have hzNeg :
        coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
          coordinateUnlinkExteriorPlanarCompactCollarNegativeHalfImage m a :=
      ⟨p, hpNeg, rfl⟩
    have hzRight := hreverse.1 hzNeg
    have hzLeft :
        coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
          coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m := by
      exact rawOrientationWitness_mem_compactLeft m a x
    exact Set.disjoint_left.mp
      (disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarOffSeam m)
      hzLeft hzRight

/-- The noncomputable compact-collar orientation flag is always false. -/
theorem coordinateUnlinkExteriorPlanarCompactCollarOrientationReversed_eq_false
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarCompactCollarOrientationReversed m a = false := by
  apply
    (coordinateUnlinkExteriorPlanarCompactCollarOrientationReversed_eq_false_iff
      m a).2
  exact coordinateUnlinkExteriorPlanarCompactCollarRawForward_holds m a

/-- The source normalization selected for the compact collar is the identity homeomorphism. -/
theorem coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph_eq_refl
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph m a =
      Homeomorph.refl (Sphere 3 × EquatorCollarInterval) := by
  apply Homeomorph.ext
  intro p
  exact
    coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph_apply_of_forward
      m a (coordinateUnlinkExteriorPlanarCompactCollarRawForward_holds m a) p

/-- The oriented compact collar map is exactly the original transported smooth collar map. -/
theorem coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_eq_raw
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m a =
      coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  funext p
  rw [coordinateUnlinkExteriorPlanarOrientedCompactCollarMap,
    Function.comp_apply,
    coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph_apply_of_forward
      m a (coordinateUnlinkExteriorPlanarCompactCollarRawForward_holds m a)]

/-- A raw compact-collar point lies in the global left open side exactly at negative time. -/
theorem coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap_mem_left_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarLeftOffSeam m ↔
      p.2.1 < 0 := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  rw [← coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_eq_raw m a]
  exact coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_left_iff m a p

/-- A raw compact-collar point lies in the global right open side exactly at positive time. -/
theorem coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap_mem_right_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarRightOffSeam m ↔
      0 < p.2.1 := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  rw [← coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_eq_raw m a]
  exact coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_right_iff m a p

/-- A raw compact-collar point lies on the full labelled seam exactly at time zero. -/
theorem coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap_mem_seam_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarSeam m ↔
      p.2.1 = 0 := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  exact
    coordinateUnlinkExteriorPlanarCompactCollar_mem_compactNeckStarSeam_iff m a p

/-- A raw compact-collar point lies in the closed left cut carrier exactly at nonpositive time. -/
theorem coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap_mem_leftCut_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m ↔
      p.2.1 ≤ 0 := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  rw [← coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_eq_raw m a]
  exact
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_leftCut_iff m a p

/-- A raw compact-collar point lies in the closed right cut carrier exactly at nonnegative time. -/
theorem coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap_mem_rightCut_iff
    (m : ℕ) [NeZero m] (a : ZMod m)
    (p : Sphere 3 × EquatorCollarInterval) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap m a p ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m ↔
      0 ≤ p.2.1 := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  rw [← coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_eq_raw m a]
  exact
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_mem_rightCut_iff m a p

end SplittingSpheres

end
