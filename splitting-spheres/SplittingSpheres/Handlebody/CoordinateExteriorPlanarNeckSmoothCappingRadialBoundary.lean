/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckSmoothCappingBoundary

/-!
# Radial boundaries of the direct smooth planar-neck cappings

The boundary formulas for the direct cappings initially retain the boundaries of both pieces
away from their attaching ranges.  This file identifies those ranges exactly.  On a compact
cut side, the attaching range is precisely the subtype preimage of the transported neck seam.
On the four-ball side, the attaching range is the entire model boundary.  The transported seam
lies in the model interior of the ambient compact coordinate exterior, so removing it from a
cut boundary leaves exactly the old ambient radial boundary.

Consequently the boundary of either capped pushout is the image of the corresponding ambient
radial boundary in the compact cut side.  These are equalities for the explicit direct atlases;
no boundary preservation under a comparison homeomorphism is asserted or used.
-/

@[expose] public section

noncomputable section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace SplittingSpheres

variable (m : ℕ) [NeZero m]

private theorem leftCutAttachingMap_coe_radialBoundary
    (p : ZMod m × Sphere 3) :
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m p).1 =
      coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m p.1 p.2 := by
  classical
  change coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1
      (compactNeckLeftHalfParameter (p.2, euclideanFourBallCollarZero)) = _
  unfold coordinateUnlinkExteriorPlanarOrientedCompactCollarMap
  rw [Function.comp_apply]
  by_cases h : coordinateUnlinkExteriorPlanarCompactCollarRawForward m p.1
  · rw [coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph_apply_of_forward
      m p.1 h]
    unfold compactNeckLeftHalfParameter
      coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero
    congr 3
    simp only [euclideanFourBallCollarZero_value, neg_zero]
  · rw [coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph_apply_of_not_forward
      m p.1 h]
    unfold compactNeckLeftHalfParameter
      coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero
      coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph
    congr 3
    apply Subtype.ext
    simp [euclideanFourBallCollarZero_value]

private theorem rightCutAttachingMap_coe_radialBoundary
    (p : ZMod m × Sphere 3) :
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m p).1 =
      coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m p.1 p.2 := by
  classical
  change coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1
      (compactNeckRightHalfParameter (p.2, euclideanFourBallCollarZero)) = _
  unfold coordinateUnlinkExteriorPlanarOrientedCompactCollarMap
  rw [Function.comp_apply]
  by_cases h : coordinateUnlinkExteriorPlanarCompactCollarRawForward m p.1
  · rw [coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph_apply_of_forward
      m p.1 h]
    unfold compactNeckRightHalfParameter
      coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero
    congr 3
  · rw [coordinateUnlinkExteriorPlanarCompactCollarOrientedSourceHomeomorph_apply_of_not_forward
      m p.1 h]
    unfold compactNeckRightHalfParameter
      coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero
      coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph
    congr 3
    apply Subtype.ext
    simp [euclideanFourBallCollarZero_value]

/-- The attaching range in the compact left cut is exactly the transported neck seam,
corestricted to that cut carrier. -/
theorem range_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap :
    range (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m) =
      (Subtype.val : CompactNeckLeftCut m →
        CoordinateUnlinkExteriorEighthPowerPullback m) ⁻¹'
          coordinateUnlinkExteriorPlanarCompactNeckStarSeam m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    change (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m p).1 ∈
      coordinateUnlinkExteriorPlanarCompactNeckStarSeam m
    rw [leftCutAttachingMap_coe_radialBoundary]
    exact
      range_coordinateUnlinkExteriorPlanarCompactCollarZero_subset_compactNeckStarSeam
        m p.1 ⟨p.2, rfl⟩
  · intro hz
    change z.1 ∈ coordinateUnlinkExteriorPlanarCompactNeckStarSeam m at hz
    rw [coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_range_transport_family] at hz
    obtain ⟨⟨a, s⟩, hs⟩ := hz
    have hzZero : z.1 ∈
        range (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a) := by
      rw [range_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero]
      exact ⟨s, by
        simpa only [coordinateUnlinkExteriorPlanarNeckSphereFamily_apply] using hs⟩
    obtain ⟨q, hq⟩ := hzZero
    refine ⟨(a, q), ?_⟩
    apply Subtype.ext
    rw [leftCutAttachingMap_coe_radialBoundary]
    exact hq

/-- The attaching range in the compact right cut is exactly the transported neck seam,
corestricted to that cut carrier. -/
theorem range_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap :
    range (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m) =
      (Subtype.val : CompactNeckRightCut m →
        CoordinateUnlinkExteriorEighthPowerPullback m) ⁻¹'
          coordinateUnlinkExteriorPlanarCompactNeckStarSeam m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    change (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m p).1 ∈
      coordinateUnlinkExteriorPlanarCompactNeckStarSeam m
    rw [rightCutAttachingMap_coe_radialBoundary]
    exact
      range_coordinateUnlinkExteriorPlanarCompactCollarZero_subset_compactNeckStarSeam
        m p.1 ⟨p.2, rfl⟩
  · intro hz
    change z.1 ∈ coordinateUnlinkExteriorPlanarCompactNeckStarSeam m at hz
    rw [coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_range_transport_family] at hz
    obtain ⟨⟨a, s⟩, hs⟩ := hz
    have hzZero : z.1 ∈
        range (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a) := by
      rw [range_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero]
      exact ⟨s, by
        simpa only [coordinateUnlinkExteriorPlanarNeckSphereFamily_apply] using hs⟩
    obtain ⟨q, hq⟩ := hzZero
    refine ⟨(a, q), ?_⟩
    apply Subtype.ext
    rw [rightCutAttachingMap_coe_radialBoundary]
    exact hq

omit [NeZero m] in
/-- The labelled Euclidean four-ball attaching map covers the entire direct model boundary. -/
theorem range_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    range (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) =
      coordinateUnlinkExteriorModel.boundary (ZMod m × EuclideanFourBall) := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  rw [coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily_boundary]
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    change coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar
        (p.2, euclideanFourBallCollarZero) ∈
      euclideanFourBallModel.boundary EuclideanFourBall
    rw [coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar_apply,
      ← range_euclideanFourBallSmoothCollar_zero]
    exact mem_range_self p.2
  · intro hz
    change z.2 ∈ euclideanFourBallModel.boundary EuclideanFourBall at hz
    rw [← range_euclideanFourBallSmoothCollar_zero] at hz
    obtain ⟨s, hs⟩ := hz
    refine ⟨(z.1, s), ?_⟩
    apply Prod.ext
    · rfl
    · change coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar
          (s, euclideanFourBallCollarZero) = z.2
      rw [coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar_apply]
      exact hs

private theorem transportedNeckCompactCollarZero_not_mem_ambientBoundary
    (a : ZMod m) (s : Sphere 3) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
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
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a s ∉
      coordinateUnlinkExteriorModel.boundary
        (CoordinateUnlinkExteriorEighthPowerPullback m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
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
  intro hpBoundary
  let p : Sphere 3 × EquatorCollarInterval :=
    (s, ⟨0, by norm_num [equatorCollarIntervalOpens]⟩)
  change coordinateUnlinkExteriorModel.IsBoundaryPoint
    (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a s) at hpBoundary
  have hsource :
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ)).IsBoundaryPoint p :=
    ((isLocalDiffeomorph_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap
      m a p).isBoundaryPoint_iff (by simp)).mpr (by
        simpa only [p, coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero]
          using hpBoundary)
  have hempty :
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ)).boundary
          (Sphere 3 × EquatorCollarInterval) = ∅ :=
    ModelWithCorners.Boundaryless.boundary_eq_empty
  change p ∈ ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
      (modelWithCornersSelf ℝ ℝ)).boundary
      (Sphere 3 × EquatorCollarInterval) at hsource
  rw [hempty] at hsource
  exact hsource

/-- The full transported compact neck seam is disjoint from the ambient radial boundary. -/
theorem disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarSeam_ambientBoundary :
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    Disjoint (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
      (coordinateUnlinkExteriorModel.boundary
        (CoordinateUnlinkExteriorEighthPowerPullback m)) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
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
  rw [Set.disjoint_left]
  intro z hzSeam hzBoundary
  rw [coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_range_transport_family] at hzSeam
  obtain ⟨⟨a, s⟩, hs⟩ := hzSeam
  have hzZero : z ∈
      range (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a) := by
    rw [range_coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero]
    exact ⟨s, by
      simpa only [coordinateUnlinkExteriorPlanarNeckSphereFamily_apply] using hs⟩
  obtain ⟨q, rfl⟩ := hzZero
  exact transportedNeckCompactCollarZero_not_mem_ambientBoundary m a q hzBoundary

/-- The full transported compact neck seam lies in the model interior of the ambient compact
coordinate exterior. -/
theorem coordinateUnlinkExteriorPlanarCompactNeckStarSeam_subset_ambientInterior :
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarCompactNeckStarSeam m ⊆
      coordinateUnlinkExteriorModel.interior
        (CoordinateUnlinkExteriorEighthPowerPullback m) := by
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  intro z hzSeam
  rw [← coordinateUnlinkExteriorModel.compl_boundary]
  exact Set.disjoint_left.mp
    (disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarSeam_ambientBoundary m) hzSeam

/-- Removing the capping seam from the left cut boundary leaves exactly the subtype preimage
of the old ambient radial boundary. -/
theorem boundary_compactNeckLeftCut_sdiff_smoothCappingAttachingRange :
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    coordinateUnlinkExteriorModel.boundary (CompactNeckLeftCut m) \
        range (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m) =
      (Subtype.val : CompactNeckLeftCut m →
        CoordinateUnlinkExteriorEighthPowerPullback m) ⁻¹'
          coordinateUnlinkExteriorModel.boundary
            (CoordinateUnlinkExteriorEighthPowerPullback m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
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
  let _ := compactNeckLeftCutChartedSpace m
  rw [boundary_compactNeckLeftCut,
    range_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap]
  ext z
  constructor
  · rintro ⟨hzBoundary | hzSeam, hzNotSeam⟩
    · exact hzBoundary
    · exact False.elim (hzNotSeam hzSeam)
  · intro hzBoundary
    refine ⟨Or.inl hzBoundary, ?_⟩
    intro hzSeam
    exact Set.disjoint_left.mp
      (disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarSeam_ambientBoundary m)
      hzSeam hzBoundary

/-- Removing the capping seam from the right cut boundary leaves exactly the subtype preimage
of the old ambient radial boundary. -/
theorem boundary_compactNeckRightCut_sdiff_smoothCappingAttachingRange :
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    coordinateUnlinkExteriorModel.boundary (CompactNeckRightCut m) \
        range (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m) =
      (Subtype.val : CompactNeckRightCut m →
        CoordinateUnlinkExteriorEighthPowerPullback m) ⁻¹'
          coordinateUnlinkExteriorModel.boundary
            (CoordinateUnlinkExteriorEighthPowerPullback m) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
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
  let _ := compactNeckRightCutChartedSpace m
  rw [boundary_compactNeckRightCut,
    range_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap]
  ext z
  constructor
  · rintro ⟨hzBoundary | hzSeam, hzNotSeam⟩
    · exact hzBoundary
    · exact False.elim (hzNotSeam hzSeam)
  · intro hzBoundary
    refine ⟨Or.inl hzBoundary, ?_⟩
    intro hzSeam
    exact Set.disjoint_left.mp
      (disjoint_coordinateUnlinkExteriorPlanarCompactNeckStarSeam_ambientBoundary m)
      hzSeam hzBoundary

/-- For the direct left capping atlas, the boundary is exactly the pushout image of the old
ambient radial boundary in the compact left cut. -/
theorem boundary_coordinateUnlinkExteriorPlanarNeckLeftSmoothCapping_radial :
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    coordinateUnlinkExteriorModel.boundary
        (CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m) =
      topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) ''
        ((Subtype.val : CompactNeckLeftCut m →
          CoordinateUnlinkExteriorEighthPowerPullback m) ⁻¹'
            coordinateUnlinkExteriorModel.boundary
              (CoordinateUnlinkExteriorEighthPowerPullback m)) := by
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ := compactNeckLeftCutChartedSpace m
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  rw [boundary_coordinateUnlinkExteriorPlanarNeckLeftSmoothCapping,
    boundary_compactNeckLeftCut_sdiff_smoothCappingAttachingRange,
    range_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap,
    sdiff_self, image_empty, union_empty]

/-- For the direct right capping atlas, the boundary is exactly the pushout image of the old
ambient radial boundary in the compact right cut. -/
theorem boundary_coordinateUnlinkExteriorPlanarNeckRightSmoothCapping_radial :
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    letI := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
    coordinateUnlinkExteriorModel.boundary
        (CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping m) =
      topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) ''
        ((Subtype.val : CompactNeckRightCut m →
          CoordinateUnlinkExteriorEighthPowerPullback m) ⁻¹'
            coordinateUnlinkExteriorModel.boundary
              (CoordinateUnlinkExteriorEighthPowerPullback m)) := by
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ := compactNeckRightCutChartedSpace m
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  rw [boundary_coordinateUnlinkExteriorPlanarNeckRightSmoothCapping,
    boundary_compactNeckRightCut_sdiff_smoothCappingAttachingRange,
    range_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap,
    sdiff_self, image_empty, union_empty]

end SplittingSpheres
