/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCapReparametrization
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCompactCutComparison
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckSmoothCapping

/-!
# Comparing the old and direct smooth neck cappings

The original planar neck cappings are topological pushouts built from product caps.  This file
compares their boundary, body, and cap pieces with the compact cuts and direct Euclidean-ball
families, then applies the point-set pushout congruence to identify the old capped spaces with the
direct smooth-capping spaces.

All results here are point-set homeomorphisms and exact coprojection formulas.  No charted-space
transport, diffeomorphism, smoothness, or manifold-boundary comparison is asserted.
-/

@[expose] public section

open Function Set Topology
open scoped Topology

noncomputable section

namespace SplittingSpheres

private local instance comparisonStandardPowerChartedSpace (m : ℕ) [NeZero m] :
    ChartedSpace (EuclideanSpace ℝ (Fin 4)) (StandardUnlinkPowerPullback m) :=
  standardUnlinkPowerPullbackChartedSpace m

private local instance comparisonCompactExteriorPowerChartedSpace (m : ℕ) [NeZero m] :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
  coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m

private theorem comparisonStrictEquator_inclusion
    (m : ℕ) [NeZero m] (a : ZMod m) (s : Sphere 3) :
    coordinateUnlinkExteriorEighthPowerPullbackToComplement m
        (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m
          (equatorUnlinkPowerLift m a s)).1 =
      equatorUnlinkPowerLift m a s := by
  rw [standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_equatorUnlinkPowerLift]
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    exact equatorUnlinkClosedTubeExteriorPowerLift_powerCoordinate m a s

private theorem compactCollarZero_neckEquatorHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) (s : Sphere 3) :
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a
        (coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph m a s) =
      coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
        (coordinateUnlinkExteriorPlanarNeckSphereMap m a s) := by
  apply coordinateUnlinkExteriorEighthPowerPullbackToComplement_injective m
  rw [coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero_eq,
    comparisonStrictEquator_inclusion]
  simpa only [Function.comp_apply, sub_add_cancel,
    coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph_apply,
    coordinateUnlinkExteriorPlanarTransportedNeckSphereMap_apply] using
      (congrFun (transportedNeckSphereMap_eq_equatorPowerLift_comp_reparam m
        (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m)) s).symm

private theorem leftCutAttachingMap_coe
    (m : ℕ) [NeZero m] (p : ZMod m × Sphere 3) :
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

private theorem rightCutAttachingMap_coe
    (m : ℕ) [NeZero m] (p : ZMod m × Sphere 3) :
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

private theorem compactStar_compactCollarZero_neckEquatorHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) (s : Sphere 3) :
    coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
        (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a
          (coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph m a s)) =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m (a, s)) := by
  rw [compactCollarZero_neckEquatorHomeomorph,
    coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph, Homeomorph.trans_apply,
    (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm_apply_apply]
  simpa only [coordinateUnlinkExteriorPlanarNeckSphereFamily_apply] using
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar_neckSphereFamily
      m (a, s)

private theorem compactStar_compactCollarZero_neckEquatorHomeomorph_right
    (m : ℕ) [NeZero m] (a : ZMod m) (s : Sphere 3) :
    coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
        (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m a
          (coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph m a s)) =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m)
        (coordinateUnlinkExteriorPlanarNeckStarToRight m (a, s)) := by
  rw [compactStar_compactCollarZero_neckEquatorHomeomorph]
  exact topologicalPushout_condition
    (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
    (coordinateUnlinkExteriorPlanarNeckStarToRight m) (a, s)

/-- Identify the old left attaching boundary with the labelled smooth three-spheres. -/
def coordinateUnlinkExteriorPlanarNeckOldLeftBoundaryHomeomorphSmoothBoundary
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckLeftFamilyBoundary m ≃ₜ
      ZMod m × Sphere 3 :=
  (coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryHomeomorphSphere m).trans
    (coordinateUnlinkExteriorPlanarNeckEquatorFamilyHomeomorph m)

/-- Identify the old uncapped left body with the compact left cut carrier. -/
def coordinateUnlinkExteriorPlanarNeckOldLeftUncappedHomeomorphCompactCut
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckLeftFamilyUncapped m ≃ₜ
      CompactNeckLeftCut m :=
  (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphComplementOneHandles
    m).trans (compactNeckLeftCutHomeomorphNeckLeftComplement m).symm

/-- Identify the old labelled left product caps with the direct Euclidean four-ball family. -/
def coordinateUnlinkExteriorPlanarNeckOldLeftCapsHomeomorphSmoothCaps
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckLeftFamilyCaps m ≃ₜ
      ZMod m × EuclideanFourBall :=
  (coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsHomeomorphProductFourBall m).trans
    (coordinateUnlinkExteriorPlanarNeckReparametrizedProductCapFamilyHomeomorph m)

private theorem oldLeftUncapped_boundary_to_star
    (m : ℕ) [NeZero m]
    (q : CoordinateUnlinkExteriorPlanarNeckLeftFamilyBoundary m) :
    coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphComplementOneHandles m
        (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped m q) =
      coordinateUnlinkExteriorPlanarNeckStarToLeft m
        (coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryHomeomorphSphere m q) := by
  rw [coordinateUnlinkExteriorPlanarNeckStarToLeft_apply]
  unfold coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryHomeomorphSphere
    coordinateUnlinkExteriorPlanarNeckGridVerticalLeftHomeomorphComplement
  simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  rw [(coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphComplementOneHandles
    m).injective.eq_iff]
  apply (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal m).injective
  rw [(coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphOriginal m).apply_symm_apply]
  exact simLeft_uncapped_compatibility m q

/-- The old-to-compact left body comparison commutes with the attaching maps. -/
theorem coordinateUnlinkExteriorPlanarNeckOldLeftUncappedHomeomorphCompactCut_boundary
    (m : ℕ) [NeZero m]
    (q : CoordinateUnlinkExteriorPlanarNeckLeftFamilyBoundary m) :
    coordinateUnlinkExteriorPlanarNeckOldLeftUncappedHomeomorphCompactCut m
        (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped m q) =
      coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m
        (coordinateUnlinkExteriorPlanarNeckOldLeftBoundaryHomeomorphSmoothBoundary m q) := by
  apply Subtype.ext
  apply (coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m).injective
  let p := coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryHomeomorphSphere m q
  let z := coordinateUnlinkExteriorPlanarNeckOldLeftUncappedHomeomorphCompactCut m
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped m q)
  calc
    coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
        z.1 =
        topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m)
          (compactNeckLeftCutHomeomorphNeckLeftComplement m z) := by
            exact (compactNeckLeftCutHomeomorphNeckLeftComplement_inclusion m z).symm
    _ = topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m)
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m p) := by
            apply congrArg
            change (compactNeckLeftCutHomeomorphNeckLeftComplement m)
                ((compactNeckLeftCutHomeomorphNeckLeftComplement m).symm
                  (
                coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedHomeomorphComplementOneHandles
                  m
                (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped m q))) = _
            rw [(compactNeckLeftCutHomeomorphNeckLeftComplement m).apply_symm_apply]
            exact oldLeftUncapped_boundary_to_star m q
    _ = coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m
          (coordinateUnlinkExteriorPlanarNeckOldLeftBoundaryHomeomorphSmoothBoundary m q)).1 := by
      rw [leftCutAttachingMap_coe]
      symm
      change coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
          (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m p.1
            (coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph m p.1 p.2)) =
        topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m)
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m p)
      simpa only [Prod.eta] using
        (compactStar_compactCollarZero_neckEquatorHomeomorph m p.1 p.2)

private theorem coordinateUnlinkExteriorPlanarNeckOldLeftCapsHomeomorphSmoothCaps_boundary
    (m : ℕ) [NeZero m]
    (q : CoordinateUnlinkExteriorPlanarNeckLeftFamilyBoundary m) :
    coordinateUnlinkExteriorPlanarNeckOldLeftCapsHomeomorphSmoothCaps m
        (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps m q) =
      (let p := coordinateUnlinkExteriorPlanarNeckOldLeftBoundaryHomeomorphSmoothBoundary m q
       (p.1,
        (euclideanFourBallBoundaryHomeomorphSphereThree.symm p.2).1)) := by
  rw [coordinateUnlinkExteriorPlanarNeckOldLeftCapsHomeomorphSmoothCaps, Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarNeckLeftFamily_boundary]
  change coordinateUnlinkExteriorPlanarNeckReparametrizedProductCapFamilyHomeomorph m
      (let p := coordinateUnlinkExteriorPlanarNeckLeftFamilyBoundaryHomeomorphSphere m q
       (p.1, productFourSphereBoundaryInclusion p.2)) = _
  rw [
    coordinateUnlinkExteriorPlanarNeckReparametrizedProductCapFamilyHomeomorph_boundary_inclusion]
  rfl

/-- The old-to-Euclidean left cap comparison commutes with the attaching maps. -/
theorem coordinateUnlinkExteriorPlanarNeckOldLeftCapsHomeomorphSmoothCaps_attaching
    (m : ℕ) [NeZero m]
    (q : CoordinateUnlinkExteriorPlanarNeckLeftFamilyBoundary m) :
    coordinateUnlinkExteriorPlanarNeckOldLeftCapsHomeomorphSmoothCaps m
        (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps m q) =
      coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m
        (coordinateUnlinkExteriorPlanarNeckOldLeftBoundaryHomeomorphSmoothBoundary m q) := by
  rw [coordinateUnlinkExteriorPlanarNeckOldLeftCapsHomeomorphSmoothCaps_boundary]
  let p := coordinateUnlinkExteriorPlanarNeckOldLeftBoundaryHomeomorphSmoothBoundary m q
  change (p.1, (euclideanFourBallBoundaryHomeomorphSphereThree.symm p.2).1) =
    (p.1, coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar
      (p.2, euclideanFourBallCollarZero))
  apply Prod.ext
  · rfl
  · rw [coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar_apply,
      euclideanFourBallSmoothCollar_zero_eq_boundaryHomeomorph_symm]

/-- Compare the old capped left family with the direct left smooth-capping pushout. -/
def coordinateUnlinkExteriorPlanarNeckOldLeftCappedHomeomorphSmoothCapping
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckLeftFamilyCapped m ≃ₜ
      CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m :=
  topologicalPushoutCongr
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToUncapped m)
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyNeckToCaps m)
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckOldLeftBoundaryHomeomorphSmoothBoundary m)
    (coordinateUnlinkExteriorPlanarNeckOldLeftUncappedHomeomorphCompactCut m)
    (coordinateUnlinkExteriorPlanarNeckOldLeftCapsHomeomorphSmoothCaps m)
    (coordinateUnlinkExteriorPlanarNeckOldLeftUncappedHomeomorphCompactCut_boundary m)
    (coordinateUnlinkExteriorPlanarNeckOldLeftCapsHomeomorphSmoothCaps_attaching m)

/-- The left capped comparison agrees with the body comparison on the left coprojection. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckOldLeftCappedHomeomorphSmoothCapping_inl
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckLeftFamilyUncapped m) :
    coordinateUnlinkExteriorPlanarNeckOldLeftCappedHomeomorphSmoothCapping m
        (coordinateUnlinkExteriorPlanarNeckLeftFamilyUncappedToCapped m x) =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckOldLeftUncappedHomeomorphCompactCut m x) := by
  apply topologicalPushoutCongr_inl

/-- The left capped comparison agrees with the cap comparison on the right coprojection. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckOldLeftCappedHomeomorphSmoothCapping_inr
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarNeckLeftFamilyCaps m) :
    coordinateUnlinkExteriorPlanarNeckOldLeftCappedHomeomorphSmoothCapping m
        (coordinateUnlinkExteriorPlanarNeckLeftFamilyCapsToCapped m x) =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckOldLeftCapsHomeomorphSmoothCaps m x) := by
  apply topologicalPushoutCongr_inr

/-- Identify the old right attaching boundary with the labelled smooth three-spheres. -/
def coordinateUnlinkExteriorPlanarNeckOldRightBoundaryHomeomorphSmoothBoundary
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarRightNodeNeckBoundaryFamily m ≃ₜ
      ZMod m × Sphere 3 :=
  (coordinateUnlinkExteriorPlanarRightNodeNeckBoundaryHomeomorphSphere m).trans
    (coordinateUnlinkExteriorPlanarNeckEquatorFamilyHomeomorph m)

/-- Identify the old uncapped right body with the compact right cut carrier. -/
def coordinateUnlinkExteriorPlanarNeckOldRightUncappedHomeomorphCompactCut
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarRightNodeUncapped m ≃ₜ
      CompactNeckRightCut m :=
  (coordinateUnlinkExteriorPlanarRightNodeUncappedHomeomorphComplementOneHandle
    m).trans (compactNeckRightCutHomeomorphNeckRightComplement m).symm

/-- Identify the old right product-cap family with the direct Euclidean four-ball family. -/
def coordinateUnlinkExteriorPlanarNeckOldRightCapsHomeomorphSmoothCaps
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarRightNodeCapFamily m ≃ₜ
      ZMod m × EuclideanFourBall :=
  (coordinateUnlinkExteriorPlanarRightNodeCapFamilyHomeomorph m).trans
    (coordinateUnlinkExteriorPlanarNeckReparametrizedProductCapFamilyHomeomorph m)

private theorem oldRightUncapped_boundary_to_star
    (m : ℕ) [NeZero m]
    (q : CoordinateUnlinkExteriorPlanarRightNodeNeckBoundaryFamily m) :
    coordinateUnlinkExteriorPlanarRightNodeUncappedHomeomorphComplementOneHandle m
        (coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped m q) =
      coordinateUnlinkExteriorPlanarNeckStarToRight m
        (coordinateUnlinkExteriorPlanarRightNodeNeckBoundaryHomeomorphSphere m q) := by
  rw [coordinateUnlinkExteriorPlanarNeckStarToRight_apply]
  unfold coordinateUnlinkExteriorPlanarRightNodeNeckBoundaryHomeomorphSphere
    coordinateUnlinkExteriorPlanarNeckGridVerticalRightHomeomorphComplement
  simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  rw [(coordinateUnlinkExteriorPlanarRightNodeUncappedHomeomorphComplementOneHandle
    m).injective.eq_iff]
  rfl

/-- The old-to-compact right body comparison commutes with the attaching maps. -/
theorem coordinateUnlinkExteriorPlanarNeckOldRightUncappedHomeomorphCompactCut_boundary
    (m : ℕ) [NeZero m]
    (q : CoordinateUnlinkExteriorPlanarRightNodeNeckBoundaryFamily m) :
    coordinateUnlinkExteriorPlanarNeckOldRightUncappedHomeomorphCompactCut m
        (coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped m q) =
      coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m
        (coordinateUnlinkExteriorPlanarNeckOldRightBoundaryHomeomorphSmoothBoundary m q) := by
  apply Subtype.ext
  apply (coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m).injective
  let p := coordinateUnlinkExteriorPlanarRightNodeNeckBoundaryHomeomorphSphere m q
  let z := coordinateUnlinkExteriorPlanarNeckOldRightUncappedHomeomorphCompactCut m
    (coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped m q)
  calc
    coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
        z.1 =
        topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m)
          (compactNeckRightCutHomeomorphNeckRightComplement m z) := by
            exact (compactNeckRightCutHomeomorphNeckRightComplement_inclusion m z).symm
    _ = topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m p) := by
            apply congrArg
            change (compactNeckRightCutHomeomorphNeckRightComplement m)
                ((compactNeckRightCutHomeomorphNeckRightComplement m).symm
                  (coordinateUnlinkExteriorPlanarRightNodeUncappedHomeomorphComplementOneHandle m
                    (coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped m q))) = _
            rw [(compactNeckRightCutHomeomorphNeckRightComplement m).apply_symm_apply]
            exact oldRightUncapped_boundary_to_star m q
    _ = coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m
          (coordinateUnlinkExteriorPlanarNeckOldRightBoundaryHomeomorphSmoothBoundary m q)).1 := by
      rw [rightCutAttachingMap_coe]
      symm
      change coordinateUnlinkExteriorPlanarCompactNeckStarHomeomorph m
          (coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarZero m p.1
            (coordinateUnlinkExteriorPlanarNeckEquatorHomeomorph m p.1 p.2)) =
        topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckStarToLeft m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m)
          (coordinateUnlinkExteriorPlanarNeckStarToRight m p)
      simpa only [Prod.eta] using
        (compactStar_compactCollarZero_neckEquatorHomeomorph_right m p.1 p.2)

private theorem coordinateUnlinkExteriorPlanarNeckOldRightCapsHomeomorphSmoothCaps_boundary
    (m : ℕ) [NeZero m]
    (q : CoordinateUnlinkExteriorPlanarRightNodeNeckBoundaryFamily m) :
    coordinateUnlinkExteriorPlanarNeckOldRightCapsHomeomorphSmoothCaps m
        (coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m q) =
      (let p := coordinateUnlinkExteriorPlanarNeckOldRightBoundaryHomeomorphSmoothBoundary m q
       (p.1,
        (euclideanFourBallBoundaryHomeomorphSphereThree.symm p.2).1)) := by
  rw [coordinateUnlinkExteriorPlanarNeckOldRightCapsHomeomorphSmoothCaps, Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarRightNode_neckToCapFamily_conjugacy]
  change coordinateUnlinkExteriorPlanarNeckReparametrizedProductCapFamilyHomeomorph m
      (let p := coordinateUnlinkExteriorPlanarRightNodeNeckBoundaryHomeomorphSphere m q
       (p.1, productFourSphereBoundaryInclusion p.2)) = _
  rw [
    coordinateUnlinkExteriorPlanarNeckReparametrizedProductCapFamilyHomeomorph_boundary_inclusion]
  rfl

/-- The old-to-Euclidean right cap comparison commutes with the attaching maps. -/
theorem coordinateUnlinkExteriorPlanarNeckOldRightCapsHomeomorphSmoothCaps_attaching
    (m : ℕ) [NeZero m]
    (q : CoordinateUnlinkExteriorPlanarRightNodeNeckBoundaryFamily m) :
    coordinateUnlinkExteriorPlanarNeckOldRightCapsHomeomorphSmoothCaps m
        (coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m q) =
      coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m
        (coordinateUnlinkExteriorPlanarNeckOldRightBoundaryHomeomorphSmoothBoundary m q) := by
  rw [coordinateUnlinkExteriorPlanarNeckOldRightCapsHomeomorphSmoothCaps_boundary]
  let p := coordinateUnlinkExteriorPlanarNeckOldRightBoundaryHomeomorphSmoothBoundary m q
  change (p.1, (euclideanFourBallBoundaryHomeomorphSphereThree.symm p.2).1) =
    (p.1, coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar
      (p.2, euclideanFourBallCollarZero))
  apply Prod.ext
  · rfl
  · rw [coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar_apply,
      euclideanFourBallSmoothCollar_zero_eq_boundaryHomeomorph_symm]

/-- Compare the old capped right node with the direct right smooth-capping pushout. -/
def coordinateUnlinkExteriorPlanarNeckOldRightCappedHomeomorphSmoothCapping
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarRightNodeCapped m ≃ₜ
      CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping m :=
  (topologicalPushoutComm
    (coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m)
    (coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped m)).trans
      (topologicalPushoutCongr
        (coordinateUnlinkExteriorPlanarRightNodeNeckToUncapped m)
        (coordinateUnlinkExteriorPlanarRightNodeNeckToCapFamily m)
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckOldRightBoundaryHomeomorphSmoothBoundary m)
        (coordinateUnlinkExteriorPlanarNeckOldRightUncappedHomeomorphCompactCut m)
        (coordinateUnlinkExteriorPlanarNeckOldRightCapsHomeomorphSmoothCaps m)
        (coordinateUnlinkExteriorPlanarNeckOldRightUncappedHomeomorphCompactCut_boundary m)
        (coordinateUnlinkExteriorPlanarNeckOldRightCapsHomeomorphSmoothCaps_attaching m))

/-- The right capped comparison agrees with the cap comparison on the cap coprojection. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckOldRightCappedHomeomorphSmoothCapping_cap
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarRightNodeCapFamily m) :
    coordinateUnlinkExteriorPlanarNeckOldRightCappedHomeomorphSmoothCapping m
        (coordinateUnlinkExteriorPlanarRightNodeCapFamilyToCapped m x) =
      topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckOldRightCapsHomeomorphSmoothCaps m x) := by
  rw [coordinateUnlinkExteriorPlanarNeckOldRightCappedHomeomorphSmoothCapping,
    Homeomorph.trans_apply,
    topologicalPushoutComm_inl, topologicalPushoutCongr_inr]

/-- The right capped comparison agrees with the body comparison on the body coprojection. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckOldRightCappedHomeomorphSmoothCapping_body
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarRightNodeUncapped m) :
    coordinateUnlinkExteriorPlanarNeckOldRightCappedHomeomorphSmoothCapping m
        (coordinateUnlinkExteriorPlanarRightNodeUncappedToCapped m x) =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckOldRightUncappedHomeomorphCompactCut m x) := by
  rw [coordinateUnlinkExteriorPlanarNeckOldRightCappedHomeomorphSmoothCapping,
    Homeomorph.trans_apply,
    topologicalPushoutComm_inr, topologicalPushoutCongr_inl]

/-- Recognize the direct left smooth-capping pushout as the labelled family of point-set
one-handles. -/
def coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingHomeomorphOneHandle
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m ≃ₜ
      ZMod m × OneHandlePiece :=
  (coordinateUnlinkExteriorPlanarNeckOldLeftCappedHomeomorphSmoothCapping m).symm.trans
    (coordinateUnlinkExteriorPlanarNeckLeftFamilyCappedHomeomorphOneHandle m)

/-- Recognize the direct right smooth-capping pushout as the point-set one-handle. -/
def coordinateUnlinkExteriorPlanarNeckRightSmoothCappingHomeomorphOneHandle
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping m ≃ₜ OneHandlePiece :=
  (coordinateUnlinkExteriorPlanarNeckOldRightCappedHomeomorphSmoothCapping m).symm.trans
    (coordinateUnlinkExteriorPlanarRightNodeCappedHomeomorphOneHandle m)

end SplittingSpheres
