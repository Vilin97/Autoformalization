/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckRightSmoothCappingOneHandleDiffeomorph
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckSmoothCappingDiffeomorphismRecognition
public import SplittingSpheres.Handlebody.CoordinateExteriorRoundedCapPowerTrivialization
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCompactCoordinateCaps
public import SplittingSpheres.Foundations.DiffeomorphOverLocalDiffeomorph
import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckSmoothCappingRadialBoundary
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Direct recognition of the left smooth capping as labelled one-handles

This file identifies the direct left smooth capping with a labelled family of natural
one-handles.  The construction trivializes the compact left cut through the direct rounded-cap
power pullback, reflects the left unlink component onto the right-tube carrier, and uses the
literal standard collar on that carrier.  The reflection agrees exactly with the component-one
standard exterior collar, so the cut, cap, and signed-seam generators are local diffeomorphisms
for the direct atlases.

The analytic reflection and trivialization machinery is private.  A small construction record
retains only the semantic body and cap maps, their point-set homeomorphism, and the resulting
smooth comparison needed by the public endpoint.
-/

open Function Metric Set Topology TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

private def coordinateThreeSignLinearIsometry (i : Fin 5) :
    ℝ ≃ₗᵢ[ℝ] ℝ :=
  if i = 3 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

private def coordinateThreeReflectionLinearIsometry :
    EuclideanSpace ℝ (Fin 5) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 5) :=
  LinearIsometryEquiv.piLpCongrRight 2 coordinateThreeSignLinearIsometry

private theorem coordinateThreeReflectionLinearIsometry_apply
    (x : EuclideanSpace ℝ (Fin 5)) (i : Fin 5) :
    coordinateThreeReflectionLinearIsometry x i =
      if i = 3 then -x i else x i := by
  simp only [coordinateThreeReflectionLinearIsometry,
    coordinateThreeSignLinearIsometry,
    LinearIsometryEquiv.piLpCongrRight_apply]
  split_ifs <;> rfl

private theorem coordinateThreeReflectionLinearIsometry_involutive
    (x : EuclideanSpace ℝ (Fin 5)) :
    coordinateThreeReflectionLinearIsometry
        (coordinateThreeReflectionLinearIsometry x) = x := by
  ext i
  rw [coordinateThreeReflectionLinearIsometry_apply,
    coordinateThreeReflectionLinearIsometry_apply]
  split_ifs <;> simp

private def coordinateThreeReflectionSphere (q : Sphere 4) : Sphere 4 :=
  ⟨coordinateThreeReflectionLinearIsometry q.1, by
    rw [mem_sphere_zero_iff_norm]
    rw [coordinateThreeReflectionLinearIsometry.norm_map]
    exact mem_sphere_zero_iff_norm.mp q.2⟩

private theorem coordinateThreeReflectionSphere_coe (q : Sphere 4) :
    (coordinateThreeReflectionSphere q : EuclideanSpace ℝ (Fin 5)) =
      coordinateThreeReflectionLinearIsometry q.1 :=
  rfl

private theorem coordinateThreeReflectionSphere_apply
    (q : Sphere 4) (i : Fin 5) :
    (coordinateThreeReflectionSphere q : EuclideanSpace ℝ (Fin 5)) i =
      if i = 3 then -q.1 i else q.1 i := by
  simp [coordinateThreeReflectionSphere_coe,
    coordinateThreeReflectionLinearIsometry_apply]

private def coordinateThreeReflectionSphereHomeomorph : Sphere 4 ≃ₜ Sphere 4 where
  toFun := coordinateThreeReflectionSphere
  invFun := coordinateThreeReflectionSphere
  left_inv q := by
    apply Subtype.ext
    exact coordinateThreeReflectionLinearIsometry_involutive q.1
  right_inv q := by
    apply Subtype.ext
    exact coordinateThreeReflectionLinearIsometry_involutive q.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact coordinateThreeReflectionLinearIsometry.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact coordinateThreeReflectionLinearIsometry.continuous.comp continuous_subtype_val

private theorem coordinateThreeReflectionSphere_involutive (q : Sphere 4) :
    coordinateThreeReflectionSphere (coordinateThreeReflectionSphere q) = q :=
  coordinateThreeReflectionSphereHomeomorph.left_inv q

private def coordinateZeroSignLinearIsometry (i : Fin 2) :
    ℝ ≃ₗᵢ[ℝ] ℝ :=
  if i = 0 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

private def coordinateZeroReflectionNormalLinearIsometry :
    UnlinkNormalPlane ≃ₗᵢ[ℝ] UnlinkNormalPlane :=
  LinearIsometryEquiv.piLpCongrRight 2 coordinateZeroSignLinearIsometry

private theorem coordinateZeroReflectionNormalLinearIsometry_apply
    (x : UnlinkNormalPlane) (i : Fin 2) :
    coordinateZeroReflectionNormalLinearIsometry x i =
      if i = 0 then -x i else x i := by
  simp only [coordinateZeroReflectionNormalLinearIsometry,
    coordinateZeroSignLinearIsometry,
    LinearIsometryEquiv.piLpCongrRight_apply]
  split_ifs <;> rfl

private def coordinateZeroReflectionCircle (u : Sphere 1) : Sphere 1 :=
  ⟨coordinateZeroReflectionNormalLinearIsometry u.1, by
    rw [mem_sphere_zero_iff_norm,
      coordinateZeroReflectionNormalLinearIsometry.norm_map]
    exact mem_sphere_zero_iff_norm.mp u.2⟩

private theorem coordinateZeroReflectionCircle_coe (u : Sphere 1) :
    (coordinateZeroReflectionCircle u : UnlinkNormalPlane) =
      coordinateZeroReflectionNormalLinearIsometry u.1 :=
  rfl

private theorem coordinateZeroReflectionCircle_apply
    (u : Sphere 1) (i : Fin 2) :
    (coordinateZeroReflectionCircle u : UnlinkNormalPlane) i =
      if i = 0 then -u.1 i else u.1 i := by
  rw [coordinateZeroReflectionCircle_coe,
    coordinateZeroReflectionNormalLinearIsometry_apply]

local instance coordinateZeroReflectionNormalFinrank :
    Fact (Module.finrank ℝ UnlinkNormalPlane = 1 + 1) := ⟨by simp⟩

private def coordinateZeroReflectionCircleDiffeomorph :
    Sphere 1 ≃ₘ^∞⟮
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)),
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))⟯ Sphere 1 :=
  TauCeti.LinearIsometryEquiv.unitSphereDiffeomorph
    (n := 1) (k := 1) coordinateZeroReflectionNormalLinearIsometry ∞

private theorem coordinateZeroReflectionCircleDiffeomorph_apply (u : Sphere 1) :
    coordinateZeroReflectionCircleDiffeomorph u =
      coordinateZeroReflectionCircle u := by
  apply Subtype.ext
  exact TauCeti.LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply
    coordinateZeroReflectionNormalLinearIsometry u

local instance coordinateThreeReflectionAmbientFinrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) := ⟨by simp⟩

private def coordinateThreeReflectionSphereStandardDiffeomorph :
    Sphere 4 ≃ₘ^∞⟮
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)),
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))⟯ Sphere 4 :=
  TauCeti.LinearIsometryEquiv.unitSphereDiffeomorph
    (n := 4) (k := 4) coordinateThreeReflectionLinearIsometry ∞

private theorem coordinateThreeReflectionSphereStandardDiffeomorph_apply
    (q : Sphere 4) :
    coordinateThreeReflectionSphereStandardDiffeomorph q =
      coordinateThreeReflectionSphere q := by
  apply Subtype.ext
  exact TauCeti.LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply
    coordinateThreeReflectionLinearIsometry q

private def coordinateThreeReflectionSphereCommonDiffeomorph :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    Sphere 4 ≃ₘ^∞⟮coordinateUnlinkExteriorModel,
      coordinateUnlinkExteriorModel⟯ Sphere 4 := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  exact coordinateUnlinkExteriorCommonModelToStandardSphereIdentityDiffeomorph.trans
    (coordinateThreeReflectionSphereStandardDiffeomorph.trans
      standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph)

private theorem coordinateThreeReflectionSphereCommonDiffeomorph_apply
    (q : Sphere 4) :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    coordinateThreeReflectionSphereCommonDiffeomorph q =
      coordinateThreeReflectionSphere q := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  change coordinateThreeReflectionSphereStandardDiffeomorph q =
    coordinateThreeReflectionSphere q
  exact coordinateThreeReflectionSphereStandardDiffeomorph_apply q

private theorem coordinateThreeReflectionSphere_normal_sub_center_one
    (q : Sphere 4) :
    standardUnlinkNormalProjection (coordinateThreeReflectionSphere q) -
        standardUnlinkNormalCenter 1 =
      coordinateZeroReflectionNormalLinearIsometry
        (standardUnlinkNormalProjection q - standardUnlinkNormalCenter 0) := by
  ext i
  fin_cases i <;>
    simp [coordinateZeroReflectionNormalLinearIsometry_apply,
      coordinateThreeReflectionSphere_apply, standardUnlinkHeight]

private theorem norm_coordinateThreeReflectionSphere_sub_center_one
    (q : Sphere 4) :
    ‖standardUnlinkNormalProjection (coordinateThreeReflectionSphere q) -
        standardUnlinkNormalCenter 1‖ =
      ‖standardUnlinkNormalProjection q - standardUnlinkNormalCenter 0‖ := by
  rw [coordinateThreeReflectionSphere_normal_sub_center_one]
  exact coordinateZeroReflectionNormalLinearIsometry.norm_map _

private theorem coordinateThreeReflectionSphere_mem_openTube_one_iff
    (q : Sphere 4) (r : ℝ) :
    coordinateThreeReflectionSphere q ∈ standardUnlinkOpenTube 1 r ↔
      q ∈ standardUnlinkOpenTube 0 r := by
  simp only [standardUnlinkOpenTube, mem_preimage, mem_ball, dist_eq_norm]
  rw [norm_coordinateThreeReflectionSphere_sub_center_one]

private theorem coordinateThreeReflectionSphere_mem_openTube_zero_iff
    (q : Sphere 4) (r : ℝ) :
    coordinateThreeReflectionSphere q ∈ standardUnlinkOpenTube 0 r ↔
      q ∈ standardUnlinkOpenTube 1 r := by
  have h := coordinateThreeReflectionSphere_mem_openTube_one_iff
    (coordinateThreeReflectionSphere q) r
  rw [coordinateThreeReflectionSphere_involutive] at h
  exact h.symm

private theorem coordinateThreeReflectionSphere_coord_three (q : Sphere 4) :
    (coordinateThreeReflectionSphere q : EuclideanSpace ℝ (Fin 5)) 3 = -q.1 3 := by
  rw [coordinateThreeReflectionSphere_apply]
  simp

private theorem coordinateThreeReflectionSphere_of_mem_equator
    (q : Sphere 4) (hq : q ∈ coordinateEquator) :
    coordinateThreeReflectionSphere q = q := by
  apply Subtype.ext
  ext i
  rw [coordinateThreeReflectionSphere_apply]
  split_ifs with hi
  · subst i
    change q.1 3 = 0 at hq
    simp [hq]
  · rfl

private theorem standardUnlinkOpenTubeDiffeomorph_coe_eq_spherePolarForward
    (i : Fin 2) {r : ℝ} (hr : r < 1 / 2)
    (p : Sphere 2 × UnlinkNormalDisk i r) :
    ((standardUnlinkOpenTubeDiffeomorph i hr p).1 : Sphere 4) =
      (spherePolarForward (spherePolarTubeDomainInclusion i hr p)).1 := by
  rfl

set_option linter.flexible false in
private theorem coordinateThreeReflectionSphere_standardUnlinkExteriorCollar
    (p : Sphere 2 ×
      (Sphere 1 × CoordinateUnlinkExteriorEighthCollarRadius)) :
    coordinateThreeReflectionSphere
        (standardUnlinkExteriorEighthCollarHomeomorph 0 p).1 =
      (standardUnlinkExteriorEighthCollarHomeomorph 1
        (p.1, (coordinateZeroReflectionCircle p.2.1, p.2.2))).1 := by
  unfold standardUnlinkExteriorEighthCollarHomeomorph
  rw [standardUnlinkExteriorCollarHomeomorph_coe,
    standardUnlinkExteriorCollarHomeomorph_coe,
    standardUnlinkOpenTubeDiffeomorph_coe_eq_spherePolarForward,
    standardUnlinkOpenTubeDiffeomorph_coe_eq_spherePolarForward]
  have hnormal :
      standardUnlinkNormalCenter 1 +
          unlinkExteriorCollarRadiusValue p.2.2 •
            (coordinateZeroReflectionCircle p.2.1 : UnlinkNormalPlane) =
        coordinateZeroReflectionNormalLinearIsometry
          (standardUnlinkNormalCenter 0 +
            unlinkExteriorCollarRadiusValue p.2.2 • p.2.1.1) := by
    ext i
    fin_cases i <;>
      simp [coordinateZeroReflectionNormalLinearIsometry_apply,
        coordinateZeroReflectionCircle_apply, standardUnlinkHeight]
  have hscale :
      spherePolarScale
          (standardUnlinkNormalCenter 0 +
            unlinkExteriorCollarRadiusValue p.2.2 • p.2.1.1) =
        spherePolarScale
          (standardUnlinkNormalCenter 1 +
            unlinkExteriorCollarRadiusValue p.2.2 •
              (coordinateZeroReflectionCircle p.2.1 : UnlinkNormalPlane)) := by
    simp only [spherePolarScale]
    rw [hnormal, coordinateZeroReflectionNormalLinearIsometry.norm_map]
  apply Subtype.ext
  ext i
  fin_cases i
  all_goals simp [spherePolarTubeDomainInclusion, spherePolarForward_coe,
      spherePolarAmbientMap, unlinkNormalExteriorCollarInDisk_coe,
      unlinkNormalExteriorCollarForward_coe,
      coordinateThreeReflectionSphere_apply,
      coordinateZeroReflectionCircle_apply, standardUnlinkHeight]
  · exact Or.inl hscale
  · exact Or.inl hscale
  · exact Or.inl hscale
  · ring

private theorem coordinateThreeReflectionSphere_equatorCollar
    (p : Sphere 3 × EquatorCollarInterval) :
    coordinateThreeReflectionSphere (equatorCollarSphereMap p) =
      equatorCollarSphereMap
        (p.1, coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2) := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [coordinateThreeReflectionSphere_apply, equatorCollarSphereMap,
      equatorCollarAmbientMap, equatorCollarScale,
      coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph]

private def coordinateZeroReflectionExteriorCollarDiffeomorphNatural :
    CoordinateUnlinkExteriorEighthCollarDomain ≃ₘ^∞⟮
      standardUnlinkExteriorCollarModel,
      standardUnlinkExteriorCollarModel⟯
        CoordinateUnlinkExteriorEighthCollarDomain :=
  (Diffeomorph.refl
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (Sphere 2) ∞).prodCongr
    (coordinateZeroReflectionCircleDiffeomorph.prodCongr
      (Diffeomorph.refl (modelWithCornersEuclideanHalfSpace 1)
        CoordinateUnlinkExteriorEighthCollarRadius ∞))

private theorem coordinateZeroReflectionExteriorCollarDiffeomorphNatural_apply
    (p : CoordinateUnlinkExteriorEighthCollarDomain) :
    coordinateZeroReflectionExteriorCollarDiffeomorphNatural p =
      (p.1, (coordinateZeroReflectionCircle p.2.1, p.2.2)) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact coordinateZeroReflectionCircleDiffeomorph_apply p.2.1
    · rfl

private def coordinateZeroReflectionExteriorCollarDiffeomorph :
    CoordinateUnlinkExteriorEighthCollarDomain ≃ₘ^∞⟮
      coordinateUnlinkExteriorModel, coordinateUnlinkExteriorModel⟯
        CoordinateUnlinkExteriorEighthCollarDomain where
  toEquiv := coordinateZeroReflectionExteriorCollarDiffeomorphNatural.toEquiv
  contMDiff_toFun := by
    rw [ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left,
      ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right]
    exact coordinateZeroReflectionExteriorCollarDiffeomorphNatural.contMDiff
  contMDiff_invFun := by
    rw [ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left,
      ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right]
    exact coordinateZeroReflectionExteriorCollarDiffeomorphNatural.symm.contMDiff

private theorem coordinateZeroReflectionExteriorCollarDiffeomorph_apply
    (p : CoordinateUnlinkExteriorEighthCollarDomain) :
    coordinateZeroReflectionExteriorCollarDiffeomorph p =
      (p.1, (coordinateZeroReflectionCircle p.2.1, p.2.2)) :=
  coordinateZeroReflectionExteriorCollarDiffeomorphNatural_apply p

variable (m : ℕ) [NeZero m]

local instance commonModelFourBallChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace EuclideanFourBall :=
  coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace

local instance roundedClosedCapChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CollaredCutSide coordinateClosedCapZero) :=
  coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace

private theorem compactNeckLeftCut_mem_coordinateClosedCapZero
    (q : CompactNeckLeftCut m) :
    q.1.1.1.1 ∈ coordinateClosedCapZero := by
  change q.1.1.1.1 ∈ (coordinateOpenCap 1)ᶜ
  exact (Set.ext_iff.mp
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier_eq_preimage_compl_cap_one m)
      q.1).mp q.2

private def compactNeckLeftCutToRoundedCapPowerPullback
    (q : CompactNeckLeftCut m) :
    CoordinateExteriorRoundedCapPowerPullback m :=
  ⟨(⟨q.1.1.1.1, compactNeckLeftCut_mem_coordinateClosedCapZero m q⟩,
      q.1.1.2), by
    apply Subtype.ext
    exact congrArg Subtype.val q.1.2⟩

private theorem compactNeckLeftCutToRoundedCapPowerPullback_injective :
    Injective (compactNeckLeftCutToRoundedCapPowerPullback m) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z ↦ (z.1.1 : Sphere 4)) h
  · exact congrArg (fun z ↦ z.1.2) h

private theorem compactNeckLeftCut_reflection_mem_rightTubeClosedCarrier
    (q : CompactNeckLeftCut m) :
    coordinateThreeReflectionSphere q.1.1.1.1 ∈
      coordinateExteriorRightTubeClosedCarrier := by
  rw [coordinateExteriorRightTubeClosedCarrier_eq_compl_openTube]
  intro hreflect
  have hleft : q.1.1.1.1 ∈ standardUnlinkOpenTube 0 (1 / 8 : ℝ) :=
    (coordinateThreeReflectionSphere_mem_openTube_one_iff
      q.1.1.1.1 (1 / 8 : ℝ)).mp hreflect
  exact q.1.1.1.2 (Or.inl hleft)

private theorem coordinateUnlinkExteriorEighth_reflection_mem_rightTubeClosedCarrier
    (q : CoordinateUnlinkExteriorEighth) :
    coordinateThreeReflectionSphere q.1 ∈
      coordinateExteriorRightTubeClosedCarrier := by
  rw [coordinateExteriorRightTubeClosedCarrier_eq_compl_openTube]
  intro hreflect
  have hleft : q.1 ∈ standardUnlinkOpenTube 0 (1 / 8 : ℝ) :=
    (coordinateThreeReflectionSphere_mem_openTube_one_iff
      q.1 (1 / 8 : ℝ)).mp hreflect
  exact q.2 (Or.inl hleft)

private def leftCappingExteriorBaseReflectionToRightTube
    (q : CoordinateUnlinkExteriorEighth) : CoordinateExteriorRightTubeClosed :=
  ⟨coordinateThreeReflectionSphere q.1,
    coordinateUnlinkExteriorEighth_reflection_mem_rightTubeClosedCarrier q⟩

private theorem
    leftCappingExteriorBaseReflectionToRightTube_comp_leftCollar
    (p : CoordinateUnlinkExteriorEighthCollarDomain) :
    leftCappingExteriorBaseReflectionToRightTube
        (coordinateUnlinkExteriorEighthCollarToExterior 0 p) =
      coordinateExteriorRightTubeStandardBoundaryCollar
        (coordinateZeroReflectionExteriorCollarDiffeomorph p) := by
  apply Subtype.ext
  rw [coordinateExteriorRightTubeStandardBoundaryCollar_coe,
    coordinateExteriorRightTubeStandardCollarAmbient,
    coordinateZeroReflectionExteriorCollarDiffeomorph_apply]
  exact coordinateThreeReflectionSphere_standardUnlinkExteriorCollar p

private def compactNeckLeftCutLabel (q : CompactNeckLeftCut m) : ZMod m :=
  ((coordinateExteriorRoundedCapPowerTrivializationHomeomorph m).symm
    (compactNeckLeftCutToRoundedCapPowerPullback m q)).1

private theorem roundedCapPowerTrivializationHomeomorph_symm_snd
    (z : CoordinateExteriorRoundedCapPowerPullback m) :
    ((coordinateExteriorRoundedCapPowerTrivializationHomeomorph m).symm z).2 =
      z.1.1 := by
  have h := congrArg
    (fun w : CoordinateExteriorRoundedCapPowerPullback m ↦ w.1.1)
    ((coordinateExteriorRoundedCapPowerTrivializationHomeomorph m).apply_symm_apply z)
  exact h

private def compactNeckLeftCutReflectedBase
    (q : CompactNeckLeftCut m) : CoordinateExteriorRightTubeClosed :=
  ⟨coordinateThreeReflectionSphere q.1.1.1.1,
    compactNeckLeftCut_reflection_mem_rightTubeClosedCarrier m q⟩

private def leftCappingBodyMap
    (q : CompactNeckLeftCut m) :
    ZMod m × CoordinateExteriorRightTubeClosed :=
  (compactNeckLeftCutLabel m q, compactNeckLeftCutReflectedBase m q)

private theorem leftCappingBodyMap_injective :
    Injective (leftCappingBodyMap m) := by
  intro x y h
  have hreflect : coordinateThreeReflectionSphere x.1.1.1.1 =
      coordinateThreeReflectionSphere y.1.1.1.1 :=
    congrArg (fun z ↦ (z.2.1 : Sphere 4)) h
  have hbase : x.1.1.1.1 = y.1.1.1.1 :=
    coordinateThreeReflectionSphereHomeomorph.injective hreflect
  have hlabel : compactNeckLeftCutLabel m x = compactNeckLeftCutLabel m y := by
    have h' := congrArg Prod.fst h
    change compactNeckLeftCutLabel m x = compactNeckLeftCutLabel m y at h'
    exact h'
  have hrounded : compactNeckLeftCutToRoundedCapPowerPullback m x =
      compactNeckLeftCutToRoundedCapPowerPullback m y := by
    apply (coordinateExteriorRoundedCapPowerTrivializationHomeomorph m).symm.injective
    apply Prod.ext hlabel
    rw [roundedCapPowerTrivializationHomeomorph_symm_snd,
      roundedCapPowerTrivializationHomeomorph_symm_snd]
    apply Subtype.ext
    exact hbase
  exact compactNeckLeftCutToRoundedCapPowerPullback_injective m hrounded

private def leftCappingCapMap
    (z : ZMod m × EuclideanFourBall) :
    ZMod m × CoordinateExteriorRightTubeClosed :=
  (z.1, ⟨(euclideanFourBallRoundedHemisphereDiffeomorph z.2).1,
    coordinateClosedCapZero_subset_rightTubeClosedCarrier
      (euclideanFourBallRoundedHemisphereDiffeomorph z.2).2⟩)

omit [NeZero m] in
private theorem leftCappingCapMap_injective :
    Injective (leftCappingCapMap m) := by
  intro x y h
  apply Prod.ext
  · have h' := congrArg Prod.fst h
    change x.1 = y.1 at h'
    exact h'
  · apply euclideanFourBallRoundedHemisphereDiffeomorph.injective
    apply Subtype.ext
    exact congrArg (fun z ↦ (z.2.1 : Sphere 4)) h

private theorem continuous_compactNeckLeftCutToRoundedCapPowerPullback :
    Continuous (compactNeckLeftCutToRoundedCapPowerPullback m) := by
  unfold compactNeckLeftCutToRoundedCapPowerPullback
  fun_prop

private def leftCappingBodyContinuousMap :
    C(CompactNeckLeftCut m, ZMod m × CoordinateExteriorRightTubeClosed) where
  toFun := leftCappingBodyMap m
  continuous_toFun := by
    have hlabel : Continuous (compactNeckLeftCutLabel m) :=
      (coordinateExteriorRoundedCapPowerTrivializationHomeomorph m).symm.continuous.fst.comp
        (continuous_compactNeckLeftCutToRoundedCapPowerPullback m)
    have hbase : Continuous (fun q : CompactNeckLeftCut m ↦ q.1.1.1.1) := by
      fun_prop
    have hreflect : Continuous
        (fun q : CompactNeckLeftCut m ↦ coordinateThreeReflectionSphere q.1.1.1.1) :=
      coordinateThreeReflectionSphereHomeomorph.continuous.comp hbase
    exact hlabel.prodMk (Continuous.subtype_mk hreflect _)

private def leftCappingCapContinuousMap :
    C(ZMod m × EuclideanFourBall,
      ZMod m × CoordinateExteriorRightTubeClosed) where
  toFun := leftCappingCapMap m
  continuous_toFun := by
    unfold leftCappingCapMap
    fun_prop

private theorem leftCapping_attaching_corestriction
    (a : ZMod m) (s : Sphere 3) :
    compactNeckLeftCutToRoundedCapPowerPullback m
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m (a, s)) =
      coordinateExteriorRoundedCapEquatorPowerLift m a s := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change (compactNeckLeftBoundaryCollarMap m
        (a, s, euclideanFourBallCollarZero)).1.1 =
      (roundedHemisphereClosedCapBoundaryCollar
        (s, euclideanFourBallCollarZero) : Sphere 4)
    simp only [compactNeckLeftBoundaryCollarMap,
      compactNeckLeftHalfParameter,
      coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_eq_raw,
      coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap,
      euclideanFourBallCollarZero_value,
      neg_zero, equatorUnlinkPowerCollarLift_zero, ne_eq,
      roundedHemisphereClosedCapBoundaryCollar_coe]
    rw [standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_equatorUnlinkPowerLift]
    change equatorSphereMap s =
      equatorCollarSphereMap
        (s, roundedHemisphereEquatorTime euclideanFourBallCollarZero)
    rw [show roundedHemisphereEquatorTime euclideanFourBallCollarZero =
        ⟨0, show (0 : ℝ) ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) by norm_num⟩ by
      apply Subtype.ext
      simp]
    exact (equatorCollarSphereMap_zero s).symm
  · apply Subtype.ext
    change (compactNeckLeftBoundaryCollarMap m
        (a, s, euclideanFourBallCollarZero)).1.2.1 =
      equatorUnlinkPowerRootTranslate m
        (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) s
    simp only [compactNeckLeftBoundaryCollarMap,
      compactNeckLeftHalfParameter,
      coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_eq_raw,
      coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap,
      euclideanFourBallCollarZero_value,
      neg_zero, equatorUnlinkPowerCollarLift_zero, ne_eq]
    rw [standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_equatorUnlinkPowerLift]
    exact equatorUnlinkClosedTubeExteriorPowerLift_powerCoordinate
      m (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) s

private theorem roundedCapPowerTrivializationHomeomorph_symm_equatorLift
    (a : ZMod m) (s : Sphere 3) :
    (coordinateExteriorRoundedCapPowerTrivializationHomeomorph m).symm
        (coordinateExteriorRoundedCapEquatorPowerLift m a s) =
      (a, roundedHemisphereClosedCapBoundaryCollar
        (s, euclideanFourBallCollarZero)) := by
  apply (coordinateExteriorRoundedCapPowerTrivializationHomeomorph m).injective
  rw [(coordinateExteriorRoundedCapPowerTrivializationHomeomorph m).apply_symm_apply]
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact (coordinateExteriorRoundedCapPowerRootTranslate_boundary m a s).symm

private theorem leftCapping_attaching
    (p : ZMod m × Sphere 3) :
    leftCappingBodyContinuousMap m
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m p) =
      leftCappingCapContinuousMap m
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m p) := by
  apply Prod.ext
  · change compactNeckLeftCutLabel m
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m p) = p.1
    unfold compactNeckLeftCutLabel
    rw [leftCapping_attaching_corestriction,
      roundedCapPowerTrivializationHomeomorph_symm_equatorLift]
  · apply Subtype.ext
    change coordinateThreeReflectionSphere
        (compactNeckLeftBoundaryCollarMap m
          (p.1, p.2, euclideanFourBallCollarZero)).1.1 =
      (euclideanFourBallRoundedHemisphereDiffeomorph
        (coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar
          (p.2, euclideanFourBallCollarZero)) :
            CollaredCutSide coordinateClosedCapZero)
    rw [euclideanFourBallRoundedHemisphereDiffeomorph_boundaryZero_coe]
    have hround : (compactNeckLeftBoundaryCollarMap m
          (p.1, p.2, euclideanFourBallCollarZero)).1.1 =
        (roundedHemisphereClosedCapBoundaryCollar
          (p.2, euclideanFourBallCollarZero) : Sphere 4) := by
      simp only [compactNeckLeftBoundaryCollarMap,
        compactNeckLeftHalfParameter,
        coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_eq_raw,
        coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap,
        euclideanFourBallCollarZero_value,
        neg_zero, equatorUnlinkPowerCollarLift_zero, ne_eq,
        roundedHemisphereClosedCapBoundaryCollar_coe]
      rw [standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_equatorUnlinkPowerLift]
      change equatorSphereMap p.2 =
        equatorCollarSphereMap
          (p.2, roundedHemisphereEquatorTime euclideanFourBallCollarZero)
      rw [show roundedHemisphereEquatorTime euclideanFourBallCollarZero =
          ⟨0, show (0 : ℝ) ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) by norm_num⟩ by
        apply Subtype.ext
        simp]
      exact (equatorCollarSphereMap_zero p.2).symm
    rw [hround]
    have hroundEquator :
        (roundedHemisphereClosedCapBoundaryCollar
          (p.2, euclideanFourBallCollarZero) : Sphere 4) =
            equatorSphereMap p.2 := by
      rw [← euclideanFourBallRoundedHemisphereDiffeomorph_boundaryCollar]
      exact euclideanFourBallRoundedHemisphereDiffeomorph_boundaryZero_coe p.2
    rw [hroundEquator]
    exact coordinateThreeReflectionSphere_of_mem_equator _
      (by
        rw [← range_equatorSphereMap]
        exact ⟨p.2, rfl⟩)

private theorem coordinateThreeReflectionSphere_mem_coordinateClosedCapZero_of_nonnegative
    (q : Sphere 4) (hq : 0 ≤ q.1 3) :
    coordinateThreeReflectionSphere q ∈ coordinateClosedCapZero := by
  change ¬0 < (coordinateThreeReflectionSphere q).1 3
  rw [coordinateThreeReflectionSphere_coord_three]
  exact not_lt_of_ge (neg_nonpos.mpr hq)

private theorem coordinateThreeReflectionSphere_mem_coordinateUnlinkExterior_of_nonnegative
    (q : CoordinateExteriorRightTubeClosed) (hq : 0 ≤ q.1.1 3) :
    coordinateThreeReflectionSphere q.1 ∈ coordinateUnlinkExterior (1 / 8 : ℝ) := by
  rw [coordinateUnlinkExterior, mem_compl_iff]
  rintro (hleft | hright)
  · have htarget : q.1 ∈ standardUnlinkOpenTube 1 (1 / 8 : ℝ) :=
      (coordinateThreeReflectionSphere_mem_openTube_zero_iff
        q.1 (1 / 8 : ℝ)).mp hleft
    have hcarrier := q.2
    change q.1 ∈ coordinateExteriorRightTubeClosedCarrier at hcarrier
    rw [coordinateExteriorRightTubeClosedCarrier_eq_compl_openTube] at hcarrier
    exact hcarrier htarget
  · have hcap : coordinateThreeReflectionSphere q.1 ∈ coordinateClosedCapZero :=
      coordinateThreeReflectionSphere_mem_coordinateClosedCapZero_of_nonnegative q.1 hq
    have hcarrier := coordinateClosedCapZero_subset_rightTubeClosedCarrier hcap
    rw [coordinateExteriorRightTubeClosedCarrier_eq_compl_openTube] at hcarrier
    exact hcarrier hright

private def leftCappingTargetToCapOfNonpositive
    (z : ZMod m × CoordinateExteriorRightTubeClosed)
    (hz : z.2.1.1 3 ≤ 0) : ZMod m × EuclideanFourBall :=
  (z.1, euclideanFourBallRoundedHemisphereDiffeomorph.symm
    ⟨z.2.1, by
      change ¬0 < z.2.1.1 3
      exact not_lt_of_ge hz⟩)

omit [NeZero m] in
private theorem leftCappingCapMap_targetToCapOfNonpositive
    (z : ZMod m × CoordinateExteriorRightTubeClosed)
    (hz : z.2.1.1 3 ≤ 0) :
    leftCappingCapMap m (leftCappingTargetToCapOfNonpositive m z hz) = z := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change ((euclideanFourBallRoundedHemisphereDiffeomorph
      (euclideanFourBallRoundedHemisphereDiffeomorph.symm
        ⟨z.2.1, by
          change ¬0 < z.2.1.1 3
          exact not_lt_of_ge hz⟩) :
            CollaredCutSide coordinateClosedCapZero) : Sphere 4) = z.2.1
    exact congrArg (fun q : CollaredCutSide coordinateClosedCapZero ↦ (q : Sphere 4)) <|
      euclideanFourBallRoundedHemisphereDiffeomorph.apply_symm_apply
        ⟨z.2.1, by
          change ¬0 < z.2.1.1 3
          exact not_lt_of_ge hz⟩

private def leftCappingTargetReflectedRoundedCap
    (z : ZMod m × CoordinateExteriorRightTubeClosed)
    (hz : 0 ≤ z.2.1.1 3) : CollaredCutSide coordinateClosedCapZero :=
  ⟨coordinateThreeReflectionSphere z.2.1,
    coordinateThreeReflectionSphere_mem_coordinateClosedCapZero_of_nonnegative z.2.1 hz⟩

private def leftCappingTargetRoundedPowerPoint
    (z : ZMod m × CoordinateExteriorRightTubeClosed)
    (hz : 0 ≤ z.2.1.1 3) : CoordinateExteriorRoundedCapPowerPullback m :=
  coordinateExteriorRoundedCapPowerTrivializationHomeomorph m
    (z.1, leftCappingTargetReflectedRoundedCap m z hz)

private def leftCappingTargetToBodyOfNonnegative
    (z : ZMod m × CoordinateExteriorRightTubeClosed)
    (hz : 0 ≤ z.2.1.1 3) : CompactNeckLeftCut m := by
  let r := leftCappingTargetRoundedPowerPoint m z hz
  let base : ↑(coordinateUnlinkExterior (1 / 8 : ℝ)) :=
    ⟨coordinateThreeReflectionSphere z.2.1,
      coordinateThreeReflectionSphere_mem_coordinateUnlinkExterior_of_nonnegative z.2 hz⟩
  let total : CoordinateUnlinkExteriorEighthPowerPullback m :=
    ⟨(base, r.1.2), by
      apply Subtype.ext
      exact congrArg Subtype.val r.2⟩
  refine ⟨total, ?_⟩
  exact (Set.ext_iff.mp
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier_eq_preimage_compl_cap_one m)
      total).mpr (leftCappingTargetReflectedRoundedCap m z hz).2

private theorem compactNeckLeftCutToRoundedCapPowerPullback_targetToBodyOfNonnegative
    (z : ZMod m × CoordinateExteriorRightTubeClosed)
    (hz : 0 ≤ z.2.1.1 3) :
    compactNeckLeftCutToRoundedCapPowerPullback m
        (leftCappingTargetToBodyOfNonnegative m z hz) =
      leftCappingTargetRoundedPowerPoint m z hz := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · rfl

private theorem leftCappingBodyMap_targetToBodyOfNonnegative
    (z : ZMod m × CoordinateExteriorRightTubeClosed)
    (hz : 0 ≤ z.2.1.1 3) :
    leftCappingBodyMap m (leftCappingTargetToBodyOfNonnegative m z hz) = z := by
  apply Prod.ext
  · change ((coordinateExteriorRoundedCapPowerTrivializationHomeomorph m).symm
        (compactNeckLeftCutToRoundedCapPowerPullback m
          (leftCappingTargetToBodyOfNonnegative m z hz))).1 = z.1
    rw [compactNeckLeftCutToRoundedCapPowerPullback_targetToBodyOfNonnegative,
      leftCappingTargetRoundedPowerPoint,
      (coordinateExteriorRoundedCapPowerTrivializationHomeomorph m).symm_apply_apply]
  · apply Subtype.ext
    exact coordinateThreeReflectionSphere_involutive z.2.1

private theorem leftCapping_cover :
    range (leftCappingBodyContinuousMap m) ∪
        range (leftCappingCapContinuousMap m) = univ := by
  rw [eq_univ_iff_forall]
  intro z
  by_cases hz : z.2.1.1 3 ≤ 0
  · exact Or.inr ⟨leftCappingTargetToCapOfNonpositive m z hz,
      leftCappingCapMap_targetToCapOfNonpositive m z hz⟩
  · have hz' : 0 ≤ z.2.1.1 3 := le_of_not_ge hz
    exact Or.inl ⟨leftCappingTargetToBodyOfNonnegative m z hz',
      leftCappingBodyMap_targetToBodyOfNonnegative m z hz'⟩

omit [NeZero m] in
private theorem exists_leftCapping_ball_attaching_of_cap_base_mem_equator
    (y : ZMod m × EuclideanFourBall)
    (hy : ((euclideanFourBallRoundedHemisphereDiffeomorph y.2 :
      CollaredCutSide coordinateClosedCapZero) : Sphere 4) ∈ coordinateEquator) :
    ∃ p : ZMod m × Sphere 3,
      coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m p = y := by
  have hyTargetBoundary : euclideanFourBallRoundedHemisphereDiffeomorph y.2 ∈
      coordinateUnlinkExteriorModel.boundary
        (CollaredCutSide coordinateClosedCapZero) := by
    rw [coordinateUnlinkExteriorRoundedHemisphereClosedCap_boundary]
    exact hy
  have hySourceBoundary : y.2 ∈
      coordinateUnlinkExteriorModel.boundary EuclideanFourBall :=
    ((euclideanFourBallRoundedHemisphereDiffeomorph.isLocalDiffeomorph y.2)
      |>.isBoundaryPoint_iff (by simp)).mpr hyTargetBoundary
  rw [coordinateUnlinkExteriorCommonModelEuclideanFourBall_boundary] at hySourceBoundary
  rw [← range_euclideanFourBallSmoothCollar_zero] at hySourceBoundary
  obtain ⟨s, hs⟩ := hySourceBoundary
  refine ⟨(y.1, s), ?_⟩
  apply Prod.ext
  · rfl
  · change coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar
        (s, euclideanFourBallCollarZero) = y.2
    rw [coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar_apply]
    exact hs

private theorem leftCapping_cross
    (x : CompactNeckLeftCut m) (y : ZMod m × EuclideanFourBall)
    (hxy : leftCappingBodyContinuousMap m x = leftCappingCapContinuousMap m y) :
    ∃ p : ZMod m × Sphere 3,
      coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m p = x ∧
        coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m p = y := by
  have hbase : coordinateThreeReflectionSphere x.1.1.1.1 =
      (euclideanFourBallRoundedHemisphereDiffeomorph y.2 :
        CollaredCutSide coordinateClosedCapZero) :=
    congrArg (fun z : ZMod m × CoordinateExteriorRightTubeClosed ↦
      (z.2.1 : Sphere 4)) hxy
  have hxCap : x.1.1.1.1 ∈ coordinateClosedCapZero :=
    compactNeckLeftCut_mem_coordinateClosedCapZero m x
  have hxNonpositive : x.1.1.1.1.1 3 ≤ 0 := by
    change ¬0 < x.1.1.1.1.1 3 at hxCap
    exact le_of_not_gt hxCap
  have hreflectNonnegative :
      0 ≤ (coordinateThreeReflectionSphere x.1.1.1.1).1 3 := by
    rw [coordinateThreeReflectionSphere_coord_three]
    exact neg_nonneg.mpr hxNonpositive
  have hyNonpositive :
      ((euclideanFourBallRoundedHemisphereDiffeomorph y.2 :
        CollaredCutSide coordinateClosedCapZero) : Sphere 4).1 3 ≤ 0 := by
    have hyCap := (euclideanFourBallRoundedHemisphereDiffeomorph y.2).2
    change ¬0 < ((euclideanFourBallRoundedHemisphereDiffeomorph y.2 :
      CollaredCutSide coordinateClosedCapZero) : Sphere 4).1 3 at hyCap
    exact le_of_not_gt hyCap
  have hyEquator : ((euclideanFourBallRoundedHemisphereDiffeomorph y.2 :
      CollaredCutSide coordinateClosedCapZero) : Sphere 4) ∈ coordinateEquator := by
    change ((euclideanFourBallRoundedHemisphereDiffeomorph y.2 :
      CollaredCutSide coordinateClosedCapZero) : Sphere 4).1 3 = 0
    apply le_antisymm hyNonpositive
    rw [← hbase]
    exact hreflectNonnegative
  obtain ⟨p, hp⟩ :=
    exists_leftCapping_ball_attaching_of_cap_base_mem_equator m y hyEquator
  refine ⟨p, ?_, hp⟩
  apply leftCappingBodyMap_injective m
  calc
    leftCappingBodyMap m
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m p) =
        leftCappingCapMap m
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m p) :=
      leftCapping_attaching m p
    _ = leftCappingCapMap m y := congrArg (leftCappingCapMap m) hp
    _ = leftCappingBodyMap m x := hxy.symm

private theorem compactSpace_compactNeckLeftCut :
    CompactSpace (CompactNeckLeftCut m) := by
  let _ : CompactSpace (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    compactSpace_coordinateUnlinkExteriorEighthPowerPullback m
  exact isCompact_iff_compactSpace.mp
    (isClosed_coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m).isCompact

private def leftCappingRightTubeFamilyHomeomorph :
    CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m ≃ₜ
      ZMod m × CoordinateExteriorRightTubeClosed := by
  let _ : CompactSpace (CompactNeckLeftCut m) :=
    compactSpace_compactNeckLeftCut m
  exact topologicalPushoutHomeomorph
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (leftCappingBodyContinuousMap m)
    (leftCappingCapContinuousMap m)
    (leftCapping_attaching m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m).injective
    (leftCappingBodyMap_injective m)
    (leftCappingCapMap_injective m)
    (leftCapping_cross m)
    (leftCapping_cover m)

private theorem leftCappingRightTubeFamilyHomeomorph_inl
    (x : CompactNeckLeftCut m) :
    leftCappingRightTubeFamilyHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x) =
      leftCappingBodyMap m x := by
  let _ : CompactSpace (CompactNeckLeftCut m) :=
    compactSpace_compactNeckLeftCut m
  change leftCappingRightTubeFamilyHomeomorph m _ =
    (leftCappingBodyContinuousMap m) x
  simpa [leftCappingRightTubeFamilyHomeomorph] using
    topologicalPushoutHomeomorph_inl
      (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
      (leftCappingBodyContinuousMap m)
      (leftCappingCapContinuousMap m)
      (leftCapping_attaching m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m).injective
      (leftCappingBodyMap_injective m)
      (leftCappingCapMap_injective m)
      (leftCapping_cross m)
      (leftCapping_cover m) x

private theorem leftCappingRightTubeFamilyHomeomorph_inr
    (y : ZMod m × EuclideanFourBall) :
    leftCappingRightTubeFamilyHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) y) =
      leftCappingCapMap m y := by
  let _ : CompactSpace (CompactNeckLeftCut m) :=
    compactSpace_compactNeckLeftCut m
  change leftCappingRightTubeFamilyHomeomorph m _ =
    (leftCappingCapContinuousMap m) y
  simpa [leftCappingRightTubeFamilyHomeomorph] using
    topologicalPushoutHomeomorph_inr
      (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
      (leftCappingBodyContinuousMap m)
      (leftCappingCapContinuousMap m)
      (leftCapping_attaching m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m).injective
      (leftCappingBodyMap_injective m)
      (leftCappingCapMap_injective m)
      (leftCapping_cross m)
      (leftCapping_cover m) y

private theorem leftCapping_isLocalDiffeomorphAt_congr_of_eqOn_open
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace CoordinateUnlinkExteriorModelSpace M]
    [ChartedSpace CoordinateUnlinkExteriorModelSpace N]
    {f g : M → N} {x : M}
    (hg : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ g x)
    (W : Set M) (hWopen : IsOpen W) (hxW : x ∈ W)
    (hfg : EqOn f g W) :
    IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ f x := by
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp <|
    hg.contMDiffAt.continuousAt.preimage_mem_nhds <|
      hg.localInverse.open_source.mem_nhds hg.localInverse_mem_source
  let Ψ := hg.localInverse.symm
  let U := W ∩ V
  have hU : IsOpen U := hWopen.inter hVopen
  let q := Ψ.toOpenPartialHomeomorph.restrOpen U hU
  have hEq : EqOn f q q.source := by
    intro y hy
    change y ∈ Ψ.source ∩ U at hy
    have hyTarget : y ∈ hg.localInverse.target := hy.1
    have hgySource : g y ∈ hg.localInverse.source := hVsub hy.2.2
    apply (hfg hy.2.1).trans
    change g y = hg.localInverse.symm y
    calc
      g y = hg.localInverse.symm (hg.localInverse (g y)) :=
        (hg.localInverse.left_inv hgySource).symm
      _ = hg.localInverse.symm y :=
        congrArg hg.localInverse.symm (hg.localInverse_left_inv hyTarget)
  let Φ : PartialDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel M N ∞ :=
    { toPartialEquiv :=
        { toFun := f
          invFun := q.toPartialEquiv.invFun
          source := q.source
          target := q.target
          map_source' := by
            intro y hy
            rw [hEq hy]
            exact q.map_source hy
          map_target' := by
            intro y hy
            exact q.map_target hy
          left_inv' := by
            intro y hy
            rw [hEq hy]
            exact q.left_inv hy
          right_inv' := by
            intro y hy
            exact (hEq (q.toPartialEquiv.map_target hy)).trans
              (q.toPartialEquiv.right_inv hy) }
      open_source := q.open_source
      open_target := q.open_target
      contMDiffOn_toFun := by
        apply (Ψ.contMDiffOn_toFun.mono ?_).congr hEq
        intro y hy
        change y ∈ Ψ.source ∩ U at hy
        exact hy.1
      contMDiffOn_invFun := by
        apply Ψ.contMDiffOn_invFun.mono
        intro y hy
        change y ∈ Ψ.target ∩ Ψ.symm ⁻¹' U at hy
        exact hy.1 }
  apply Φ.isLocalDiffeomorphAt
  change x ∈ Ψ.source ∩ U
  exact ⟨hg.localInverse_mem_target, hxW, hxV⟩

private theorem leftCapping_isLocalDiffeomorphAt_congr_of_eventuallyEq
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace CoordinateUnlinkExteriorModelSpace M]
    [ChartedSpace CoordinateUnlinkExteriorModelSpace N]
    {f g : M → N} {x : M}
    (hg : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ g x)
    (heq : f =ᶠ[nhds x] g) :
    IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ f x := by
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp heq
  exact leftCapping_isLocalDiffeomorphAt_congr_of_eqOn_open hg W hWopen hxW
    (fun y hy ↦ hWsub hy)

private theorem leftCapping_reflect_isLocalDiffeomorph
    {M N P : Type} [TopologicalSpace M] [TopologicalSpace N]
    [TopologicalSpace P]
    [ChartedSpace CoordinateUnlinkExteriorModelSpace M]
    [ChartedSpace CoordinateUnlinkExteriorModelSpace N]
    [ChartedSpace CoordinateUnlinkExteriorModelSpace P]
    (p : N → P) (f : M → N)
    (hp : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ p)
    (hf : Continuous f)
    (hpf : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (p ∘ f)) :
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ f := by
  intro x
  let hpx := hp (f x)
  have hinv : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (fun y ↦ hpx.localInverse y) (p (f x)) :=
    hpx.localInverse_isLocalDiffeomorphAt
  have hcomp : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (hpx.localInverse ∘ (p ∘ f)) x :=
    (hpf x).comp (g := fun y ↦ hpx.localInverse y)
      coordinateUnlinkExteriorModel N hinv
  apply leftCapping_isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp
  filter_upwards [hpx.localInverse_eventuallyEq_left.comp_tendsto
    hf.continuousAt] with y hy
  simpa only [Function.comp_apply, id_eq] using hy.symm

private def leftCappingPartialDiffeomorphOfAtlas
    {X H E : Type*} [TopologicalSpace X] [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace H X] (I : ModelWithCorners ℝ E H)
    (e : OpenPartialHomeomorph X H)
    (he : e ∈ IsManifold.maximalAtlas I ∞ X) :
    PartialDiffeomorph I I X H ∞ where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he

private theorem
    isLocalDiffeomorph_coordinateUnlinkExteriorEighthCollarToExterior_leftCapping
    (i : Fin 2) :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorEighthCollarToExterior i) := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  intro p
  let sourceChart : PartialDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel CoordinateUnlinkExteriorEighthCollarDomain
      CoordinateUnlinkExteriorModelSpace ∞ :=
    leftCappingPartialDiffeomorphOfAtlas coordinateUnlinkExteriorModel
      (chartAt CoordinateUnlinkExteriorModelSpace p)
      (IsManifold.chart_mem_maximalAtlas p)
  let targetOpenChart := coordinateUnlinkExteriorEighthCollarChart i p
  have htargetAtlas : targetOpenChart ∈
      atlas CoordinateUnlinkExteriorModelSpace CoordinateUnlinkExteriorEighth :=
    Or.inr ⟨i, p, rfl⟩
  have htargetMax : targetOpenChart ∈
      IsManifold.maximalAtlas coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
    StructureGroupoid.subset_maximalAtlas
      (contDiffGroupoid ∞ coordinateUnlinkExteriorModel) htargetAtlas
  let targetChart : PartialDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel CoordinateUnlinkExteriorEighth
      CoordinateUnlinkExteriorModelSpace ∞ :=
    leftCappingPartialDiffeomorphOfAtlas coordinateUnlinkExteriorModel
      targetOpenChart htargetMax
  let phi := sourceChart.trans targetChart.symm
  refine ⟨phi, ?_, ?_⟩
  · change p ∈ sourceChart.source ∩
      sourceChart ⁻¹' targetChart.symm.source
    refine ⟨mem_chart_source CoordinateUnlinkExteriorModelSpace p, ?_⟩
    change (chartAt CoordinateUnlinkExteriorModelSpace p) p ∈
      targetOpenChart.target
    change (chartAt CoordinateUnlinkExteriorModelSpace p) p ∈
      (chartAt CoordinateUnlinkExteriorModelSpace p).target
    exact (chartAt CoordinateUnlinkExteriorModelSpace p).map_source
      (mem_chart_source CoordinateUnlinkExteriorModelSpace p)
  · intro q hq
    change coordinateUnlinkExteriorEighthCollarToExterior i q =
      targetOpenChart.symm ((chartAt CoordinateUnlinkExteriorModelSpace p) q)
    rw [show targetOpenChart =
        (chartAt CoordinateUnlinkExteriorModelSpace p).lift_openEmbedding
          (isOpenEmbedding_coordinateUnlinkExteriorEighthCollarToExterior i) by rfl]
    simp only [OpenPartialHomeomorph.lift_openEmbedding_symm, comp_apply]
    rw [(chartAt CoordinateUnlinkExteriorModelSpace p).left_inv hq.1]

private theorem
    isLocalDiffeomorph_coordinateExteriorRightTubeStandardBoundaryCollar_leftCapping :
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      coordinateExteriorRightTubeStandardBoundaryCollar := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  apply isLocalDiffeomorph_collaredCutSideHalfCollarMap
    coordinateUnlinkExteriorModel ∞
    coordinateExteriorRightTubeClosedCarrier
    coordinateExteriorRightTubeBoundary
    isOpen_coordinateExteriorRightTubeClosed_offBoundary
  intro i j
  apply IsManifold.compatible_of_mem_maximalAtlas
  · apply IsManifold.subset_maximalAtlas
    exact ⟨i, rfl⟩
  · apply IsManifold.subset_maximalAtlas
    exact ⟨j, rfl⟩

private theorem isLocalDiffeomorph_coordinateExteriorRightTubeStandardOffMap_leftCapping :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (collaredCutSideOffBoundaryOpensMap
        coordinateExteriorRightTubeClosedCarrier
        coordinateExteriorRightTubeBoundary
        isOpen_coordinateExteriorRightTubeClosed_offBoundary) := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  apply isLocalDiffeomorph_collaredCutSideOffBoundaryMap
    coordinateUnlinkExteriorModel ∞
    coordinateExteriorRightTubeClosedCarrier
    coordinateExteriorRightTubeBoundary
    isOpen_coordinateExteriorRightTubeClosed_offBoundary
  intro i j
  apply IsManifold.compatible_of_mem_maximalAtlas
  · apply IsManifold.subset_maximalAtlas
    exact ⟨i, rfl⟩
  · apply IsManifold.subset_maximalAtlas
    exact ⟨j, rfl⟩

private theorem coordinateOpenCapZero_subset_rightClosedTubeExterior
    {q : Sphere 4} (hq : q ∈ coordinateOpenCap 0) :
    q ∉ standardUnlinkClosedTube 1 (1 / 8 : ℝ) := by
  rw [mem_coordinateOpenCap_zero] at hq
  intro hclosed
  change dist (standardUnlinkNormalProjection q)
      (standardUnlinkNormalCenter 1) ≤ 1 / 8 at hclosed
  rw [dist_eq_norm] at hclosed
  let v := standardUnlinkNormalProjection q - standardUnlinkNormalCenter 1
  have hsq : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    simpa [Fin.sum_univ_succ] using EuclideanSpace.real_norm_sq_eq v
  have hv0 : v 0 = q.1 3 - 1 / 2 := by
    simp [v, standardUnlinkHeight]
  have hv1sq : 0 ≤ v 1 ^ 2 := sq_nonneg _
  have hvnorm_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
  rw [hv0] at hsq
  nlinarith

private theorem
    isLocalDiffeomorphAt_leftCappingExteriorBaseReflectionToRightTube_standard
    (q : CoordinateUnlinkExteriorEighth)
    (hqCap : (q.1 : Sphere 4) ∈ coordinateOpenCap 0) :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      leftCappingExteriorBaseReflectionToRightTube q := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  by_cases hleft :
      ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 0‖ =
        (1 / 8 : ℝ)
  · let z : StandardUnlinkExteriorCollar 0 (1 / 8 : ℝ) (1 / 4 : ℝ) :=
      ⟨q.1, (mem_standardUnlinkExteriorCollarSet_iff 0
        (by norm_num) (by norm_num) q.1).2 ⟨hleft.ge, by
          rw [hleft]
          norm_num⟩⟩
    let p : CoordinateUnlinkExteriorEighthCollarDomain :=
      (standardUnlinkExteriorEighthCollarHomeomorph 0).symm z
    have hpq : coordinateUnlinkExteriorEighthCollarToExterior 0 p = q := by
      apply Subtype.ext
      change (standardUnlinkExteriorEighthCollarHomeomorph 0 p).1 = q.1
      simpa only [p, z] using congrArg Subtype.val
        ((standardUnlinkExteriorEighthCollarHomeomorph 0).apply_symm_apply z)
    have hc : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        (coordinateUnlinkExteriorEighthCollarToExterior 0) :=
      isLocalDiffeomorph_coordinateUnlinkExteriorEighthCollarToExterior_leftCapping 0
    have hparam : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        coordinateZeroReflectionExteriorCollarDiffeomorph :=
      coordinateZeroReflectionExteriorCollarDiffeomorph.isLocalDiffeomorph
    have ht : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        coordinateExteriorRightTubeStandardBoundaryCollar :=
      isLocalDiffeomorph_coordinateExteriorRightTubeStandardBoundaryCollar_leftCapping
    have htarget : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        (coordinateExteriorRightTubeStandardBoundaryCollar ∘
          coordinateZeroReflectionExteriorCollarDiffeomorph) := by
      intro x
      exact (hparam x).comp coordinateUnlinkExteriorModel
        CoordinateExteriorRightTubeClosed (ht _)
    have hcomp : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        (leftCappingExteriorBaseReflectionToRightTube ∘
          coordinateUnlinkExteriorEighthCollarToExterior 0) := by
      intro x
      apply leftCapping_isLocalDiffeomorphAt_congr_of_eqOn_open
        (htarget x) univ isOpen_univ (mem_univ x)
      intro y _
      exact leftCappingExteriorBaseReflectionToRightTube_comp_leftCollar y
    have h := isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
      coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
      leftCappingExteriorBaseReflectionToRightTube
      (coordinateUnlinkExteriorEighthCollarToExterior 0) hc hcomp p
    rwa [hpq] at h
  · have hleftGt : (1 / 8 : ℝ) <
        ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 0‖ := by
      have hnotOpen := q.2
      change q.1 ∉ standardUnlinkOpenTubes (1 / 8 : ℝ) at hnotOpen
      have hge : (1 / 8 : ℝ) ≤
          ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 0‖ := by
        apply le_of_not_gt
        intro hlt
        apply hnotOpen
        exact Or.inl (by
          change dist (standardUnlinkNormalProjection q.1)
            (standardUnlinkNormalCenter 0) < 1 / 8
          simpa only [dist_eq_norm] using hlt)
      exact lt_of_le_of_ne hge (Ne.symm hleft)
    have hrightGt : (1 / 8 : ℝ) <
        ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1‖ := by
      have hnot := coordinateOpenCapZero_subset_rightClosedTubeExterior hqCap
      change q.1 ∉ standardUnlinkClosedTube 1 (1 / 8 : ℝ) at hnot
      change ¬ dist (standardUnlinkNormalProjection q.1)
        (standardUnlinkNormalCenter 1) ≤ 1 / 8 at hnot
      rw [dist_eq_norm] at hnot
      exact lt_of_not_ge hnot
    have hqInterior : q ∈ coordinateUnlinkExteriorEighthInteriorOpens :=
      (mem_coordinateUnlinkExteriorEighthInteriorOpens_iff q).2 (by
        intro i
        fin_cases i
        · exact hleftGt
        · exact hrightGt)
    let U := coordinateUnlinkExteriorEighthInteriorOpens
    let V := collaredCutSideOffBoundaryOpens
      coordinateExteriorRightTubeClosedCarrier
      coordinateExteriorRightTubeBoundary
      isOpen_coordinateExteriorRightTubeClosed_offBoundary
    let c : U → CoordinateUnlinkExteriorEighth := Subtype.val
    have hmem (x : U) :
        (leftCappingExteriorBaseReflectionToRightTube x.1).1 ∈ V := by
      change coordinateThreeReflectionSphere x.1.1 ∈
        collaredCutSideOffBoundary coordinateExteriorRightTubeClosedCarrier
          coordinateExteriorRightTubeBoundary
      rw [coordinateExteriorRightTubeClosed_offBoundary]
      change ¬ dist
        (standardUnlinkNormalProjection (coordinateThreeReflectionSphere x.1.1))
          (standardUnlinkNormalCenter 1) ≤ 1 / 8
      rw [dist_eq_norm, norm_coordinateThreeReflectionSphere_sub_center_one]
      exact not_le.mpr
        ((mem_coordinateUnlinkExteriorEighthInteriorOpens_iff x.1).mp x.2 0)
    let r : U → V := fun x ↦
      ⟨leftCappingExteriorBaseReflectionToRightTube x.1, hmem x⟩
    let d : V → CoordinateExteriorRightTubeClosed :=
      collaredCutSideOffBoundaryOpensMap
        coordinateExteriorRightTubeClosedCarrier
        coordinateExteriorRightTubeBoundary
        isOpen_coordinateExteriorRightTubeClosed_offBoundary
    have hc : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞ c :=
      isLocalDiffeomorph_opensSubtypeVal
        coordinateUnlinkExteriorModel coordinateUnlinkExteriorEighthInteriorOpens
    have hd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞ d :=
      isLocalDiffeomorph_coordinateExteriorRightTubeStandardOffMap_leftCapping
    have hrContinuous : Continuous r := by
      have hreflect : Continuous
          (fun x : U ↦ coordinateThreeReflectionSphere x.1.1) :=
        coordinateThreeReflectionSphereHomeomorph.continuous.comp
          (continuous_subtype_val.comp continuous_subtype_val)
      simpa only [r, leftCappingExteriorBaseReflectionToRightTube] using
        (Continuous.subtype_mk hreflect _)
    have hprojV : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        (Subtype.val : V → Sphere 4) :=
      isLocalDiffeomorph_opensSubtypeVal coordinateUnlinkExteriorModel V
    have hprojR : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        ((Subtype.val : V → Sphere 4) ∘ r) := by
      intro x
      have hOne := coordinateUnlinkExteriorEighthInteriorSphereDiffeomorph
        |>.isLocalDiffeomorph x
      have hTwo := isLocalDiffeomorph_opensSubtypeVal
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        standardUnlinkClosedTubeExteriorOpens
        (coordinateUnlinkExteriorEighthInteriorSphereDiffeomorph x)
      have hThree :=
        standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph
          |>.isLocalDiffeomorph
            ((coordinateUnlinkExteriorEighthInteriorSphereDiffeomorph x :
              StandardUnlinkClosedTubeExterior) : Sphere 4)
      have hFour := coordinateThreeReflectionSphereCommonDiffeomorph
        |>.isLocalDiffeomorph x.1.1
      have hOneTwo := hOne.comp
        (g := (Subtype.val : StandardUnlinkClosedTubeExterior → Sphere 4))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (Sphere 4) hTwo
      have hOneTwoThree := hOneTwo.comp
        (g := standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph)
        coordinateUnlinkExteriorModel (Sphere 4) hThree
      have hcomp := hOneTwoThree.comp
        (g := coordinateThreeReflectionSphereCommonDiffeomorph)
        coordinateUnlinkExteriorModel (Sphere 4) hFour
      apply leftCapping_isLocalDiffeomorphAt_congr_of_eqOn_open hcomp
        univ isOpen_univ (mem_univ x)
      intro y _
      change coordinateThreeReflectionSphere y.1.1 =
        coordinateThreeReflectionSphereCommonDiffeomorph y.1.1
      exact (coordinateThreeReflectionSphereCommonDiffeomorph_apply y.1.1).symm
    have hr : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞ r :=
      leftCapping_reflect_isLocalDiffeomorph
        (Subtype.val : V → Sphere 4) r hprojV hrContinuous hprojR
    have hrightMap : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞ (d ∘ r) := by
      intro x
      exact (hr x).comp coordinateUnlinkExteriorModel
        CoordinateExteriorRightTubeClosed (hd (r x))
    have hcomp : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        (leftCappingExteriorBaseReflectionToRightTube ∘ c) := by
      intro x
      apply leftCapping_isLocalDiffeomorphAt_congr_of_eqOn_open
        (hrightMap x) univ isOpen_univ (mem_univ x)
      intro y _
      apply Subtype.ext
      rfl
    let p : U := ⟨q, hqInterior⟩
    have h := isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
      coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
      leftCappingExteriorBaseReflectionToRightTube c hc hcomp p
    simpa only [c] using h

private def leftCappingCutBaseMap (q : CompactNeckLeftCut m) :
    CoordinateExteriorRightTubeClosed :=
  leftCappingExteriorBaseReflectionToRightTube
    (coordinateUnlinkExteriorEighthPowerPullbackProj m q.1)

private theorem leftCappingCutBaseMap_eq_bodyMap_snd
    (q : CompactNeckLeftCut m) :
    leftCappingCutBaseMap m q = (leftCappingBodyMap m q).2 := by
  rfl

private theorem isLocalDiffeomorph_compactNeckLeftCutOffMap :
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (collaredCutSideOffBoundaryOpensMap
        (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
        (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
        (isOpen_compactNeckLeftCut_offBoundary m)) := by
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := compactNeckLeftCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckLeftCut m) :=
    isManifold_compactNeckLeftCut m
  apply isLocalDiffeomorph_collaredCutSideOffBoundaryMap
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckLeftCut_offBoundary m)
  intro i j
  apply IsManifold.compatible_of_mem_maximalAtlas
  · apply IsManifold.subset_maximalAtlas
    exact ⟨i, rfl⟩
  · apply IsManifold.subset_maximalAtlas
    exact ⟨j, rfl⟩

private theorem isLocalDiffeomorphAt_leftCappingCutBaseMap_of_offBoundary_standard
    (q : CompactNeckLeftCut m)
    (hq : q.1 ∈ collaredCutSideOffBoundary
      (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)) :
    letI := compactNeckLeftCutChartedSpace m
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (leftCappingCutBaseMap m) q := by
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
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := compactNeckLeftCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckLeftCut m) :=
    isManifold_compactNeckLeftCut m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  let U := collaredCutSideOffBoundaryOpens
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckLeftCut_offBoundary m)
  let c : U → CompactNeckLeftCut m :=
    collaredCutSideOffBoundaryOpensMap
      (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
      (isOpen_compactNeckLeftCut_offBoundary m)
  have hc : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ c :=
    isLocalDiffeomorph_compactNeckLeftCutOffMap m
  have hproj : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorEighthPowerPullbackProj m) :=
    isLocalDiffeomorph_coordinateUnlinkExteriorEighthPowerPullbackProj m
  have hbase : ∀ x : U, IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      leftCappingExteriorBaseReflectionToRightTube
      (coordinateUnlinkExteriorEighthPowerPullbackProj m x.1) := by
    intro x
    apply isLocalDiffeomorphAt_leftCappingExteriorBaseReflectionToRightTube_standard
    have hx := x.2
    change x.1 ∈ collaredCutSideOffBoundary
      (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) at hx
    rcases hx with ⟨hxCarrier, hxNotSeam⟩
    have hnonpositive :
        (coordinateUnlinkExteriorEighthPowerPullbackProj m x.1 : Sphere 4).1 3 ≤ 0 := by
      rw [coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier_eq_preimage_compl_cap_one]
        at hxCarrier
      change (coordinateUnlinkExteriorEighthPowerPullbackProj m x.1 : Sphere 4) ∉
        coordinateOpenCap 1 at hxCarrier
      rw [mem_coordinateOpenCap_one] at hxCarrier
      exact le_of_not_gt hxCarrier
    have hnonzero :
        (coordinateUnlinkExteriorEighthPowerPullbackProj m x.1 : Sphere 4).1 3 ≠ 0 := by
      intro hzero
      apply hxNotSeam
      rw [coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_preimage_coordinateEquator]
      exact hzero
    rw [mem_coordinateOpenCap_zero]
    exact lt_of_le_of_ne hnonpositive hnonzero
  have hcomp : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (leftCappingCutBaseMap m ∘ c) := by
    intro x
    have hsub := isLocalDiffeomorph_opensSubtypeVal
      coordinateUnlinkExteriorModel U x
    have hsubproj : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        (coordinateUnlinkExteriorEighthPowerPullbackProj m ∘
          (Subtype.val : U → CoordinateUnlinkExteriorEighthPowerPullback m)) x :=
      hsub.comp (g := coordinateUnlinkExteriorEighthPowerPullbackProj m)
        coordinateUnlinkExteriorModel CoordinateUnlinkExteriorEighth (hproj x.1)
    have h : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        (leftCappingExteriorBaseReflectionToRightTube ∘
          coordinateUnlinkExteriorEighthPowerPullbackProj m ∘
          (Subtype.val : U → CoordinateUnlinkExteriorEighthPowerPullback m)) x :=
      hsubproj.comp (g := leftCappingExteriorBaseReflectionToRightTube)
        coordinateUnlinkExteriorModel CoordinateExteriorRightTubeClosed (hbase x)
    apply leftCapping_isLocalDiffeomorphAt_congr_of_eqOn_open h
      univ isOpen_univ (mem_univ x)
    intro y _
    rfl
  let p : U := ⟨q.1, hq⟩
  have hp := isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    (leftCappingCutBaseMap m) c hc hcomp p
  simpa only [c, collaredCutSideOffBoundaryOpensMap] using hp

private theorem leftCapping_capOffSeam_base_eq_rightCapping
    (x : ↑(topologicalPushoutInrOffSeamOpens
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m))) :
    Prod.snd
        (leftCappingRightTubeFamilyHomeomorph m
          (topologicalPushoutInrOffSeamMap'
            (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
            (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
            (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap
              m) x)) =
      coordinateExteriorRightTubePowerPullbackProj m
        (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m
          (topologicalPushoutInrOffSeamMap'
            (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
            (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
            (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap
              m) x)) := by
  simp only [topologicalPushoutInrOffSeamMap',
    leftCappingRightTubeFamilyHomeomorph_inr,
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph_inr]
  apply Subtype.ext
  rfl

private theorem isLocalDiffeomorph_leftCapping_capOffSeam :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    letI := coordinateExteriorRightTubeStandardChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (leftCappingRightTubeFamilyHomeomorph m ∘
        topologicalPushoutInrOffSeamMap'
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
          (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap
            m)) := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × CoordinateExteriorRightTubeClosed) :=
    isManifold_discreteProductChartedSpace coordinateUnlinkExteriorModel ∞
      (ZMod m) CoordinateExteriorRightTubeClosed
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let F := leftCappingRightTubeFamilyHomeomorph m ∘
    topologicalPushoutInrOffSeamMap'
      (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
  have hF : Continuous F :=
    (leftCappingRightTubeFamilyHomeomorph m).continuous.comp
      (isOpenEmbedding_topologicalPushoutInrOffSeamMap'
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        |>.continuous)
  have hsnd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × CoordinateExteriorRightTubeClosed →
        CoordinateExteriorRightTubeClosed) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := CoordinateExteriorRightTubeClosed))
  apply leftCapping_reflect_isLocalDiffeomorph Prod.snd F hsnd hF
  have hright :=
    isLocalDiffeomorph_coordinateExteriorPlanarNeckRightSmoothCappingRightTube_capOffSeam m
  have hproj :=
    isLocalDiffeomorph_coordinateExteriorRightTubePowerPullbackProj_standard m
  intro x
  have hcomp := (hright x).comp
    (g := coordinateExteriorRightTubePowerPullbackProj m)
    coordinateUnlinkExteriorModel CoordinateExteriorRightTubeClosed
    (hproj _)
  apply leftCapping_isLocalDiffeomorphAt_congr_of_eqOn_open hcomp univ
    isOpen_univ (mem_univ x)
  intro y _
  exact leftCapping_capOffSeam_base_eq_rightCapping m y

private theorem isLocalDiffeomorph_leftCapping_cutOffSeam :
    letI := compactNeckLeftCutChartedSpace m
    letI := coordinateExteriorRightTubeStandardChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (leftCappingRightTubeFamilyHomeomorph m ∘
        topologicalPushoutInlOffSeamMap'
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
          (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)) := by
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
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := compactNeckLeftCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckLeftCut m) :=
    isManifold_compactNeckLeftCut m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × CoordinateExteriorRightTubeClosed) :=
    isManifold_discreteProductChartedSpace coordinateUnlinkExteriorModel ∞
      (ZMod m) CoordinateExteriorRightTubeClosed
  let U := topologicalPushoutInlOffSeamOpens
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
  let F : U → ZMod m × CoordinateExteriorRightTubeClosed :=
    leftCappingRightTubeFamilyHomeomorph m ∘
      topologicalPushoutInlOffSeamMap'
      (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
  have hF : Continuous F :=
    (leftCappingRightTubeFamilyHomeomorph m).continuous.comp
      (isOpenEmbedding_topologicalPushoutInlOffSeamMap'
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        |>.continuous)
  have hsnd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × CoordinateExteriorRightTubeClosed →
        CoordinateExteriorRightTubeClosed) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := CoordinateExteriorRightTubeClosed))
  apply leftCapping_reflect_isLocalDiffeomorph Prod.snd F hsnd hF
  intro x
  have hxOff : x.1.1 ∈ collaredCutSideOffBoundary
      (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) := by
    refine ⟨x.1.2, ?_⟩
    have hx := x.2
    change x.1 ∉ range
      (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m) at hx
    rw [range_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap] at hx
    exact hx
  have hOne : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Subtype.val : U → CompactNeckLeftCut m) x :=
    isLocalDiffeomorph_opensSubtypeVal coordinateUnlinkExteriorModel U x
  have hTwo : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (leftCappingCutBaseMap m) x.1 :=
    isLocalDiffeomorphAt_leftCappingCutBaseMap_of_offBoundary_standard m x.1 hxOff
  have hcomp : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (leftCappingCutBaseMap m ∘ (Subtype.val : U → CompactNeckLeftCut m)) x :=
    hOne.comp (g := leftCappingCutBaseMap m) coordinateUnlinkExteriorModel
      CoordinateExteriorRightTubeClosed hTwo
  apply leftCapping_isLocalDiffeomorphAt_congr_of_eqOn_open hcomp
    univ isOpen_univ (mem_univ x)
  intro y _
  rw [Function.comp_apply]
  change Prod.snd
      (leftCappingRightTubeFamilyHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) y.1)) = _
  rw [leftCappingRightTubeFamilyHomeomorph_inl]
  exact (leftCappingCutBaseMap_eq_bodyMap_snd m y.1).symm

private theorem leftCapping_equatorCollarNeg_not_mem_closedTubes_quarter
    (p : Sphere 3 × EquatorCollarInterval)
    (hp : |(p.2.1 : ℝ)| < 1 / 8) :
    equatorCollarSphereMap
        (p.1, coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2) ∉
      standardUnlinkClosedTubes (1 / 4 : ℝ) := by
  intro h
  rcases h with h | h
  · have hle :
        ‖standardUnlinkNormalProjection
              (equatorCollarSphereMap
                (p.1,
                  coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2)) -
            standardUnlinkNormalCenter 0‖ ≤ 1 / 4 := by
      simpa only [standardUnlinkClosedTube, mem_preimage, mem_closedBall,
        dist_eq_norm] using h
    have hsq := EuclideanSpace.real_norm_sq_eq
      (standardUnlinkNormalProjection
          (equatorCollarSphereMap
            (p.1,
              coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2)) -
        standardUnlinkNormalCenter 0)
    have hsqle :
        ‖standardUnlinkNormalProjection
              (equatorCollarSphereMap
                (p.1,
                  coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2)) -
            standardUnlinkNormalCenter 0‖ ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by norm_num)).2 hle
    have hpt : -(1 / 8 : ℝ) < p.2.1 ∧ p.2.1 < 1 / 8 := abs_lt.mp hp
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsq
    simp [standardUnlinkNormalProjection, standardUnlinkNormalCenter,
      standardUnlinkHeight,
      coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph,
      equatorCollarSphereMap, equatorCollarAmbientMap] at hsq hsqle
    nlinarith [sq_nonneg
      (equatorCollarScale (-(p.2.1 : ℝ)) * p.1.1 3),
      norm_nonneg
        (standardUnlinkNormalProjection
          (equatorCollarSphereMap
            (p.1,
              coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2)) -
        standardUnlinkNormalCenter 0)]
  · have hle :
        ‖standardUnlinkNormalProjection
              (equatorCollarSphereMap
                (p.1,
                  coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2)) -
            standardUnlinkNormalCenter 1‖ ≤ 1 / 4 := by
      simpa only [standardUnlinkClosedTube, mem_preimage, mem_closedBall,
        dist_eq_norm] using h
    have hsq := EuclideanSpace.real_norm_sq_eq
      (standardUnlinkNormalProjection
          (equatorCollarSphereMap
            (p.1,
              coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2)) -
        standardUnlinkNormalCenter 1)
    have hsqle :
        ‖standardUnlinkNormalProjection
              (equatorCollarSphereMap
                (p.1,
                  coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2)) -
            standardUnlinkNormalCenter 1‖ ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by norm_num)).2 hle
    have hpt : -(1 / 8 : ℝ) < p.2.1 ∧ p.2.1 < 1 / 8 := abs_lt.mp hp
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsq
    simp [standardUnlinkNormalProjection, standardUnlinkNormalCenter,
      standardUnlinkHeight,
      coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph,
      equatorCollarSphereMap, equatorCollarAmbientMap] at hsq hsqle
    nlinarith [sq_nonneg
      (equatorCollarScale (-(p.2.1 : ℝ)) * p.1.1 3),
      norm_nonneg
        (standardUnlinkNormalProjection
          (equatorCollarSphereMap
            (p.1,
              coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2)) -
        standardUnlinkNormalCenter 1)]

private def leftCappingSeamTargetBase
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :
    CoordinateExteriorRightTubeClosed :=
  Prod.snd (leftCappingRightTubeFamilyHomeomorph m
    (coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m p))

private def rightCappingProjectedSeamTargetBase
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :
    CoordinateExteriorRightTubeClosed :=
  coordinateExteriorRightTubePowerPullbackProj m
    (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m
      (coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m p))

private theorem isLocalDiffeomorph_rightCappingProjectedSeamTargetBase :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (rightCappingProjectedSeamTargetBase m) := by
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    isManifold_signedSeamFamilyCommonModel m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullbackStandard m
  have hseam :=
    isLocalDiffeomorph_coordinateExteriorPlanarNeckRightSmoothCappingRightTube_seam m
  have hproj :=
    isLocalDiffeomorph_coordinateExteriorRightTubePowerPullbackProj_standard m
  intro p
  change IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
    coordinateUnlinkExteriorModel ∞
    (coordinateExteriorRightTubePowerPullbackProj m ∘
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m ∘
        coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m)) p
  exact (hseam p).comp
    (g := coordinateExteriorRightTubePowerPullbackProj m)
    coordinateUnlinkExteriorModel CoordinateExteriorRightTubeClosed (hproj _)

private theorem leftCappingSeamTargetBase_coe_of_positive
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : 0 < signedSeamTime m p) :
    (leftCappingSeamTargetBase m p : Sphere 4) =
      equatorCollarSphereMap
        (p.2.1,
          coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2.2) := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  rw [leftCappingSeamTargetBase,
    coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap_of_positive m p hp,
    leftCappingRightTubeFamilyHomeomorph_inr]
  change
    ((euclideanFourBallRoundedHemisphereDiffeomorph
      (euclideanFourBallSmoothCollar (signedSeamHalfReparam m p).2) :
        CollaredCutSide coordinateClosedCapZero) : Sphere 4) = _
  rw [← coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar_apply,
    euclideanFourBallRoundedHemisphereDiffeomorph_boundaryCollar,
    roundedHemisphereClosedCapBoundaryCollar_coe,
    roundedHemisphereClosedCapCollarAmbient]
  congr 2
  apply Subtype.ext
  change -|(p.2.2.1 : ℝ)| = -(p.2.2.1 : ℝ)
  change 0 < (p.2.2.1 : ℝ) at hp
  rw [abs_of_pos hp]

private theorem rightCappingProjectedSeamTargetBase_coe_of_positive
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : 0 < signedSeamTime m p) :
    (rightCappingProjectedSeamTargetBase m p : Sphere 4) =
      equatorCollarSphereMap
        (p.2.1,
          coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2.2) := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
  rw [rightCappingProjectedSeamTargetBase,
    coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap_of_positive m p hp,
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph_inr]
  simp only [coordinateExteriorRightTubePowerPullbackProj,
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap,
    coordinateExteriorRoundedCapPowerPullbackToRightTube]
  change
    (((coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallSeamBranch m p)).1.1 :
        CollaredCutSide coordinateClosedCapZero) : Sphere 4) = _
  rw [coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph]
  change
    ((euclideanFourBallRoundedHemisphereDiffeomorph
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallSeamBranch m p).2 :
        CollaredCutSide coordinateClosedCapZero) : Sphere 4) = _
  rw [coordinateUnlinkExteriorPlanarNeckEuclideanFourBallSeamBranch]
  change
    ((euclideanFourBallRoundedHemisphereDiffeomorph
      (euclideanFourBallSmoothCollar (signedSeamHalfReparam m p).2) :
        CollaredCutSide coordinateClosedCapZero) : Sphere 4) = _
  rw [← coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar_apply,
    euclideanFourBallRoundedHemisphereDiffeomorph_boundaryCollar,
    roundedHemisphereClosedCapBoundaryCollar_coe,
    roundedHemisphereClosedCapCollarAmbient]
  congr 2
  apply Subtype.ext
  change -|(p.2.2.1 : ℝ)| = -(p.2.2.1 : ℝ)
  change 0 < (p.2.2.1 : ℝ) at hp
  rw [abs_of_pos hp]

private theorem leftCappingSeamTargetBase_coe_of_nonpositive
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : signedSeamTime m p ≤ 0)
    (hsmall : |(p.2.2.1 : ℝ)| < 1 / 8) :
    (leftCappingSeamTargetBase m p : Sphere 4) =
      equatorCollarSphereMap
        (p.2.1,
          coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2.2) := by
  rw [leftCappingSeamTargetBase,
    coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap_of_nonpositive m p hp,
    leftCappingRightTubeFamilyHomeomorph_inl]
  rw [leftCappingBodyMap, compactNeckLeftCutReflectedBase]
  change coordinateThreeReflectionSphere
    (compactNeckLeftBoundaryCollarMap m (signedSeamHalfReparam m p)).1.1.1 = _
  rw [compactNeckLeftBoundaryCollarMap,
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_eq_raw,
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap,
    compactNeckLeftHalfParameter_signedSeamHalfReparam m p hp,
    standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_apply_base,
    standardUnlinkClosedTubeExteriorToCoordinateExterior_coe,
    signedSeamHalfReparam_fst]
  rw [standardUnlinkComplementSmoothExteriorDiffeomorph_eq_self_of_not_mem_closedTubes_quarter]
  · exact coordinateThreeReflectionSphere_equatorCollar p.2
  · change equatorCollarSphereMap p.2 ∉
      standardUnlinkClosedTubes (1 / 4 : ℝ)
    have hsmall' :
        abs ((coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph
          p.2.2 : EquatorCollarInterval) : ℝ) < 1 / 8 := by
      simpa [coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph,
        abs_neg] using hsmall
    simpa [coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph] using
      leftCapping_equatorCollarNeg_not_mem_closedTubes_quarter
        (p.2.1,
          coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2.2)
        hsmall'

private theorem rightCappingProjectedSeamTargetBase_coe_of_nonpositive
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : signedSeamTime m p ≤ 0)
    (hsmall : |(p.2.2.1 : ℝ)| < 1 / 8) :
    (rightCappingProjectedSeamTargetBase m p : Sphere 4) =
      equatorCollarSphereMap
        (p.2.1,
          coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2.2) := by
  rw [rightCappingProjectedSeamTargetBase,
    coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap_of_nonpositive m p hp,
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph_inl]
  simp only [coordinateExteriorRightTubePowerPullbackProj,
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap]
  rw [coordinateUnlinkExteriorPlanarNeckRightCutSeamBranch,
    coordinateUnlinkExteriorPlanarNeckRightCutCollar]
  change
    (compactNeckRightBoundaryCollarMap m (signedSeamHalfReparam m p)).1.1.1 = _
  rw [compactNeckRightBoundaryCollarMap,
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_eq_raw,
    coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap]
  have hparam :
      compactNeckRightHalfParameter (signedSeamHalfReparam m p).2 =
        (p.2.1,
          coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2.2) := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change |(p.2.2.1 : ℝ)| = -(p.2.2.1 : ℝ)
      exact abs_of_nonpos hp
  rw [hparam,
    standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_apply_base,
    standardUnlinkClosedTubeExteriorToCoordinateExterior_coe,
    signedSeamHalfReparam_fst]
  change
    (standardUnlinkComplementSmoothExteriorDiffeomorph
      (equatorUnlinkPowerCollarLift m
        (p.1 - coordinateUnlinkExteriorPlanarSmoothNeckShift m)
        (p.2.1,
          coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2.2)).1.1 :
      Sphere 4) = _
  rw [standardUnlinkComplementSmoothExteriorDiffeomorph_eq_self_of_not_mem_closedTubes_quarter]
  · rfl
  · exact leftCapping_equatorCollarNeg_not_mem_closedTubes_quarter p.2 hsmall

private theorem leftCappingSeamTargetBase_eq_rightCapping_of_small
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hsmall : |signedSeamTime m p| < 1 / 8) :
    leftCappingSeamTargetBase m p =
      rightCappingProjectedSeamTargetBase m p := by
  apply Subtype.ext
  by_cases hp : signedSeamTime m p ≤ 0
  · rw [leftCappingSeamTargetBase_coe_of_nonpositive m p hp hsmall,
      rightCappingProjectedSeamTargetBase_coe_of_nonpositive m p hp hsmall]
  · have hp' : 0 < signedSeamTime m p := lt_of_not_ge hp
    rw [leftCappingSeamTargetBase_coe_of_positive m p hp',
      rightCappingProjectedSeamTargetBase_coe_of_positive m p hp']

private theorem leftCappingSeamTargetBase_eq_rightCapping_of_positive
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : 0 < signedSeamTime m p) :
    leftCappingSeamTargetBase m p =
      rightCappingProjectedSeamTargetBase m p := by
  apply Subtype.ext
  rw [leftCappingSeamTargetBase_coe_of_positive m p hp,
    rightCappingProjectedSeamTargetBase_coe_of_positive m p hp]

private theorem isLocalDiffeomorph_leftCutCollar :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckLeftCutChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m) := by
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  have hcompat := collaredCutSideAtlasChart_compatible_of_localDiffeomorphOn
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckLeftCut_offBoundary m)
    (compactNeckLeftBoundaryCollarMap m)
    (compactNeckLeftBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckLeftBoundaryCollarMap_toCut m)
    (isLocalDiffeomorphOn_compactNeckLeftBoundaryCollarMap m)
  exact isLocalDiffeomorph_collaredCutSideHalfCollarMap
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckLeftCut_offBoundary m)
    (compactNeckLeftBoundaryCollarMap m)
    (compactNeckLeftBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckLeftBoundaryCollarMap_toCut m)
    (compactNeckLeftCut_collarCoverage m) hcompat

private theorem isLocalDiffeomorphAt_leftCappingSeamTargetBase_of_negative
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : signedSeamTime m p < 0) :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (leftCappingSeamTargetBase m) p := by
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    isManifold_signedSeamFamilyCommonModel m
  let _ := compactNeckLeftCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckLeftCut m) :=
    isManifold_compactNeckLeftCut m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  have hhalf : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (signedSeamHalfReparam m) p :=
    isLocalDiffeomorphOn_signedSeamHalfReparam_negative m ⟨p, hp⟩
  have hcollar : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
      (signedSeamHalfReparam m p) :=
    isLocalDiffeomorph_leftCutCollar m (signedSeamHalfReparam m p)
  have hbranch : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m ∘
        signedSeamHalfReparam m) p :=
    hhalf.comp coordinateUnlinkExteriorModel (CompactNeckLeftCut m) hcollar
  have hoff :
      (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m
        (signedSeamHalfReparam m p)).1 ∈
        collaredCutSideOffBoundary
          (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
          (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) := by
    change compactNeckLeftBoundaryCollarMap m
      (signedSeamHalfReparam m p) ∈ _
    rw [compactNeckLeftBoundaryCollarMap_mem_offBoundary_iff]
    change 0 < |signedSeamTime m p|
    exact abs_pos.mpr (ne_of_lt hp)
  have hbase : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (leftCappingCutBaseMap m)
      (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m
        (signedSeamHalfReparam m p)) :=
    isLocalDiffeomorphAt_leftCappingCutBaseMap_of_offBoundary_standard m _ hoff
  have hcomp : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (leftCappingCutBaseMap m ∘
        coordinateUnlinkExteriorPlanarNeckLeftCutCollar m ∘
        signedSeamHalfReparam m) p :=
    hbranch.comp coordinateUnlinkExteriorModel
      CoordinateExteriorRightTubeClosed hbase
  let W : Set
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    {q | signedSeamTime m q < 0}
  apply leftCapping_isLocalDiffeomorphAt_congr_of_eqOn_open hcomp W
  · exact isOpen_lt (contMDiff_signedSeamFamilyTime m).continuous continuous_const
  · exact hp
  · intro q hq
    rw [leftCappingSeamTargetBase,
      coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap_of_nonpositive
        m q (le_of_lt hq), leftCappingRightTubeFamilyHomeomorph_inl]
    exact (leftCappingCutBaseMap_eq_bodyMap_snd m _).symm

private theorem isLocalDiffeomorphAt_leftCappingSeamTargetBase_of_positive
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : 0 < signedSeamTime m p) :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (leftCappingSeamTargetBase m) p := by
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let W : Set
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    {q | 0 < signedSeamTime m q}
  apply leftCapping_isLocalDiffeomorphAt_congr_of_eqOn_open
    (isLocalDiffeomorph_rightCappingProjectedSeamTargetBase m p) W
  · exact isOpen_lt continuous_const
      (contMDiff_signedSeamFamilyTime m).continuous
  · exact hp
  · intro q hq
    exact leftCappingSeamTargetBase_eq_rightCapping_of_positive m q hq

private theorem isLocalDiffeomorphAt_leftCappingSeamTargetBase_of_zero
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : signedSeamTime m p = 0) :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (leftCappingSeamTargetBase m) p := by
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let W : Set
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    {q | |signedSeamTime m q| < 1 / 8}
  apply leftCapping_isLocalDiffeomorphAt_congr_of_eqOn_open
    (isLocalDiffeomorph_rightCappingProjectedSeamTargetBase m p) W
  · have ht : Continuous (signedSeamTime m) :=
      (contMDiff_signedSeamFamilyTime m).continuous
    exact (_root_.continuous_abs.comp ht).isOpen_preimage _ isOpen_Iio
  · change |signedSeamTime m p| < 1 / 8
    rw [hp, abs_zero]
    norm_num
  · intro q hq
    exact leftCappingSeamTargetBase_eq_rightCapping_of_small m q hq

private theorem isLocalDiffeomorph_leftCappingSeamTargetBase :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (leftCappingSeamTargetBase m) := by
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  intro p
  rcases lt_trichotomy (signedSeamTime m p) 0 with hp | hp | hp
  · exact isLocalDiffeomorphAt_leftCappingSeamTargetBase_of_negative m p hp
  · exact isLocalDiffeomorphAt_leftCappingSeamTargetBase_of_zero m p hp
  · exact isLocalDiffeomorphAt_leftCappingSeamTargetBase_of_positive m p hp

private theorem isLocalDiffeomorph_leftCapping_seam :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := coordinateExteriorRightTubeStandardChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (leftCappingRightTubeFamilyHomeomorph m ∘
        coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m) := by
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    isManifold_signedSeamFamilyCommonModel m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × CoordinateExteriorRightTubeClosed) :=
    isManifold_discreteProductChartedSpace coordinateUnlinkExteriorModel ∞
      (ZMod m) CoordinateExteriorRightTubeClosed
  let F := leftCappingRightTubeFamilyHomeomorph m ∘
    coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m
  have hF : Continuous F :=
    (leftCappingRightTubeFamilyHomeomorph m).continuous.comp
      (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m).continuous
  have hsnd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × CoordinateExteriorRightTubeClosed →
        CoordinateExteriorRightTubeClosed) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := CoordinateExteriorRightTubeClosed))
  apply leftCapping_reflect_isLocalDiffeomorph Prod.snd F hsnd hF
  intro p
  change IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
    coordinateUnlinkExteriorModel ∞ (leftCappingSeamTargetBase m) p
  exact isLocalDiffeomorph_leftCappingSeamTargetBase m p

private def leftCappingRightTubeFamilyDiffeomorph :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := coordinateExteriorRightTubeStandardChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel,
        coordinateUnlinkExteriorModel⟯
      ZMod m × CoordinateExteriorRightTubeClosed := by
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    isManifold_signedSeamFamilyCommonModel m
  let _ := compactNeckLeftCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckLeftCut m) :=
    isManifold_compactNeckLeftCut m
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBall) :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × CoordinateExteriorRightTubeClosed) :=
    isManifold_discreteProductChartedSpace coordinateUnlinkExteriorModel ∞
      (ZMod m) CoordinateExteriorRightTubeClosed
  exact diffeomorphOfCollaredPushoutHomeomorph
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap m)
    (coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingSeamMap_attaching_coverage m)
    (isManifold_coordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m)
    (leftCappingRightTubeFamilyHomeomorph m)
    (isLocalDiffeomorph_leftCapping_seam m)
    (isLocalDiffeomorph_leftCapping_cutOffSeam m)
    (isLocalDiffeomorph_leftCapping_capOffSeam m)

private def rightTubeOneHandleFamilyHomeomorph :
    ZMod m × CoordinateExteriorRightTubeClosed ≃ₜ
      ZMod m × OneHandlePiece :=
  (Homeomorph.refl (ZMod m)).prodCongr
    coordinateExteriorRightTubeOneHandleHomeomorph

private def rightTubeOneHandleFamilyDiffeomorph :
    letI := coordinateExteriorRightTubeStandardChartedSpace
    letI := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m) CoordinateExteriorRightTubeClosed
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    (ZMod m × CoordinateExteriorRightTubeClosed)
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, oneHandlePieceModel⟯
        ZMod m × OneHandlePiece := by
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ := discreteProductChartedSpace OneHandleModelSpace
    (ZMod m) OneHandlePiece
  have hs : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × CoordinateExteriorRightTubeClosed →
        CoordinateExteriorRightTubeClosed) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := CoordinateExteriorRightTubeClosed))
  have ht : IsLocalDiffeomorph oneHandlePieceModel
      oneHandlePieceModel ∞
      (Prod.snd : ZMod m × OneHandlePiece → OneHandlePiece) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      oneHandlePieceModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := OneHandlePiece))
  exact diffeomorphOfHomeomorphOverDiffeomorph
    coordinateUnlinkExteriorModel oneHandlePieceModel Prod.snd Prod.snd
    hs ht coordinateExteriorRightTubeOneHandleStandardDiffeomorph
    (rightTubeOneHandleFamilyHomeomorph m) (by
      intro z
      change coordinateExteriorRightTubeOneHandleHomeomorph z.2 =
        coordinateExteriorRightTubeOneHandleStandardDiffeomorph z.2
      exact (coordinateExteriorRightTubeOneHandleStandardDiffeomorph_apply z.2).symm)

private def leftCappingOneHandleFamilyDiffeomorph :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, oneHandlePieceModel⟯
        ZMod m × OneHandlePiece := by
  let _ := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ := discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) CoordinateExteriorRightTubeClosed
  let _ := discreteProductChartedSpace OneHandleModelSpace
    (ZMod m) OneHandlePiece
  let e₁ : CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel,
        coordinateUnlinkExteriorModel⟯
      ZMod m × CoordinateExteriorRightTubeClosed :=
    leftCappingRightTubeFamilyDiffeomorph m
  let e₂ : (ZMod m × CoordinateExteriorRightTubeClosed)
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, oneHandlePieceModel⟯
      ZMod m × OneHandlePiece :=
    rightTubeOneHandleFamilyDiffeomorph m
  exact e₁.trans e₂

private theorem leftCappingOneHandleFamilyDiffeomorph_apply
    (z : CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m) :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    leftCappingOneHandleFamilyDiffeomorph m z =
      rightTubeOneHandleFamilyHomeomorph m
        (leftCappingRightTubeFamilyHomeomorph m z) := by
  rfl

private theorem leftCappingOneHandleFamilyDiffeomorph_toHomeomorph :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    (leftCappingOneHandleFamilyDiffeomorph m).toHomeomorph =
      (leftCappingRightTubeFamilyHomeomorph m).trans
        (rightTubeOneHandleFamilyHomeomorph m) := by
  rfl

private theorem leftCappingOneHandleFamilyDiffeomorph_inl
    (x : CompactNeckLeftCut m) :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    leftCappingOneHandleFamilyDiffeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x) =
      rightTubeOneHandleFamilyHomeomorph m (leftCappingBodyMap m x) := by
  rw [leftCappingOneHandleFamilyDiffeomorph_apply,
    leftCappingRightTubeFamilyHomeomorph_inl]

private theorem leftCappingOneHandleFamilyDiffeomorph_inr
    (y : ZMod m × EuclideanFourBall) :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    leftCappingOneHandleFamilyDiffeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) y) =
      rightTubeOneHandleFamilyHomeomorph m (leftCappingCapMap m y) := by
  rw [leftCappingOneHandleFamilyDiffeomorph_apply,
    leftCappingRightTubeFamilyHomeomorph_inr]

@[expose] public section

namespace CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal

/-- The minimal semantic construction spine for the direct left-capping recognition.

The analytic reflection and rounded-cap trivialization proofs remain private to this module;
these fields record only the resulting point-set maps and their smooth recognition. -/
structure Construction (m : ℕ) [NeZero m] where
  /-- The body generator map into the labelled direct right-tube family. -/
  bodyMap : CompactNeckLeftCut m →
    ZMod m × CoordinateExteriorRightTubeClosed
  /-- The rounded-cap generator map into the labelled direct right-tube family. -/
  capMap : ZMod m × EuclideanFourBall →
    ZMod m × CoordinateExteriorRightTubeClosed
  /-- The point-set comparison with the labelled direct right-tube family. -/
  rightTubeHomeomorph :
    CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m ≃ₜ
      ZMod m × CoordinateExteriorRightTubeClosed
  /-- The body coprojection law for the point-set comparison. -/
  rightTubeHomeomorph_inl (x : CompactNeckLeftCut m) :
    rightTubeHomeomorph
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x) =
      bodyMap x
  /-- The cap coprojection law for the point-set comparison. -/
  rightTubeHomeomorph_inr (y : ZMod m × EuclideanFourBall) :
    rightTubeHomeomorph
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) y) =
      capMap y
  /-- The resulting direct diffeomorphism to the labelled natural one-handle family. -/
  diffeomorph :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, oneHandlePieceModel⟯
        ZMod m × OneHandlePiece
  /-- The smooth comparison has the expected composite forward function. -/
  diffeomorph_apply (z :
      CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m) :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    diffeomorph z =
      ((Homeomorph.refl (ZMod m)).prodCongr
        coordinateExteriorRightTubeOneHandleHomeomorph)
          (rightTubeHomeomorph z)
  /-- Forgetting smoothness gives the composite point-set comparison. -/
  diffeomorph_toHomeomorph :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    diffeomorph.toHomeomorph =
      rightTubeHomeomorph.trans
        ((Homeomorph.refl (ZMod m)).prodCongr
          coordinateExteriorRightTubeOneHandleHomeomorph)

/-- The direct point-set and smooth construction underlying the left-capping recognition. -/
noncomputable def construction (m : ℕ) [NeZero m] : Construction m :=
  Classical.choice (by
    exact ⟨{
      bodyMap := leftCappingBodyMap m
      capMap := leftCappingCapMap m
      rightTubeHomeomorph := leftCappingRightTubeFamilyHomeomorph m
      rightTubeHomeomorph_inl := leftCappingRightTubeFamilyHomeomorph_inl m
      rightTubeHomeomorph_inr := leftCappingRightTubeFamilyHomeomorph_inr m
      diffeomorph := leftCappingOneHandleFamilyDiffeomorph m
      diffeomorph_apply := leftCappingOneHandleFamilyDiffeomorph_apply m
      diffeomorph_toHomeomorph :=
        leftCappingOneHandleFamilyDiffeomorph_toHomeomorph m }⟩)

end CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal

/-- Recognize the direct left smooth capping as the labelled natural one-handle family. -/
noncomputable def coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, oneHandlePieceModel⟯
        ZMod m × OneHandlePiece :=
  (CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction m).diffeomorph

/-- The direct recognition has the expected composite forward function. -/
@[simp] theorem coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph_apply
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorPlanarNeckLeftSmoothCapping m) :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph m z =
      ((Homeomorph.refl (ZMod m)).prodCongr
        coordinateExteriorRightTubeOneHandleHomeomorph)
          ((CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
            m).rightTubeHomeomorph z) :=
  (CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
    m).diffeomorph_apply z

/-- Forgetting smoothness gives the composite point-set comparison. -/
@[simp] theorem
    coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph_toHomeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    (coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph m).toHomeomorph =
      ((CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
        m).rightTubeHomeomorph).trans
        ((Homeomorph.refl (ZMod m)).prodCongr
          coordinateExteriorRightTubeOneHandleHomeomorph) :=
  (CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
    m).diffeomorph_toHomeomorph

/-- On the compact-cut generator, the recognition is the reflected body map. -/
theorem coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph_inl
    (m : ℕ) [NeZero m] (x : CompactNeckLeftCut m) :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x) =
      ((Homeomorph.refl (ZMod m)).prodCongr
        coordinateExteriorRightTubeOneHandleHomeomorph)
          ((CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
            m).bodyMap x) := by
  rw [coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph_apply]
  rw [(CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
    m).rightTubeHomeomorph_inl]

/-- On the rounded-cap generator, the recognition is the rounded-cap map. -/
theorem coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph_inr
    (m : ℕ) [NeZero m] (y : ZMod m × EuclideanFourBall) :
    letI := coordinateUnlinkExteriorPlanarNeckLeftSmoothCappingChartedSpace m
    letI := discreteProductChartedSpace OneHandleModelSpace
      (ZMod m) OneHandlePiece
    coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) y) =
      ((Homeomorph.refl (ZMod m)).prodCongr
        coordinateExteriorRightTubeOneHandleHomeomorph)
          ((CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
            m).capMap y) := by
  rw [coordinateExteriorPlanarNeckLeftSmoothCappingOneHandleDiffeomorph_apply]
  rw [(CoordinateExteriorPlanarNeckLeftSmoothCappingOneHandleInternal.construction
    m).rightTubeHomeomorph_inr]

end

end SplittingSpheres
