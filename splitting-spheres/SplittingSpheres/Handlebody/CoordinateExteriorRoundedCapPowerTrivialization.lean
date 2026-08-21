/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.EuclideanFourBallRoundedHemisphere
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCompactCollar

/-!
# Rounded-cap power trivialization

This file constructs the shifted logarithmic power root on the direct rounded negative cap,
trivializes its nonzero power pullback by the discrete label family, and compares the result
smoothly with the common-model Euclidean four-ball family. The boundary formula uses the exact
compact-neck label shift. No capping pushout or global handlebody recognition is asserted here.
-/

@[expose] public section

open Function Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

private local instance :
    ChartedSpace CoordinateUnlinkExteriorModelSpace EuclideanFourBall :=
  coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace

private local instance : IsManifold coordinateUnlinkExteriorModel ∞
    EuclideanFourBall :=
  isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBall

private local instance :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CollaredCutSide coordinateClosedCapZero) :=
  coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace

private local instance :
    ChartedSpace CoordinateUnlinkExteriorModelSpace (Sphere 4) :=
  coordinateUnlinkExteriorCommonModelSphereChartedSpace

private local instance : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
  isManifold_coordinateUnlinkExteriorCommonModelSphere

private local instance :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      EuclideanFourBallCollarDomain :=
  coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace

private local instance :
    IsManifold coordinateUnlinkExteriorModel ∞ EuclideanFourBallCollarDomain :=
  isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain

private local instance : IsManifold coordinateUnlinkExteriorModel ∞
    (CollaredCutSide coordinateClosedCapZero) :=
  isManifold_coordinateUnlinkExteriorRoundedHemisphereClosedCap

private theorem contMDiff_roundedHemisphereClosedCapCollarAmbient_commonModel :
    ContMDiff coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      roundedHemisphereClosedCapCollarAmbient := by
  have htime : ContMDiff euclideanFourBallCollarModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : EuclideanFourBallCollarDomain ↦
        (roundedHemisphereEquatorTime p.2 : ℝ)) := by
    have hhalf : ContMDiff euclideanFourBallCollarModel
        (modelWithCornersEuclideanHalfSpace 1) ∞
        (fun p : EuclideanFourBallCollarDomain ↦ p.2.1) :=
      contMDiff_subtype_val.comp contMDiff_snd
    have hval : ContMDiff euclideanFourBallCollarModel
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : EuclideanFourBallCollarDomain ↦ (p.2.1.1 : ℝ)) :=
      contMDiff_subtypeVal_Icc.comp hhalf
    exact hval.neg.congr fun _ ↦ roundedHemisphereEquatorTime_value _
  have hin : ContMDiff euclideanFourBallCollarModel
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
        (modelWithCornersSelf ℝ ℝ)) ∞
      (fun p : EuclideanFourBallCollarDomain ↦
        (p.1, roundedHemisphereEquatorTime p.2)) := by
    apply ContMDiff.prodMk contMDiff_fst
    apply (ContMDiff.subtypeVal_comp_iff equatorCollarIntervalOpens _).mp
    exact htime
  have hnatural : ContMDiff euclideanFourBallCollarModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      roundedHemisphereClosedCapCollarAmbient := by
    exact (contMDiff_equatorCollarSphereMap.comp hin).congr fun _ ↦ rfl
  have hsource := hnatural.comp
    coordinateUnlinkExteriorRechartedFourBallCollarIdentityDiffeomorph.contMDiff
  have htarget :=
    standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph.contMDiff.comp
      hsource
  exact htarget.congr fun _ ↦ rfl

private theorem contMDiff_coordinateExteriorRoundedCapSubtypeVal :
    ContMDiff coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      (Subtype.val : CollaredCutSide coordinateClosedCapZero → Sphere 4) := by
  have hcompat : ∀ i j : CollaredCutSideAtlasIndex coordinateClosedCapZero
      coordinateEquator EuclideanFourBallCollarDomain,
      (collaredCutSideAtlasChart coordinateClosedCapZero coordinateEquator
        isOpen_roundedHemisphereClosedCapZero_offBoundary
        roundedHemisphereClosedCapCollarAmbient
        range_roundedHemisphereClosedCapCollarAmbient_subset
        isOpenEmbedding_roundedHemisphereClosedCapBoundaryCollar i).symm.trans
      (collaredCutSideAtlasChart coordinateClosedCapZero coordinateEquator
        isOpen_roundedHemisphereClosedCapZero_offBoundary
        roundedHemisphereClosedCapCollarAmbient
        range_roundedHemisphereClosedCapCollarAmbient_subset
        isOpenEmbedding_roundedHemisphereClosedCapBoundaryCollar j) ∈
        contDiffGroupoid ∞ coordinateUnlinkExteriorModel := by
    intro i j
    apply IsManifold.compatible_of_mem_maximalAtlas
    · apply IsManifold.subset_maximalAtlas
      exact ⟨i, rfl⟩
    · apply IsManifold.subset_maximalAtlas
      exact ⟨j, rfl⟩
  exact contMDiff_collaredCutSideSubtypeVal coordinateUnlinkExteriorModel ∞
    coordinateUnlinkExteriorModel coordinateClosedCapZero coordinateEquator
    isOpen_roundedHemisphereClosedCapZero_offBoundary
    roundedHemisphereClosedCapCollarAmbient
    range_roundedHemisphereClosedCapCollarAmbient_subset
    isOpenEmbedding_roundedHemisphereClosedCapBoundaryCollar
    roundedHemisphereClosedCapZero_cover hcompat
    (contMDiffOn_collaredCutSideAtlasChart_symm_subtypeVal
      coordinateUnlinkExteriorModel ∞ coordinateClosedCapZero coordinateEquator
      isOpen_roundedHemisphereClosedCapZero_offBoundary
      roundedHemisphereClosedCapCollarAmbient
      range_roundedHemisphereClosedCapCollarAmbient_subset
      isOpenEmbedding_roundedHemisphereClosedCapBoundaryCollar
      contMDiff_roundedHemisphereClosedCapCollarAmbient_commonModel)

private theorem contMDiff_standardUnlinkRightCharacter_commonSphere :
    ContMDiff coordinateUnlinkExteriorModel (modelWithCornersSelf ℝ ℂ) ∞
      standardUnlinkRightDisplacementComplex := by
  have hstd : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ ℂ) ∞
      standardUnlinkRightDisplacementComplex := by
    let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) :=
      ⟨by simp⟩
    have hcoord3 : ContDiff ℝ ∞
        (fun x : EuclideanSpace ℝ (Fin 5) ↦ x 3) := by
      fun_prop
    have hcoord4 : ContDiff ℝ ∞
        (fun x : EuclideanSpace ℝ (Fin 5) ↦ x 4) := by
      fun_prop
    have hof3 : ContDiff ℝ ∞
        (fun x : EuclideanSpace ℝ (Fin 5) ↦ (x 3 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hcoord3
    have hre : ContDiff ℝ ∞
        (fun x : EuclideanSpace ℝ (Fin 5) ↦ (x 3 - 1 / 2 : ℂ)) :=
      hof3.sub contDiff_const
    have him : ContDiff ℝ ∞
        (fun x : EuclideanSpace ℝ (Fin 5) ↦ (x 4 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hcoord4
    have hambient : ContDiff ℝ ∞
        (fun x : EuclideanSpace ℝ (Fin 5) ↦
          (x 3 - 1 / 2 : ℂ) + (x 4 : ℂ) * Complex.I) :=
      hre.add (him.mul contDiff_const)
    exact (hambient.comp_contMDiff contMDiff_coe_sphere).congr fun q ↦ by
      simp [standardUnlinkRightDisplacementComplex,
        standardUnlinkNormalProjection, standardUnlinkNormalCenter,
        standardUnlinkHeight, unlinkNormalPlaneToComplex,
        Complex.equivRealProdCLM_symm_apply]
  exact (hstd.comp
    coordinateUnlinkExteriorCommonModelToStandardSphereIdentityDiffeomorph.contMDiff).congr
      fun _ ↦ rfl

private theorem contMDiff_coordinateExteriorRoundedCapRightCharacter :
    ContMDiff coordinateUnlinkExteriorModel (modelWithCornersSelf ℝ ℂ) ∞
      (fun q : CollaredCutSide coordinateClosedCapZero ↦
        standardUnlinkRightDisplacementComplex (q.1 : Sphere 4)) :=
  contMDiff_standardUnlinkRightCharacter_commonSphere.comp
    contMDiff_coordinateExteriorRoundedCapSubtypeVal

/-- The right character does not cross the rotated logarithm cut on the rounded negative cap. -/
theorem neg_rightCharacter_mem_slitPlane_of_mem_coordinateClosedCapZero
    (q : CollaredCutSide coordinateClosedCapZero) :
    -standardUnlinkRightDisplacementComplex (q.1 : Sphere 4) ∈
      Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have hq : ¬0 < (q.1 : Sphere 4).1 3 := q.2
  simp [standardUnlinkRightDisplacementComplex,
    standardUnlinkNormalProjection, standardUnlinkNormalCenter,
    standardUnlinkHeight, unlinkNormalPlaneToComplex,
    Complex.equivRealProdCLM_symm_apply]
  linarith

/-- The rotated logarithmic root of the right character on the rounded negative cap. -/
@[nolint unusedArguments]
def coordinateExteriorRoundedCapPowerRoot (m : ℕ) [NeZero m]
    (q : CollaredCutSide coordinateClosedCapZero) : ℂ :=
  Complex.exp
    ((Complex.log
      (-standardUnlinkRightDisplacementComplex (q.1 : Sphere 4)) +
        (Real.pi : ℂ) * Complex.I) / (m : ℂ))

/-- The rounded-cap power root is smooth in the direct common-model atlas. -/
theorem contMDiff_coordinateExteriorRoundedCapPowerRoot (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
    ContMDiff coordinateUnlinkExteriorModel (modelWithCornersSelf ℝ ℂ) ∞
      (coordinateExteriorRoundedCapPowerRoot m) := by
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  intro q
  have hneg : ContDiffAt ℝ ∞ (fun z : ℂ ↦ -z)
      (standardUnlinkRightDisplacementComplex (q.1 : Sphere 4)) :=
    contDiffAt_id.neg
  have hlog : ContDiffAt ℝ ∞
      (fun z : ℂ ↦ Complex.log (-z))
      (standardUnlinkRightDisplacementComplex (q.1 : Sphere 4)) :=
    (Complex.contDiffAt_log (neg_rightCharacter_mem_slitPlane_of_mem_coordinateClosedCapZero q))
      |>.restrict_scalars ℝ |>.comp _ hneg
  have harg : ContDiffAt ℝ ∞
      (fun z : ℂ ↦
        (Complex.log (-z) + (Real.pi : ℂ) * Complex.I) / (m : ℂ))
      (standardUnlinkRightDisplacementComplex (q.1 : Sphere 4)) :=
    (hlog.add contDiffAt_const).div_const _
  have hbranch : ContMDiffAt
      (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : ℂ ↦ Complex.exp
        ((Complex.log (-z) + (Real.pi : ℂ) * Complex.I) / (m : ℂ)))
      (standardUnlinkRightDisplacementComplex (q.1 : Sphere 4)) :=
    contMDiffAt_iff_contDiffAt.mpr
      ((Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp _ harg)
  exact hbranch.comp
    (f := fun q : CollaredCutSide coordinateClosedCapZero ↦
      standardUnlinkRightDisplacementComplex (q.1 : Sphere 4))
    q contMDiff_coordinateExteriorRoundedCapRightCharacter.contMDiffAt

/-- The `m`-th power of the rounded-cap root is the right normal character. -/
@[simp]
theorem coordinateExteriorRoundedCapPowerRoot_pow (m : ℕ) [NeZero m]
    (q : CollaredCutSide coordinateClosedCapZero) :
    coordinateExteriorRoundedCapPowerRoot m q ^ m =
      standardUnlinkRightDisplacementComplex (q.1 : Sphere 4) := by
  unfold coordinateExteriorRoundedCapPowerRoot
  rw [← Complex.exp_nat_mul]
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [show (m : ℂ) *
      ((Complex.log
          (-standardUnlinkRightDisplacementComplex (q.1 : Sphere 4)) +
        (Real.pi : ℂ) * Complex.I) / (m : ℂ)) =
      Complex.log
          (-standardUnlinkRightDisplacementComplex (q.1 : Sphere 4)) +
        (Real.pi : ℂ) * Complex.I by field_simp]
  rw [Complex.exp_add, Complex.exp_log
    (Complex.slitPlane_ne_zero (neg_rightCharacter_mem_slitPlane_of_mem_coordinateClosedCapZero q)),
    Complex.exp_pi_mul_I]
  ring

/-- The rounded-cap power root never vanishes. -/
theorem coordinateExteriorRoundedCapPowerRoot_ne_zero (m : ℕ) [NeZero m]
    (q : CollaredCutSide coordinateClosedCapZero) :
    coordinateExteriorRoundedCapPowerRoot m q ≠ 0 :=
  Complex.exp_ne_zero _

/-- The labelled cap root uses the exact label of the compact collar zero section. -/
def coordinateExteriorRoundedCapPowerRootTranslate (m : ℕ) [NeZero m]
    (a : ZMod m) (q : CollaredCutSide coordinateClosedCapZero) : ℂ :=
  (((standardRootsOfUnityZModMulEquiv m
    (Multiplicative.ofAdd
      (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m))).1 : ℂˣ) : ℂ) *
    coordinateExteriorRoundedCapPowerRoot m q

/-- Each translated rounded-cap root is smooth. -/
theorem contMDiff_coordinateExteriorRoundedCapPowerRootTranslate
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
    ContMDiff coordinateUnlinkExteriorModel (modelWithCornersSelf ℝ ℂ) ∞
      (coordinateExteriorRoundedCapPowerRootTranslate m a) := by
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  let c : ℂ :=
    (((standardRootsOfUnityZModMulEquiv m
      (Multiplicative.ofAdd
        (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m))).1 : ℂˣ) : ℂ)
  have hmul : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞ (fun z : ℂ ↦ c * z) :=
    contMDiff_iff_contDiff.mpr (contDiff_const.mul contDiff_id)
  exact (hmul.comp (contMDiff_coordinateExteriorRoundedCapPowerRoot m)).congr fun _ ↦ rfl

/-- A translated rounded-cap root never vanishes. -/
theorem coordinateExteriorRoundedCapPowerRootTranslate_ne_zero
    (m : ℕ) [NeZero m] (a : ZMod m)
    (q : CollaredCutSide coordinateClosedCapZero) :
    coordinateExteriorRoundedCapPowerRootTranslate m a q ≠ 0 :=
  mul_ne_zero
    (Units.ne_zero
      (standardRootsOfUnityZModMulEquiv m
        (Multiplicative.ofAdd
          (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m))).1)
    (coordinateExteriorRoundedCapPowerRoot_ne_zero m q)

/-- Translation by the shifted label does not change the `m`-th power. -/
@[simp]
theorem coordinateExteriorRoundedCapPowerRootTranslate_pow
    (m : ℕ) [NeZero m] (a : ZMod m)
    (q : CollaredCutSide coordinateClosedCapZero) :
    coordinateExteriorRoundedCapPowerRootTranslate m a q ^ m =
      standardUnlinkRightDisplacementComplex (q.1 : Sphere 4) := by
  rw [coordinateExteriorRoundedCapPowerRootTranslate, mul_pow,
    (mem_rootsOfUnity' m
      (standardRootsOfUnityZModMulEquiv m
        (Multiplicative.ofAdd
          (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m))).1).mp
        (standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd
            (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m))).2,
    one_mul, coordinateExteriorRoundedCapPowerRoot_pow]

/-- On the collar zero section, the rounded-cap root is the equatorial power root. -/
@[simp]
theorem coordinateExteriorRoundedCapPowerRoot_boundary (m : ℕ) [NeZero m]
    (s : Sphere 3) :
    coordinateExteriorRoundedCapPowerRoot m
        (roundedHemisphereClosedCapBoundaryCollar
          (s, euclideanFourBallCollarZero)) =
      equatorUnlinkPowerRoot m s := by
  unfold coordinateExteriorRoundedCapPowerRoot equatorUnlinkPowerRoot
  rw [roundedHemisphereClosedCapBoundaryCollar_coe]
  rw [show roundedHemisphereClosedCapCollarAmbient
      (s, euclideanFourBallCollarZero) = equatorSphereMap s by
    rw [roundedHemisphereClosedCapCollarAmbient]
    rw [show roundedHemisphereEquatorTime euclideanFourBallCollarZero =
        ⟨0, show (0 : ℝ) ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) by norm_num⟩ by
      apply Subtype.ext
      simp]
    exact equatorCollarSphereMap_zero s]
  rw [standardUnlinkRightDisplacementComplex_equatorSphereMap]

/-- On the collar zero section, the translated root has the exact shifted equatorial label. -/
@[simp]
theorem coordinateExteriorRoundedCapPowerRootTranslate_boundary
    (m : ℕ) [NeZero m] (a : ZMod m) (s : Sphere 3) :
    coordinateExteriorRoundedCapPowerRootTranslate m a
        (roundedHemisphereClosedCapBoundaryCollar
          (s, euclideanFourBallCollarZero)) =
      equatorUnlinkPowerRootTranslate m
        (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) s := by
  rw [coordinateExteriorRoundedCapPowerRootTranslate,
    equatorUnlinkPowerRootTranslate,
    coordinateExteriorRoundedCapPowerRoot_boundary]

/-- Every nonzero root in a power fiber is one of the shifted labelled roots. -/
theorem exists_coordinateExteriorRoundedCapPowerRootTranslate_eq
    (m : ℕ) [NeZero m] (q : CollaredCutSide coordinateClosedCapZero)
    (w : ℂ) (hw0 : w ≠ 0)
    (hpow : w ^ m = standardUnlinkRightDisplacementComplex (q.1 : Sphere 4)) :
    ∃ a : ZMod m, coordinateExteriorRoundedCapPowerRootTranslate m a q = w := by
  let r := coordinateExteriorRoundedCapPowerRoot m q
  have hr0 : r ≠ 0 := coordinateExteriorRoundedCapPowerRoot_ne_zero m q
  let u : ℂˣ := Units.mk0 (w / r) (div_ne_zero hw0 hr0)
  have hupow : (u : ℂ) ^ m = 1 := by
    dsimp [u]
    rw [div_pow, hpow, coordinateExteriorRoundedCapPowerRoot_pow]
    exact div_self (neg_ne_zero.mp (Complex.slitPlane_ne_zero
      (neg_rightCharacter_mem_slitPlane_of_mem_coordinateClosedCapZero q)))
  let ζ : rootsOfUnity m ℂ :=
    ⟨u, (mem_rootsOfUnity' m u).mpr hupow⟩
  let b : Multiplicative (ZMod m) :=
    (standardRootsOfUnityZModMulEquiv m).symm ζ
  let shift := coordinateUnlinkExteriorPlanarSmoothNeckShift m
  refine ⟨b.toAdd + shift, ?_⟩
  change (((standardRootsOfUnityZModMulEquiv m
      (Multiplicative.ofAdd (b.toAdd + shift - shift))).1 : ℂˣ) : ℂ) * r = w
  rw [add_sub_cancel_right]
  have hb : Multiplicative.ofAdd b.toAdd = b := rfl
  rw [hb, (standardRootsOfUnityZModMulEquiv m).apply_symm_apply]
  change (w / r) * r = w
  exact div_mul_cancel₀ w hr0

/-- The direct common-model charted space on the discrete family of rounded caps. -/
@[instance_reducible, nolint unusedArguments]
def coordinateExteriorRoundedCapFamilyChartedSpace (m : ℕ) [NeZero m] :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (ZMod m × CollaredCutSide coordinateClosedCapZero) := by
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  exact discreteProductChartedSpace CoordinateUnlinkExteriorModelSpace
    (ZMod m) (CollaredCutSide coordinateClosedCapZero)

/-- The shifted root evaluated on the labelled rounded-cap family. -/
def coordinateExteriorRoundedCapFamilyPowerRoot (m : ℕ) [NeZero m]
    (p : ZMod m × CollaredCutSide coordinateClosedCapZero) : ℂ :=
  coordinateExteriorRoundedCapPowerRootTranslate m p.1 p.2

/-- The power root on the labelled rounded-cap family is smooth. -/
theorem contMDiff_coordinateExteriorRoundedCapFamilyPowerRoot
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorRoundedCapFamilyChartedSpace m
    ContMDiff coordinateUnlinkExteriorModel (modelWithCornersSelf ℝ ℂ) ∞
      (coordinateExteriorRoundedCapFamilyPowerRoot m) := by
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  let _ := coordinateExteriorRoundedCapFamilyChartedSpace m
  have hsnd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × CollaredCutSide coordinateClosedCapZero →
        CollaredCutSide coordinateClosedCapZero) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := CollaredCutSide coordinateClosedCapZero))
  intro x
  have hx := ((contMDiff_coordinateExteriorRoundedCapPowerRootTranslate m x.1).comp
    hsnd.contMDiff) x
  apply hx.congr_of_eventuallyEq
  filter_upwards [
    ((isOpen_discrete ({x.1} : Set (ZMod m))).preimage continuous_fst).mem_nhds
      (by simp)] with y hy
  simp only [mem_preimage, mem_singleton_iff] at hy
  simp [coordinateExteriorRoundedCapFamilyPowerRoot, hy]

/-- The nonzero right normal character of the direct rounded cap. -/
def coordinateExteriorRoundedCapRightNormalMap
    (q : CollaredCutSide coordinateClosedCapZero) : {z : ℂ // z ≠ 0} :=
  ⟨standardUnlinkRightDisplacementComplex (q.1 : Sphere 4),
    neg_ne_zero.mp (Complex.slitPlane_ne_zero
      (neg_rightCharacter_mem_slitPlane_of_mem_coordinateClosedCapZero q))⟩

/-- The rounded-cap right normal map is continuous. -/
theorem continuous_coordinateExteriorRoundedCapRightNormalMap :
    Continuous coordinateExteriorRoundedCapRightNormalMap :=
  Continuous.subtype_mk contMDiff_coordinateExteriorRoundedCapRightCharacter.continuous _

/-- The pullback of the nonzero-complex power cover along the rounded-cap right normal map. -/
@[nolint unusedArguments]
abbrev CoordinateExteriorRoundedCapPowerPullback (m : ℕ) [NeZero m] :=
  TopologicalCoverPullback (nonzeroComplexPow m) coordinateExteriorRoundedCapRightNormalMap

/-- Projection from the rounded-cap power pullback to the rounded cap. -/
def coordinateExteriorRoundedCapPowerPullbackProj (m : ℕ) [NeZero m] :
    CoordinateExteriorRoundedCapPowerPullback m →
      CollaredCutSide coordinateClosedCapZero :=
  topologicalCoverPullbackProj (nonzeroComplexPow m)
    coordinateExteriorRoundedCapRightNormalMap

/-- The rounded-cap power-pullback projection is a covering map. -/
theorem isCoveringMap_coordinateExteriorRoundedCapPowerPullbackProj
    (m : ℕ) [NeZero m] :
    IsCoveringMap (coordinateExteriorRoundedCapPowerPullbackProj m) :=
  IsCoveringMap.pullback (isCoveringMap_nonzeroComplexPow m)
    continuous_coordinateExteriorRoundedCapRightNormalMap

/-- The charted space pulled back along the rounded-cap power-cover projection. -/
@[instance_reducible]
def coordinateExteriorRoundedCapPowerPullbackChartedSpace (m : ℕ) [NeZero m] :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateExteriorRoundedCapPowerPullback m) := by
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  exact IsCoveringMap.pullbackChartedSpace
    (isCoveringMap_coordinateExteriorRoundedCapPowerPullbackProj m)

/-- The rounded-cap power pullback is a common-model smooth manifold with boundary. -/
theorem isManifold_coordinateExteriorRoundedCapPowerPullback
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRoundedCapPowerPullback m) := by
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide coordinateClosedCapZero) :=
    isManifold_coordinateUnlinkExteriorRoundedHemisphereClosedCap
  let _ := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
  exact IsCoveringMap.isManifold_pullbackChartedSpace
    coordinateUnlinkExteriorModel ∞
    (isCoveringMap_coordinateExteriorRoundedCapPowerPullbackProj m)

/-- The rounded-cap power-pullback projection is a local diffeomorphism. -/
theorem isLocalDiffeomorph_coordinateExteriorRoundedCapPowerPullbackProj
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
    letI := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateExteriorRoundedCapPowerPullbackProj m) := by
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide coordinateClosedCapZero) :=
    isManifold_coordinateUnlinkExteriorRoundedHemisphereClosedCap
  let _ := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRoundedCapPowerPullback m) :=
    isManifold_coordinateExteriorRoundedCapPowerPullback m
  exact IsCoveringMap.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
    (isCoveringMap_coordinateExteriorRoundedCapPowerPullbackProj m)

/-- The pulled-back model boundary is exactly the projection preimage of the rounded equator. -/
theorem coordinateExteriorRoundedCapPowerPullback_boundary
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CollaredCutSide coordinateClosedCapZero) :=
      isManifold_coordinateUnlinkExteriorRoundedHemisphereClosedCap
    letI := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRoundedCapPowerPullback m) :=
      isManifold_coordinateExteriorRoundedCapPowerPullback m
    coordinateUnlinkExteriorModel.boundary
        (CoordinateExteriorRoundedCapPowerPullback m) =
      coordinateExteriorRoundedCapPowerPullbackProj m ⁻¹'
        ((Subtype.val : CollaredCutSide coordinateClosedCapZero → Sphere 4) ⁻¹'
          coordinateEquator) := by
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide coordinateClosedCapZero) :=
    isManifold_coordinateUnlinkExteriorRoundedHemisphereClosedCap
  let _ := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRoundedCapPowerPullback m) :=
    isManifold_coordinateExteriorRoundedCapPowerPullback m
  rw [← coordinateUnlinkExteriorRoundedHemisphereClosedCap_boundary]
  exact
    ((isLocalDiffeomorph_coordinateExteriorRoundedCapPowerPullbackProj m)
      |>.preimage_boundary (by simp)).symm

/-- The labelled-family map into the rounded-cap power pullback. -/
def coordinateExteriorRoundedCapPowerTrivializationForward
    (m : ℕ) [NeZero m]
    (p : ZMod m × CollaredCutSide coordinateClosedCapZero) :
    CoordinateExteriorRoundedCapPowerPullback m :=
  ⟨(p.2, ⟨coordinateExteriorRoundedCapFamilyPowerRoot m p,
    coordinateExteriorRoundedCapPowerRootTranslate_ne_zero m p.1 p.2⟩), by
      apply Subtype.ext
      exact (coordinateExteriorRoundedCapPowerRootTranslate_pow m p.1 p.2).symm⟩

/-- The labelled-family power-pullback map is continuous. -/
theorem continuous_coordinateExteriorRoundedCapPowerTrivializationForward
    (m : ℕ) [NeZero m] :
    Continuous (coordinateExteriorRoundedCapPowerTrivializationForward m) := by
  let _ := coordinateExteriorRoundedCapFamilyChartedSpace m
  have hroot := (contMDiff_coordinateExteriorRoundedCapFamilyPowerRoot m).continuous
  exact Continuous.subtype_mk
    (continuous_snd.prodMk (Continuous.subtype_mk hroot _)) _

/-- The labelled-family power-pullback map is injective. -/
theorem injective_coordinateExteriorRoundedCapPowerTrivializationForward
    (m : ℕ) [NeZero m] :
    Injective (coordinateExteriorRoundedCapPowerTrivializationForward m) := by
  rintro ⟨a, q⟩ ⟨b, r⟩ h
  have hbase := congrArg (coordinateExteriorRoundedCapPowerPullbackProj m) h
  change q = r at hbase
  subst r
  have hroot := congrArg
    (fun z : CoordinateExteriorRoundedCapPowerPullback m ↦ z.1.2.1) h
  have hcoeff :
      (((standardRootsOfUnityZModMulEquiv m
        (Multiplicative.ofAdd
          (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m))).1 : ℂˣ) : ℂ) =
      (((standardRootsOfUnityZModMulEquiv m
        (Multiplicative.ofAdd
          (b - coordinateUnlinkExteriorPlanarSmoothNeckShift m))).1 : ℂˣ) : ℂ) := by
    apply mul_right_cancel₀ (coordinateExteriorRoundedCapPowerRoot_ne_zero m q)
    exact hroot
  have hroots :
      standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd
            (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m)) =
        standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd
            (b - coordinateUnlinkExteriorPlanarSmoothNeckShift m)) := by
    apply Subtype.ext
    apply Units.ext
    exact hcoeff
  have habsub :
      a - coordinateUnlinkExteriorPlanarSmoothNeckShift m =
        b - coordinateUnlinkExteriorPlanarSmoothNeckShift m :=
    Multiplicative.ofAdd.injective
      ((standardRootsOfUnityZModMulEquiv m).injective hroots)
  have hab := congrArg
    (fun z ↦ z + coordinateUnlinkExteriorPlanarSmoothNeckShift m) habsub
  exact Prod.ext (by simpa using hab) rfl

/-- The labelled-family power-pullback map is surjective. -/
theorem surjective_coordinateExteriorRoundedCapPowerTrivializationForward
    (m : ℕ) [NeZero m] :
    Surjective (coordinateExteriorRoundedCapPowerTrivializationForward m) := by
  intro z
  obtain ⟨a, ha⟩ := exists_coordinateExteriorRoundedCapPowerRootTranslate_eq m
    z.1.1 z.1.2.1 z.1.2.2 (by
      exact (congrArg Subtype.val z.2).symm)
  refine ⟨(a, z.1.1), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact ha

/-- The labelled-family power-pullback map is a local homeomorphism. -/
theorem isLocalHomeomorph_coordinateExteriorRoundedCapPowerTrivializationForward
    (m : ℕ) [NeZero m] :
    IsLocalHomeomorph (coordinateExteriorRoundedCapPowerTrivializationForward m) := by
  have hcomp : IsLocalHomeomorph
      (coordinateExteriorRoundedCapPowerPullbackProj m ∘
        coordinateExteriorRoundedCapPowerTrivializationForward m) := by
    simpa [Function.comp_def, coordinateExteriorRoundedCapPowerPullbackProj,
      coordinateExteriorRoundedCapPowerTrivializationForward] using
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := CollaredCutSide coordinateClosedCapZero))
  exact hcomp.of_comp
    (isCoveringMap_coordinateExteriorRoundedCapPowerPullbackProj m).isLocalHomeomorph
    (continuous_coordinateExteriorRoundedCapPowerTrivializationForward m)

/-- The labelled rounded-cap family is homeomorphic to the power pullback. -/
noncomputable def coordinateExteriorRoundedCapPowerTrivializationHomeomorph
    (m : ℕ) [NeZero m] :
    (ZMod m × CollaredCutSide coordinateClosedCapZero) ≃ₜ
      CoordinateExteriorRoundedCapPowerPullback m :=
  (isLocalHomeomorph_coordinateExteriorRoundedCapPowerTrivializationForward m)
    |>.toHomeomorphOfBijective
      ⟨injective_coordinateExteriorRoundedCapPowerTrivializationForward m,
        surjective_coordinateExteriorRoundedCapPowerTrivializationForward m⟩

/-- The labelled rounded-cap family is diffeomorphic to the power pullback. -/
noncomputable def coordinateExteriorRoundedCapPowerTrivializationDiffeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateExteriorRoundedCapFamilyChartedSpace m
    letI := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
    (ZMod m × CollaredCutSide coordinateClosedCapZero) ≃ₘ^∞⟮
      coordinateUnlinkExteriorModel, coordinateUnlinkExteriorModel⟯
      CoordinateExteriorRoundedCapPowerPullback m := by
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide coordinateClosedCapZero) :=
    isManifold_coordinateUnlinkExteriorRoundedHemisphereClosedCap
  let _ := coordinateExteriorRoundedCapFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × CollaredCutSide coordinateClosedCapZero) :=
    isManifold_discreteProductChartedSpace coordinateUnlinkExteriorModel ∞
      (ZMod m) (CollaredCutSide coordinateClosedCapZero)
  let _ := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRoundedCapPowerPullback m) :=
    isManifold_coordinateExteriorRoundedCapPowerPullback m
  let hsnd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × CollaredCutSide coordinateClosedCapZero →
        CollaredCutSide coordinateClosedCapZero) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := CollaredCutSide coordinateClosedCapZero))
  exact diffeomorphOfHomeomorphOverDiffeomorph
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    Prod.snd (coordinateExteriorRoundedCapPowerPullbackProj m) hsnd
    (isLocalDiffeomorph_coordinateExteriorRoundedCapPowerPullbackProj m)
    (Diffeomorph.refl coordinateUnlinkExteriorModel
      (CollaredCutSide coordinateClosedCapZero) ∞)
    (coordinateExteriorRoundedCapPowerTrivializationHomeomorph m) (fun _ ↦ rfl)

/-- The common-model Euclidean four-ball family is diffeomorphic to the rounded-cap family. -/
noncomputable def coordinateExteriorRoundedBallFamilyCapDiffeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    letI := coordinateExteriorRoundedCapFamilyChartedSpace m
    (ZMod m × EuclideanFourBall) ≃ₘ^∞⟮
      coordinateUnlinkExteriorModel, coordinateUnlinkExteriorModel⟯
      (ZMod m × CollaredCutSide coordinateClosedCapZero) := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ EuclideanFourBall :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBall
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide coordinateClosedCapZero) :=
    isManifold_coordinateUnlinkExteriorRoundedHemisphereClosedCap
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBall) :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily m
  let _ := coordinateExteriorRoundedCapFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × CollaredCutSide coordinateClosedCapZero) :=
    isManifold_discreteProductChartedSpace coordinateUnlinkExteriorModel ∞
      (ZMod m) (CollaredCutSide coordinateClosedCapZero)
  let hsndSource : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × EuclideanFourBall → EuclideanFourBall) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := EuclideanFourBall))
  let hsndTarget : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × CollaredCutSide coordinateClosedCapZero →
        CollaredCutSide coordinateClosedCapZero) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := CollaredCutSide coordinateClosedCapZero))
  let F : (ZMod m × EuclideanFourBall) ≃ₜ
      (ZMod m × CollaredCutSide coordinateClosedCapZero) :=
    (Homeomorph.refl (ZMod m)).prodCongr
      euclideanFourBallRoundedHemisphereDiffeomorph.toHomeomorph
  exact diffeomorphOfHomeomorphOverDiffeomorph
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    Prod.snd Prod.snd hsndSource hsndTarget
    euclideanFourBallRoundedHemisphereDiffeomorph F (fun _ ↦ rfl)

/-- The common-model Euclidean four-ball family is diffeomorphic to the rounded-cap power
pullback. -/
noncomputable def coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph
    (m : ℕ) [NeZero m] :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    letI := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
    (ZMod m × EuclideanFourBall) ≃ₘ^∞⟮
      coordinateUnlinkExteriorModel, coordinateUnlinkExteriorModel⟯
      CoordinateExteriorRoundedCapPowerPullback m := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ := coordinateExteriorRoundedCapFamilyChartedSpace m
  let _ := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
  exact (coordinateExteriorRoundedBallFamilyCapDiffeomorph m).trans
    (coordinateExteriorRoundedCapPowerTrivializationDiffeomorph m)

/-- The exact shifted equatorial lift into the rounded-cap power pullback. -/
def coordinateExteriorRoundedCapEquatorPowerLift
    (m : ℕ) [NeZero m] (a : ZMod m) (s : Sphere 3) :
    CoordinateExteriorRoundedCapPowerPullback m :=
  ⟨(roundedHemisphereClosedCapBoundaryCollar
      (s, euclideanFourBallCollarZero),
    ⟨equatorUnlinkPowerRootTranslate m
      (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) s,
      equatorUnlinkPowerRootTranslate_ne_zero m
        (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) s⟩), by
    apply Subtype.ext
    change standardUnlinkRightDisplacementComplex
        ((roundedHemisphereClosedCapBoundaryCollar
          (s, euclideanFourBallCollarZero) :
            CollaredCutSide coordinateClosedCapZero) : Sphere 4) =
      equatorUnlinkPowerRootTranslate m
        (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) s ^ m
    rw [equatorUnlinkPowerRootTranslate_pow]
    rw [roundedHemisphereClosedCapBoundaryCollar_coe]
    rw [show roundedHemisphereClosedCapCollarAmbient
        (s, euclideanFourBallCollarZero) = equatorSphereMap s by
      rw [roundedHemisphereClosedCapCollarAmbient]
      rw [show roundedHemisphereEquatorTime euclideanFourBallCollarZero =
          ⟨0, show (0 : ℝ) ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) by norm_num⟩ by
        apply Subtype.ext
        simp]
      exact equatorCollarSphereMap_zero s]
    exact standardUnlinkRightDisplacementComplex_equatorSphereMap s⟩

/-- The ball-family trivialization sends its collar zero section to the exact equatorial lift. -/
@[simp]
theorem coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph_boundary
    (m : ℕ) [NeZero m] (a : ZMod m) (s : Sphere 3) :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    letI := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
    coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m
        (a, euclideanFourBallSmoothCollar (s, euclideanFourBallCollarZero)) =
      coordinateExteriorRoundedCapEquatorPowerLift m a s := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ := coordinateExteriorRoundedCapFamilyChartedSpace m
  let _ := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
  apply Subtype.ext
  apply Prod.ext
  · exact euclideanFourBallRoundedHemisphereDiffeomorph_boundaryCollar
      (s, euclideanFourBallCollarZero)
  · apply Subtype.ext
    change coordinateExteriorRoundedCapPowerRootTranslate m a
        (euclideanFourBallRoundedHemisphereDiffeomorph
          (coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar
            (s, euclideanFourBallCollarZero))) = _
    rw [euclideanFourBallRoundedHemisphereDiffeomorph_boundaryCollar]
    exact coordinateExteriorRoundedCapPowerRootTranslate_boundary m a s

end SplittingSpheres
