/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorRightTubeStandardSmoothStructure
public import SplittingSpheres.Handlebody.CoordinateExteriorRoundedCapPowerTrivialization
public import
  SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckSmoothCappingDiffeomorphismRecognition

import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCompactCoordinateCaps
import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckSmoothCappingRadialBoundary
import SplittingSpheres.Handlebody.CoordinateExteriorPowerCompactness
import SplittingSpheres.Geometry.ExteriorCompression
import all SplittingSpheres.Handlebody.CoordinateExteriorRoundedCapPowerTrivialization
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Direct right smooth-capping recognition by the standard right-tube exterior

This file identifies the direct smooth capping of the compact right planar-neck cut with the
right-tube power pullback equipped with its literal standard-collar smooth structure.  The
comparison is built pointwise from the compact-cut inclusion and the rounded-cap power
trivialization.  Smoothness is checked on the signed seam and the two off-seam generators of the
pushout atlas; no atlas is transported through the comparison homeomorphism.

The result concerns only the direct standard-collar atlas on the right-tube pullback.  It makes no
comparison with the separate radial one-handle atlas.
-/

@[expose] public section

open Function Metric Set Topology TopologicalSpace WithLp
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

variable (m : ℕ) [NeZero m]

private theorem contMDiff_to_signedSeamInterval_of_value
    {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H)
    (f : M → EquatorCollarInterval)
    (hf : Continuous f)
    (hvalue : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞
      (fun x ↦ (f x).1 : M → ℝ)) :
    letI := signedSeamIntervalChartedSpace
    ContMDiff I (modelWithCornersEuclideanHalfSpace 1) ∞ f := by
  let _ := signedSeamIntervalChartedSpace
  let _ : IsManifold (modelWithCornersEuclideanHalfSpace 1) ∞
      EquatorCollarInterval := isManifold_signedSeamInterval
  have hraw : ContMDiff I (modelWithCornersSelf ℝ (Fin 1 → ℝ)) ∞
      (fun x : M ↦ fun _ : Fin 1 ↦ (f x).1 + 1 / 2) := by
    rw [contMDiff_pi_space]
    intro i
    fin_cases i
    exact hvalue.add contMDiff_const
  have htoLp : ContMDiff (modelWithCornersSelf ℝ (Fin 1 → ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ∞
      (WithLp.toLp 2) :=
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin 1 ↦ ℝ)).symm.toContinuousLinearMap.contMDiff
  have hcoord : ContMDiff I
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ∞
      (fun x ↦ WithLp.toLp 2 (fun _ : Fin 1 ↦ (f x).1 + 1 / 2)) :=
    htoLp.comp hraw
  intro x
  rw [contMDiffAt_iff_target_of_mem_source
    (mem_chart_source (EuclideanHalfSpace 1) (f x))]
  refine ⟨hf.continuousAt, ?_⟩
  apply (hcoord x).congr_of_eventuallyEq
  filter_upwards [] with y
  rw [extChartAt_coe]
  rw [isOpenEmbedding_signedSeamIntervalHalfSpaceChart.singletonChartedSpace_chartAt_eq]
  ext i
  fin_cases i
  change (signedSeamIntervalHalfSpaceChart (f y)).val 0 =
    (WithLp.toLp 2 (fun _ : Fin 1 ↦ (f y).1 + 1 / 2) :
      EuclideanSpace ℝ (Fin 1)) 0
  rw [signedSeamIntervalHalfSpaceChart_apply, PiLp.toLp_apply]

private abbrev NaturalSignedSeamModel :=
  (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
    (modelWithCornersSelf ℝ ℝ)

@[instance_reducible]
private noncomputable def naturalSignedSeamChartedSpace :
    ChartedSpace
      (ModelProd (EuclideanSpace ℝ (Fin 3)) ℝ)
      (Sphere 3 × EquatorCollarInterval) := inferInstance

private theorem contMDiff_identity_naturalSigned_to_common :
    letI := naturalSignedSeamChartedSpace
    letI := signedSeamCommonModelChartedSpace
    ContMDiff NaturalSignedSeamModel coordinateUnlinkExteriorModel ∞
      (id : Sphere 3 × EquatorCollarInterval →
        Sphere 3 × EquatorCollarInterval) := by
  let _ := naturalSignedSeamChartedSpace
  let _ := signedSeamIntervalChartedSpace
  let _ := signedSeamCollarBoundaryChartedSpace
  let _ := signedSeamCommonModelChartedSpace
  have hfst : ContMDiff NaturalSignedSeamModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ p.1) := contMDiff_fst
  have hsnd : ContMDiff NaturalSignedSeamModel
      (modelWithCornersEuclideanHalfSpace 1) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ p.2) := by
    apply contMDiff_to_signedSeamInterval_of_value
      NaturalSignedSeamModel _ continuous_snd
    exact contMDiff_subtype_val.comp contMDiff_snd
  have hboundary : ContMDiff NaturalSignedSeamModel
      coordinateUnlinkBoundaryCollarModel ∞
      (id : Sphere 3 × EquatorCollarInterval →
        Sphere 3 × EquatorCollarInterval) := by
    exact (ContMDiff.prodMk hfst hsnd).congr fun _ ↦ rfl
  exact (signedSeamCommonBoundaryIdentityDiffeomorph.symm.contMDiff.comp
    hboundary).congr fun _ ↦ rfl

private theorem contMDiff_identity_common_to_naturalSigned :
    letI := signedSeamCommonModelChartedSpace
    letI := naturalSignedSeamChartedSpace
    ContMDiff coordinateUnlinkExteriorModel NaturalSignedSeamModel ∞
      (id : Sphere 3 × EquatorCollarInterval →
        Sphere 3 × EquatorCollarInterval) := by
  let _ := signedSeamCommonModelChartedSpace
  let _ := signedSeamIntervalChartedSpace
  let _ := signedSeamCollarBoundaryChartedSpace
  let _ := naturalSignedSeamChartedSpace
  have hcommonBoundary := signedSeamCommonBoundaryIdentityDiffeomorph.contMDiff
  have hfst : ContMDiff coordinateUnlinkExteriorModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ p.1) :=
    (contMDiff_fst.comp hcommonBoundary).congr fun _ ↦ rfl
  have hsnd : ContMDiff coordinateUnlinkExteriorModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ (p.2.1 : ℝ)) :=
    contMDiff_signedSeamTime
  have hsndSub : ContMDiff coordinateUnlinkExteriorModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ p.2) := by
    rw [← ContMDiff.subtypeVal_comp_iff equatorCollarIntervalOpens]
    exact hsnd
  exact (ContMDiff.prodMk hfst hsndSub).congr fun _ ↦ rfl

private noncomputable def signedSeamCommonNaturalIdentityDiffeomorph :
    letI := signedSeamCommonModelChartedSpace
    letI := naturalSignedSeamChartedSpace
    (Sphere 3 × EquatorCollarInterval) ≃ₘ^∞⟮
      coordinateUnlinkExteriorModel, NaturalSignedSeamModel⟯
      (Sphere 3 × EquatorCollarInterval) := by
  let _ := signedSeamCommonModelChartedSpace
  let _ := naturalSignedSeamChartedSpace
  exact
    { toEquiv := Equiv.refl _
      contMDiff_toFun := contMDiff_identity_common_to_naturalSigned
      contMDiff_invFun := contMDiff_identity_naturalSigned_to_common }

private def equatorCollarIntervalNegDiffeomorph :
    EquatorCollarInterval ≃ₘ^∞⟮
      modelWithCornersSelf ℝ ℝ, modelWithCornersSelf ℝ ℝ⟯
      EquatorCollarInterval where
  toEquiv :=
    coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph.toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff equatorCollarIntervalOpens _).mp
    have h : ContDiff ℝ ∞ (fun t : ℝ ↦ -t) := by fun_prop
    simpa [coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph,
      Function.comp_def] using h.comp_contMDiff contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff equatorCollarIntervalOpens _).mp
    have h : ContDiff ℝ ∞ (fun t : ℝ ↦ -t) := by fun_prop
    simpa [coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph,
      Function.comp_def] using h.comp_contMDiff contMDiff_subtype_val

private def naturalSignedSeamFlipDiffeomorph :
    (Sphere 3 × EquatorCollarInterval) ≃ₘ^∞⟮
      NaturalSignedSeamModel, NaturalSignedSeamModel⟯
      (Sphere 3 × EquatorCollarInterval) :=
  (Diffeomorph.refl
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (Sphere 3) ∞).prodCongr equatorCollarIntervalNegDiffeomorph

private theorem isLocalDiffeomorph_equatorCollarNeg_common :
    letI := signedSeamCommonModelChartedSpace
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦
        equatorCollarSphereMap
          (p.1,
            coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2)) := by
  let _ := signedSeamCommonModelChartedSpace
  let _ := naturalSignedSeamChartedSpace
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  intro p
  have h₀ := signedSeamCommonNaturalIdentityDiffeomorph.isLocalDiffeomorph p
  have h₁ := naturalSignedSeamFlipDiffeomorph.isLocalDiffeomorph
    (signedSeamCommonNaturalIdentityDiffeomorph p)
  have h₀₁ := h₀.comp NaturalSignedSeamModel
    (Sphere 3 × EquatorCollarInterval) h₁
  have h₂ := equatorCollarDiffeomorph.isLocalDiffeomorph
    (naturalSignedSeamFlipDiffeomorph
      (signedSeamCommonNaturalIdentityDiffeomorph p))
  have h₀₁₂ := h₀₁.comp
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    EquatorCollarRegion h₂
  have h₃ := isLocalDiffeomorph_opensSubtypeVal
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    equatorCollarRegion
    (equatorCollarDiffeomorph
      (naturalSignedSeamFlipDiffeomorph
        (signedSeamCommonNaturalIdentityDiffeomorph p)))
  have h₀₁₂₃ := h₀₁₂.comp
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (Sphere 4) h₃
  have h₄ :=
    standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph
      |>.isLocalDiffeomorph
        (((Subtype.val : EquatorCollarRegion → Sphere 4) ∘
          equatorCollarDiffeomorph ∘ naturalSignedSeamFlipDiffeomorph ∘
          signedSeamCommonNaturalIdentityDiffeomorph) p)
  have hcomp := h₀₁₂₃.comp coordinateUnlinkExteriorModel (Sphere 4) h₄
  change IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
    coordinateUnlinkExteriorModel ∞
    (fun x ↦
      ((equatorCollarDiffeomorph
        (naturalSignedSeamFlipDiffeomorph
          (signedSeamCommonNaturalIdentityDiffeomorph x)) :
            EquatorCollarRegion) : Sphere 4)) p
  exact hcomp

private theorem rightCapping_isLocalDiffeomorphAt_congr_of_eqOn_open
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace CoordinateUnlinkExteriorModelSpace M]
    [ChartedSpace CoordinateUnlinkExteriorModelSpace N]
    {f g : M → N} {x : M}
    (hg : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ g x)
    (W : Set M) (hW : IsOpen W) (hxW : x ∈ W)
    (heq : EqOn f g W) :
    IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ f x := by
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp <|
    hg.contMDiffAt.continuousAt.preimage_mem_nhds <|
      hg.localInverse.open_source.mem_nhds hg.localInverse_mem_source
  let Ψ := hg.localInverse.symm
  let U := W ∩ V
  have hU : IsOpen U := hW.inter hVopen
  let q := Ψ.toOpenPartialHomeomorph.restrOpen U hU
  have hEq : EqOn f q q.source := by
    intro y hy
    change y ∈ Ψ.source ∩ U at hy
    have hyTarget : y ∈ hg.localInverse.target := hy.1
    have hgySource : g y ∈ hg.localInverse.source := hVsub hy.2.2
    apply (heq hy.2.1).trans
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

private theorem rightCapping_isLocalDiffeomorphAt_congr_of_eventuallyEq
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
  exact rightCapping_isLocalDiffeomorphAt_congr_of_eqOn_open hg W hWopen hxW
    (fun y hy ↦ hWsub hy)

private theorem rightCapping_reflect_isLocalDiffeomorph
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
  apply rightCapping_isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp
  filter_upwards [hpx.localInverse_eventuallyEq_left.comp_tendsto
    hf.continuousAt] with y hy
  simpa only [Function.comp_apply, id_eq] using hy.symm

/-- The underlying sphere point of the compact right cut avoids the open right tube. -/
theorem compactNeckRightCut_mem_coordinateExteriorRightTubeClosedCarrier
    (q : CompactNeckRightCut m) :
    q.1.1.1.1 ∈ coordinateExteriorRightTubeClosedCarrier := by
  rw [coordinateExteriorRightTubeClosedCarrier_eq_compl_openTube]
  intro hright
  exact q.1.1.1.2 (Or.inr hright)

/-- Include the compact right-cut body in the right-tube power pullback. -/
def coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap
    (q : CompactNeckRightCut m) :
    CoordinateExteriorRightTubePowerPullback m :=
  ⟨(⟨q.1.1.1.1, compactNeckRightCut_mem_coordinateExteriorRightTubeClosedCarrier m q⟩,
      q.1.1.2), by
    apply Subtype.ext
    exact congrArg Subtype.val q.1.2⟩

/-- The compact-cut body map is injective. -/
theorem coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap_injective :
    Injective (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap m) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z ↦ (z.1.1 : Sphere 4)) h
  · exact congrArg (fun z ↦ z.1.2) h

/-- The closed negative cap lies in the closed right-tube exterior. -/
theorem coordinateClosedCapZero_subset_rightTubeClosedCarrier :
    coordinateClosedCapZero ⊆ coordinateExteriorRightTubeClosedCarrier := by
  intro q hq
  rw [coordinateExteriorRightTubeClosedCarrier_eq_compl_openTube]
  intro htube
  have hq3 : q.1 3 ≤ 0 := by
    rw [coordinateClosedCapZero, mem_compl_iff,
      mem_coordinateOpenCap_one] at hq
    exact le_of_not_gt hq
  change dist (standardUnlinkNormalProjection q)
      (standardUnlinkNormalCenter 1) < 1 / 8 at htube
  rw [dist_eq_norm] at htube
  let v := standardUnlinkNormalProjection q - standardUnlinkNormalCenter 1
  have hsq : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    simpa [Fin.sum_univ_succ] using EuclideanSpace.real_norm_sq_eq v
  have hv0 : v 0 = q.1 3 - 1 / 2 := by
    simp [v, standardUnlinkHeight]
  have hv1sq : 0 ≤ v 1 ^ 2 := sq_nonneg _
  have hvnorm_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
  rw [hv0] at hsq
  nlinarith

/-- Include the rounded-cap power pullback in the right-tube power pullback. -/
def coordinateExteriorRoundedCapPowerPullbackToRightTube
    (z : CoordinateExteriorRoundedCapPowerPullback m) :
    CoordinateExteriorRightTubePowerPullback m :=
  ⟨(⟨z.1.1.1,
        coordinateClosedCapZero_subset_rightTubeClosedCarrier z.1.1.2⟩,
      z.1.2), by
    apply Subtype.ext
    exact congrArg Subtype.val z.2⟩

/-- The rounded-cap pullback inclusion is injective. -/
theorem coordinateExteriorRoundedCapPowerPullbackToRightTube_injective :
    Injective (coordinateExteriorRoundedCapPowerPullbackToRightTube m) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z ↦ (z.1.1 : Sphere 4)) h
  · exact congrArg (fun z ↦ z.1.2) h

/-- The rounded-cap pullback inclusion is continuous. -/
theorem continuous_coordinateExteriorRoundedCapPowerPullbackToRightTube :
    Continuous (coordinateExteriorRoundedCapPowerPullbackToRightTube m) := by
  unfold coordinateExteriorRoundedCapPowerPullbackToRightTube
  apply Continuous.subtype_mk
  fun_prop

/-- Map the labelled rounded four-ball family into the right-tube power pullback. -/
def coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap
    (z : ZMod m × EuclideanFourBall) :
    CoordinateExteriorRightTubePowerPullback m :=
  coordinateExteriorRoundedCapPowerPullbackToRightTube m
    (coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m z)

/-- The labelled rounded-cap map is injective. -/
theorem coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap_injective :
    Injective (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap m) :=
  (coordinateExteriorRoundedCapPowerPullbackToRightTube_injective m).comp
    (coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m).injective

/-- The compact-cut body map as a continuous map. -/
def coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyContinuousMap :
    C(CompactNeckRightCut m, CoordinateExteriorRightTubePowerPullback m) where
  toFun := coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap m
  continuous_toFun := by
    unfold coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap
    apply Continuous.subtype_mk
    fun_prop

/-- The labelled rounded-cap map as a continuous map. -/
def coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapContinuousMap :
    C(ZMod m × EuclideanFourBall,
      CoordinateExteriorRightTubePowerPullback m) where
  toFun := coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap m
  continuous_toFun := by
    let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    let _ := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
    exact (continuous_coordinateExteriorRoundedCapPowerPullbackToRightTube m).comp
      (coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m).continuous

private theorem nonnegative_mem_coordinateUnlinkExterior
    (q : Sphere 4) (hq : q ∈ coordinateExteriorRightTubeClosedCarrier)
    (h3 : 0 ≤ q.1 3) :
    q ∈ coordinateUnlinkExterior (1 / 8 : ℝ) := by
  rw [coordinateUnlinkExterior, mem_compl_iff]
  intro htubes
  rcases htubes with hleft | hright
  · change dist (standardUnlinkNormalProjection q)
        (standardUnlinkNormalCenter 0) < 1 / 8 at hleft
    rw [dist_eq_norm] at hleft
    let v := standardUnlinkNormalProjection q - standardUnlinkNormalCenter 0
    have hsq : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
      simpa [Fin.sum_univ_succ] using EuclideanSpace.real_norm_sq_eq v
    have hv0 : v 0 = q.1 3 + 1 / 2 := by
      simp [v, standardUnlinkHeight]
    have hv1sq : 0 ≤ v 1 ^ 2 := sq_nonneg _
    have hvnorm_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
    rw [hv0] at hsq
    nlinarith
  · rw [coordinateExteriorRightTubeClosedCarrier_eq_compl_openTube] at hq
    exact hq hright

private def targetToBodyOfNonnegative
    (z : CoordinateExteriorRightTubePowerPullback m)
    (hz : 0 ≤ (z.1.1.1 : Sphere 4).1 3) : CompactNeckRightCut m :=
  ⟨⟨(⟨z.1.1.1,
        nonnegative_mem_coordinateUnlinkExterior z.1.1.1 z.1.1.2 hz⟩,
      z.1.2), by
    apply Subtype.ext
    exact congrArg Subtype.val z.2⟩, by
    rw [coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier_eq_preimage_compl_cap_zero]
    change z.1.1.1 ∈ (coordinateOpenCap 0)ᶜ
    rw [mem_compl_iff, mem_coordinateOpenCap_zero]
    exact not_lt_of_ge hz⟩

private theorem
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap_targetToBodyOfNonnegative
    (z : CoordinateExteriorRightTubePowerPullback m)
    (hz : 0 ≤ (z.1.1.1 : Sphere 4).1 3) :
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap m
        (targetToBodyOfNonnegative m z hz) = z := by
  apply Subtype.ext
  rfl

private def targetToCapOfNonpositive
    (z : CoordinateExteriorRightTubePowerPullback m)
    (hz : (z.1.1.1 : Sphere 4).1 3 ≤ 0) :
    CoordinateExteriorRoundedCapPowerPullback m :=
  ⟨(⟨z.1.1.1, by
      rw [coordinateClosedCapZero, mem_compl_iff,
        mem_coordinateOpenCap_one]
      exact not_lt_of_ge hz⟩,
    z.1.2), by
    apply Subtype.ext
    exact congrArg Subtype.val z.2⟩

private theorem coordinateExteriorRoundedCapPowerPullbackToRightTube_targetToCapOfNonpositive
    (z : CoordinateExteriorRightTubePowerPullback m)
    (hz : (z.1.1.1 : Sphere 4).1 3 ≤ 0) :
    coordinateExteriorRoundedCapPowerPullbackToRightTube m
        (targetToCapOfNonpositive m z hz) = z := by
  apply Subtype.ext
  rfl

/-- The body and rounded-cap maps jointly cover the right-tube power pullback. -/
theorem coordinateExteriorPlanarNeckRightSmoothCappingRightTube_cover :
    range (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyContinuousMap m) ∪
        range (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapContinuousMap m) =
      univ := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
  rw [eq_univ_iff_forall]
  intro z
  by_cases hz : (z.1.1.1 : Sphere 4).1 3 ≤ 0
  · refine Or.inr ⟨
      (coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m).symm
        (targetToCapOfNonpositive m z hz), ?_⟩
    change coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap m _ = z
    rw [coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap,
      (coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m).apply_symm_apply]
    exact coordinateExteriorRoundedCapPowerPullbackToRightTube_targetToCapOfNonpositive m z hz
  · have hz' : 0 ≤ (z.1.1.1 : Sphere 4).1 3 := le_of_not_ge hz
    exact Or.inl ⟨targetToBodyOfNonnegative m z hz',
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap_targetToBodyOfNonnegative
        m z hz'⟩

private theorem rightCapping_attaching_match_base
    (a : ZMod m) (s : Sphere 3) :
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap m
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m (a, s)) =
      coordinateExteriorRoundedCapPowerPullbackToRightTube m
        (coordinateExteriorRoundedCapEquatorPowerLift m a s) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change (compactNeckRightBoundaryCollarMap m
        (a, s, euclideanFourBallCollarZero)).1.1 =
      (roundedHemisphereClosedCapBoundaryCollar
        (s, euclideanFourBallCollarZero) : Sphere 4)
    simp only [compactNeckRightBoundaryCollarMap,
      compactNeckRightHalfParameter,
      coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_eq_raw,
      coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap,
      euclideanFourBallCollarZero_value,
      equatorUnlinkPowerCollarLift_zero, ne_eq,
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
    change (compactNeckRightBoundaryCollarMap m
        (a, s, euclideanFourBallCollarZero)).1.2.1 =
      equatorUnlinkPowerRootTranslate m
        (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) s
    simp only [compactNeckRightBoundaryCollarMap,
      compactNeckRightHalfParameter,
      coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_eq_raw,
      coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap,
      euclideanFourBallCollarZero_value,
      equatorUnlinkPowerCollarLift_zero, ne_eq]
    rw [standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_equatorUnlinkPowerLift]
    exact equatorUnlinkClosedTubeExteriorPowerLift_powerCoordinate
      m (a - coordinateUnlinkExteriorPlanarSmoothNeckShift m) s

/-- The body and rounded-cap maps agree on the labelled attaching sphere family. -/
theorem coordinateExteriorPlanarNeckRightSmoothCappingRightTube_attaching
    (p : ZMod m × Sphere 3) :
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyContinuousMap m
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m p) =
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapContinuousMap m
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m p) := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
  change coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap m _ =
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap m _
  rw [show coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m p =
      (p.1, euclideanFourBallSmoothCollar
        (p.2, euclideanFourBallCollarZero)) by rfl]
  rw [coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap,
    coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph_boundary]
  exact rightCapping_attaching_match_base m p.1 p.2

private theorem exists_ball_attaching_of_cap_base_mem_equator
    (y : ZMod m × EuclideanFourBall)
    (hy : ((coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m y).1.1.1 :
      Sphere 4) ∈ coordinateEquator) :
    ∃ p : ZMod m × Sphere 3,
      coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m p = y := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBall) :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily m
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide coordinateClosedCapZero) :=
    isManifold_coordinateUnlinkExteriorRoundedHemisphereClosedCap
  let _ := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRoundedCapPowerPullback m) :=
    isManifold_coordinateExteriorRoundedCapPowerPullback m
  have hyTargetBoundary :
      coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m y ∈
        coordinateUnlinkExteriorModel.boundary
          (CoordinateExteriorRoundedCapPowerPullback m) := by
    rw [coordinateExteriorRoundedCapPowerPullback_boundary]
    exact hy
  have hySourceBoundary : y ∈
      coordinateUnlinkExteriorModel.boundary
        (ZMod m × EuclideanFourBall) := by
    exact ((coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m
      |>.isLocalDiffeomorph y).isBoundaryPoint_iff (by simp)).mpr hyTargetBoundary
  rw [coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily_boundary] at hySourceBoundary
  change y.2 ∈ euclideanFourBallModel.boundary EuclideanFourBall at hySourceBoundary
  rw [← range_euclideanFourBallSmoothCollar_zero] at hySourceBoundary
  obtain ⟨s, hs⟩ := hySourceBoundary
  refine ⟨(y.1, s), ?_⟩
  apply Prod.ext
  · rfl
  · change coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar
        (s, euclideanFourBallCollarZero) = y.2
    rw [coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar_apply]
    exact hs

/-- Equality between a body image and a cap image is induced by an attaching point. -/
theorem coordinateExteriorPlanarNeckRightSmoothCappingRightTube_cross
    (x : CompactNeckRightCut m) (y : ZMod m × EuclideanFourBall)
    (hxy : coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyContinuousMap m x =
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapContinuousMap m y) :
    ∃ p : ZMod m × Sphere 3,
      coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m p = x ∧
        coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m p = y := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
  have hbase :
      (x.1.1.1.1 : Sphere 4) =
        ((coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m y).1.1.1 :
          Sphere 4) :=
    congrArg (fun z : CoordinateExteriorRightTubePowerPullback m ↦
      (z.1.1.1 : Sphere 4)) hxy
  have hxNotCapZero : (x.1.1.1.1 : Sphere 4) ∉ coordinateOpenCap 0 := by
    have hxCarrier : x.1 ∈
        coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m := x.2
    have hx := (Set.ext_iff.mp
      (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier_eq_preimage_compl_cap_zero
        m) x.1).mp hxCarrier
    exact hx
  have hxNonnegative : 0 ≤ (x.1.1.1.1 : Sphere 4).1 3 := by
    rw [mem_coordinateOpenCap_zero] at hxNotCapZero
    exact le_of_not_gt hxNotCapZero
  have hyNonpositive :
      (((coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m y).1.1.1 :
        Sphere 4).1 3) ≤ 0 := by
    have hyClosed :
        ((coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m y).1.1.1 :
          Sphere 4) ∈ coordinateClosedCapZero :=
      (coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m y).1.1.2
    change ((coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m y).1.1.1 :
      Sphere 4) ∉ coordinateOpenCap 1 at hyClosed
    rw [mem_coordinateOpenCap_one] at hyClosed
    exact le_of_not_gt hyClosed
  have hyEquator :
      ((coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m y).1.1.1 :
        Sphere 4) ∈ coordinateEquator := by
    change ((coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m y).1.1.1 :
      Sphere 4).1 3 = 0
    apply le_antisymm hyNonpositive
    rw [← hbase]
    exact hxNonnegative
  obtain ⟨p, hp⟩ := exists_ball_attaching_of_cap_base_mem_equator m y hyEquator
  refine ⟨p, ?_, hp⟩
  apply coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap_injective m
  calc
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap m
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m p) =
        coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap m
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m p) :=
      coordinateExteriorPlanarNeckRightSmoothCappingRightTube_attaching m p
    _ = coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap m y :=
      congrArg (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap m) hp
    _ = coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap m x := hxy.symm

/-- The compact right neck cut is a compact space. -/
theorem compactSpace_compactNeckRightCut :
    CompactSpace (CompactNeckRightCut m) := by
  let _ : CompactSpace (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    compactSpace_coordinateUnlinkExteriorEighthPowerPullback m
  exact isCompact_iff_compactSpace.mp
    (isClosed_coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m).isCompact

/-- The point-set comparison from the direct right capping to the right-tube power pullback. -/
def coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph :
    CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping m ≃ₜ
      CoordinateExteriorRightTubePowerPullback m := by
  let _ : CompactSpace (CompactNeckRightCut m) :=
    compactSpace_compactNeckRightCut m
  exact topologicalPushoutHomeomorph
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyContinuousMap m)
    (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapContinuousMap m)
    (coordinateExteriorPlanarNeckRightSmoothCappingRightTube_attaching m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m).injective
    (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap_injective m)
    (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap_injective m)
    (coordinateExteriorPlanarNeckRightSmoothCappingRightTube_cross m)
    (coordinateExteriorPlanarNeckRightSmoothCappingRightTube_cover m)

/-- The point-set comparison agrees with the body map on the left coprojection. -/
@[simp]
theorem coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph_inl
    (x : CompactNeckRightCut m) :
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x) =
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap m x := by
  let _ : CompactSpace (CompactNeckRightCut m) :=
    compactSpace_compactNeckRightCut m
  change coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m _ =
    (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyContinuousMap m) x
  simpa [coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph] using
    topologicalPushoutHomeomorph_inl
      (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyContinuousMap m)
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapContinuousMap m)
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTube_attaching m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m).injective
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap_injective m)
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap_injective m)
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTube_cross m)
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTube_cover m) x

/-- The point-set comparison agrees with the cap map on the right coprojection. -/
@[simp]
theorem coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph_inr
    (y : ZMod m × EuclideanFourBall) :
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) y) =
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap m y := by
  let _ : CompactSpace (CompactNeckRightCut m) :=
    compactSpace_compactNeckRightCut m
  change coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m _ =
    (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapContinuousMap m) y
  simpa [coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph] using
    topologicalPushoutHomeomorph_inr
      (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyContinuousMap m)
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapContinuousMap m)
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTube_attaching m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m).injective
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap_injective m)
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap_injective m)
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTube_cross m)
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTube_cover m) y

private theorem rightCapping_isOpen_rightTubeClosed_offBoundary :
    IsOpen (collaredCutSideOffBoundary
      coordinateExteriorRightTubeClosedCarrier
      coordinateExteriorRightTubeBoundary) := by
  rw [coordinateExteriorRightTubeClosed_offBoundary]
  exact (isClosed_standardUnlinkClosedTube 1 (1 / 8 : ℝ)).isOpen_compl

private theorem rightCapping_isLocalDiffeomorph_roundedCapOffMap :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    letI := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (collaredCutSideOffBoundaryOpensMap coordinateClosedCapZero
        coordinateEquator
        isOpen_roundedHemisphereClosedCapZero_offBoundary) := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide coordinateClosedCapZero) :=
    isManifold_coordinateUnlinkExteriorRoundedHemisphereClosedCap
  apply isLocalDiffeomorph_collaredCutSideOffBoundaryMap
    coordinateUnlinkExteriorModel ∞ coordinateClosedCapZero coordinateEquator
    isOpen_roundedHemisphereClosedCapZero_offBoundary
    roundedHemisphereClosedCapCollarAmbient
    range_roundedHemisphereClosedCapCollarAmbient_subset
    isOpenEmbedding_roundedHemisphereClosedCapBoundaryCollar
    roundedHemisphereClosedCapZero_cover
  intro i j
  apply IsManifold.compatible_of_mem_maximalAtlas
  · apply IsManifold.subset_maximalAtlas
    exact ⟨i, rfl⟩
  · apply IsManifold.subset_maximalAtlas
    exact ⟨j, rfl⟩

private theorem coordinateOpenCapZero_subset_rightTubeClosedOffBoundary :
    coordinateOpenCap 0 ⊆
      collaredCutSideOffBoundary coordinateExteriorRightTubeClosedCarrier
        coordinateExteriorRightTubeBoundary := by
  rw [coordinateExteriorRightTubeClosed_offBoundary]
  intro q hq hclosed
  rw [mem_coordinateOpenCap_zero] at hq
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

private def coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMapBaseInclusion
    (q : CollaredCutSide coordinateClosedCapZero) :
    CoordinateExteriorRightTubeClosed :=
  ⟨q.1, coordinateClosedCapZero_subset_rightTubeClosedCarrier q.2⟩

private theorem rightCapping_roundedPowerPullback_base_mem_offBoundary_of_not_attaching
    (x : ↑(topologicalPushoutInrOffSeamOpens
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m))) :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    letI := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
    (coordinateExteriorRoundedCapPowerPullbackProj m
      (coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m x.1)).1 ∈
        collaredCutSideOffBoundary coordinateClosedCapZero coordinateEquator := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBall) :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily m
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide coordinateClosedCapZero) :=
    isManifold_coordinateUnlinkExteriorRoundedHemisphereClosedCap
  let _ := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRoundedCapPowerPullback m) :=
    isManifold_coordinateExteriorRoundedCapPowerPullback m
  let z := coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m x.1
  have hxNotBoundary : x.1 ∉ coordinateUnlinkExteriorModel.boundary
      (ZMod m × EuclideanFourBall) := by
    rw [← range_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap]
    exact x.2
  have hzNotBoundary : z ∉ coordinateUnlinkExteriorModel.boundary
      (CoordinateExteriorRoundedCapPowerPullback m) := by
    intro hz
    apply hxNotBoundary
    exact ((coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m
      |>.isLocalDiffeomorph x.1).isBoundaryPoint_iff (by simp)).mpr hz
  have hzNotEquator : (coordinateExteriorRoundedCapPowerPullbackProj m z).1 ∉
      coordinateEquator := by
    intro hz
    apply hzNotBoundary
    rw [coordinateExteriorRoundedCapPowerPullback_boundary]
    exact hz
  exact ⟨(coordinateExteriorRoundedCapPowerPullbackProj m z).2,
    hzNotEquator⟩

private theorem rightCapping_isLocalDiffeomorph_compactNeckRightCutOffMap :
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (collaredCutSideOffBoundaryOpensMap
        (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
        (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
        (isOpen_compactNeckRightCut_offBoundary m)) := by
  let _ : ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := compactNeckRightCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckRightCut m) :=
    isManifold_compactNeckRightCut m
  apply isLocalDiffeomorph_collaredCutSideOffBoundaryMap
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckRightCut_offBoundary m)
  intro i j
  apply IsManifold.compatible_of_mem_maximalAtlas
  · apply IsManifold.subset_maximalAtlas
    exact ⟨i, rfl⟩
  · apply IsManifold.subset_maximalAtlas
    exact ⟨j, rfl⟩

private theorem coordinateUnlinkExteriorEighth_subset_rightTubeClosedCarrier
    (q : CoordinateUnlinkExteriorEighth) :
    q.1 ∈ coordinateExteriorRightTubeClosedCarrier := by
  rw [coordinateExteriorRightTubeClosedCarrier_eq_compl_openTube]
  intro hright
  exact q.2 (Or.inr hright)

private def rightCappingExteriorBaseToRightTube
    (q : CoordinateUnlinkExteriorEighth) :
    CoordinateExteriorRightTubeClosed :=
  ⟨q.1, coordinateUnlinkExteriorEighth_subset_rightTubeClosedCarrier q⟩

private def rightCappingCutBaseMap (q : CompactNeckRightCut m) :
    CoordinateExteriorRightTubeClosed :=
  rightCappingExteriorBaseToRightTube
    (coordinateUnlinkExteriorEighthPowerPullbackProj m q.1)

private theorem
    rightCappingCutBaseMap_eq_coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap_proj
    (q : CompactNeckRightCut m) :
    rightCappingCutBaseMap m q =
      coordinateExteriorRightTubePowerPullbackProj m
        (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap m q) := by
  rfl

/-! ## The generators for the literal standard-collar target atlas -/

private theorem rightCapping_isLocalDiffeomorph_rightTubeStandardOffMap :
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (collaredCutSideOffBoundaryOpensMap
        coordinateExteriorRightTubeClosedCarrier
        coordinateExteriorRightTubeBoundary
        rightCapping_isOpen_rightTubeClosed_offBoundary) := by
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
    rightCapping_isOpen_rightTubeClosed_offBoundary
  intro i j
  apply IsManifold.compatible_of_mem_maximalAtlas
  · apply IsManifold.subset_maximalAtlas
    exact ⟨i, rfl⟩
  · apply IsManifold.subset_maximalAtlas
    exact ⟨j, rfl⟩

private theorem rightCapping_isLocalDiffeomorphAt_capBaseInclusion_of_offBoundary_standard
    (q : CollaredCutSide coordinateClosedCapZero)
    (hq : q.1 ∈ collaredCutSideOffBoundary coordinateClosedCapZero
      coordinateEquator) :
    letI := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMapBaseInclusion q := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide coordinateClosedCapZero) :=
    isManifold_coordinateUnlinkExteriorRoundedHemisphereClosedCap
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  let U := collaredCutSideOffBoundaryOpens coordinateClosedCapZero
    coordinateEquator isOpen_roundedHemisphereClosedCapZero_offBoundary
  let V := collaredCutSideOffBoundaryOpens
    coordinateExteriorRightTubeClosedCarrier
    coordinateExteriorRightTubeBoundary
    rightCapping_isOpen_rightTubeClosed_offBoundary
  let c : U → CollaredCutSide coordinateClosedCapZero :=
    collaredCutSideOffBoundaryOpensMap coordinateClosedCapZero
      coordinateEquator isOpen_roundedHemisphereClosedCapZero_offBoundary
  let d : V → CoordinateExteriorRightTubeClosed :=
    collaredCutSideOffBoundaryOpensMap
      coordinateExteriorRightTubeClosedCarrier
      coordinateExteriorRightTubeBoundary
      rightCapping_isOpen_rightTubeClosed_offBoundary
  have hmem (x : U) : x.1 ∈ V := by
    change x.1 ∈ collaredCutSideOffBoundary
      coordinateExteriorRightTubeClosedCarrier
      coordinateExteriorRightTubeBoundary
    apply coordinateOpenCapZero_subset_rightTubeClosedOffBoundary
    rw [← roundedHemisphereClosedCapZero_offBoundary]
    exact x.2
  let r : U → V := restrictToOpens
    (Diffeomorph.refl coordinateUnlinkExteriorModel (Sphere 4) ∞)
    U V hmem
  have hc : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ c :=
    rightCapping_isLocalDiffeomorph_roundedCapOffMap
  have hd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ d :=
    rightCapping_isLocalDiffeomorph_rightTubeStandardOffMap
  have hr : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ r :=
    isLocalDiffeomorph_restrictToOpens coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel
      (Diffeomorph.refl coordinateUnlinkExteriorModel (Sphere 4) ∞)
      U V hmem
      (Diffeomorph.refl coordinateUnlinkExteriorModel
        (Sphere 4) ∞).isLocalDiffeomorph
  have hright : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (d ∘ r) := by
    intro x
    exact (hr x).comp coordinateUnlinkExteriorModel
      CoordinateExteriorRightTubeClosed (hd (r x))
  have hcomp : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMapBaseInclusion ∘
        c) := by
    intro x
    apply rightCapping_isLocalDiffeomorphAt_congr_of_eventuallyEq (hright x)
    filter_upwards [] with y
    apply Subtype.ext
    rfl
  let p : U := ⟨q.1, hq⟩
  have hp := isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMapBaseInclusion c hc hcomp p
  simpa only [c, collaredCutSideOffBoundaryOpensMap] using hp

/-- The comparison is a local diffeomorphism on the rounded-cap off-seam generator. -/
theorem isLocalDiffeomorph_coordinateExteriorPlanarNeckRightSmoothCappingRightTube_capOffSeam :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullbackStandard m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m ∘
        topologicalPushoutInrOffSeamMap'
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)) := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBall) :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily m
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide coordinateClosedCapZero) :=
    isManifold_coordinateUnlinkExteriorRoundedHemisphereClosedCap
  let _ := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRoundedCapPowerPullback m) :=
    isManifold_coordinateExteriorRoundedCapPowerPullback m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullbackStandard m
  let U := topologicalPushoutInrOffSeamOpens
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
  let F : U → CoordinateExteriorRightTubePowerPullback m :=
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m ∘
      topologicalPushoutInrOffSeamMap'
      (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
  have hF : Continuous F := by
    exact (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m).continuous.comp
      (isOpenEmbedding_topologicalPushoutInrOffSeamMap'
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap
          m)).continuous
  apply rightCapping_reflect_isLocalDiffeomorph
    (coordinateExteriorRightTubePowerPullbackProj m) F
    (isLocalDiffeomorph_coordinateExteriorRightTubePowerPullbackProj_standard m) hF
  intro x
  let z := coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m x.1
  have hOne : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Subtype.val : U → ZMod m × EuclideanFourBall) x :=
    isLocalDiffeomorph_opensSubtypeVal coordinateUnlinkExteriorModel U x
  have hTwo : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m) x.1 :=
    (coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m
      |>.isLocalDiffeomorph x.1)
  have hThree : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateExteriorRoundedCapPowerPullbackProj m) z :=
    isLocalDiffeomorph_coordinateExteriorRoundedCapPowerPullbackProj m z
  have hzOff :=
    rightCapping_roundedPowerPullback_base_mem_offBoundary_of_not_attaching m x
  have hFour : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMapBaseInclusion
      (coordinateExteriorRoundedCapPowerPullbackProj m z) :=
    rightCapping_isLocalDiffeomorphAt_capBaseInclusion_of_offBoundary_standard
      (coordinateExteriorRoundedCapPowerPullbackProj m z) hzOff
  have hOneTwo : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m ∘
        (Subtype.val : U → ZMod m × EuclideanFourBall)) x :=
    hOne.comp
      (g := coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m)
      coordinateUnlinkExteriorModel
      (CoordinateExteriorRoundedCapPowerPullback m) hTwo
  have hOneTwoThree : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateExteriorRoundedCapPowerPullbackProj m ∘
        coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m ∘
        (Subtype.val : U → ZMod m × EuclideanFourBall)) x :=
    hOneTwo.comp
      (g := coordinateExteriorRoundedCapPowerPullbackProj m)
      coordinateUnlinkExteriorModel
      (CollaredCutSide coordinateClosedCapZero) hThree
  have hcomp : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMapBaseInclusion ∘
        coordinateExteriorRoundedCapPowerPullbackProj m ∘
        coordinateExteriorRoundedBallFamilyPowerPullbackDiffeomorph m ∘
        (Subtype.val : U → ZMod m × EuclideanFourBall)) x :=
    hOneTwoThree.comp
      (g := coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMapBaseInclusion)
      coordinateUnlinkExteriorModel CoordinateExteriorRightTubeClosed hFour
  apply rightCapping_isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp
  filter_upwards [] with y
  apply Subtype.ext
  simp only [Function.comp_apply, F, topologicalPushoutInrOffSeamMap',
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph_inr]
  rfl

private def rightCappingPartialDiffeomorphOfAtlas
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

private theorem rightCapping_isLocalDiffeomorph_coordinateUnlinkExteriorEighthCollarToExterior
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
    rightCappingPartialDiffeomorphOfAtlas coordinateUnlinkExteriorModel
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
    rightCappingPartialDiffeomorphOfAtlas coordinateUnlinkExteriorModel
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

private theorem rightCapping_isLocalDiffeomorph_rightTubeStandardBoundaryCollar :
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
    rightCapping_isOpen_rightTubeClosed_offBoundary
  intro i j
  apply IsManifold.compatible_of_mem_maximalAtlas
  · apply IsManifold.subset_maximalAtlas
    exact ⟨i, rfl⟩
  · apply IsManifold.subset_maximalAtlas
    exact ⟨j, rfl⟩

private theorem coordinateOpenCapOne_subset_leftClosedTubeExterior
    {q : Sphere 4} (hq : q ∈ coordinateOpenCap 1) :
    q ∉ standardUnlinkClosedTube 0 (1 / 8 : ℝ) := by
  rw [mem_coordinateOpenCap_one] at hq
  intro hclosed
  change dist (standardUnlinkNormalProjection q)
      (standardUnlinkNormalCenter 0) ≤ 1 / 8 at hclosed
  rw [dist_eq_norm] at hclosed
  let v := standardUnlinkNormalProjection q - standardUnlinkNormalCenter 0
  have hsq : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    simpa [Fin.sum_univ_succ] using EuclideanSpace.real_norm_sq_eq v
  have hv0 : v 0 = q.1 3 + 1 / 2 := by
    simp [v, standardUnlinkHeight]
  have hv1sq : 0 ≤ v 1 ^ 2 := sq_nonneg _
  have hvnorm_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
  rw [hv0] at hsq
  nlinarith

private theorem rightCapping_isLocalDiffeomorphAt_exteriorBaseToRightTube_standard
    (q : CoordinateUnlinkExteriorEighth)
    (hqCap : (q.1 : Sphere 4) ∈ coordinateOpenCap 1) :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ rightCappingExteriorBaseToRightTube q := by
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
  by_cases hright :
      ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1‖ =
        (1 / 8 : ℝ)
  · let z : StandardUnlinkExteriorCollar 1 (1 / 8 : ℝ) (1 / 4 : ℝ) :=
      ⟨q.1, (mem_standardUnlinkExteriorCollarSet_iff 1
        (by norm_num) (by norm_num) q.1).2 ⟨hright.ge, by
          rw [hright]
          norm_num⟩⟩
    let p : CoordinateUnlinkExteriorEighthCollarDomain :=
      (standardUnlinkExteriorEighthCollarHomeomorph 1).symm z
    have hpq : coordinateUnlinkExteriorEighthCollarToExterior 1 p = q := by
      apply Subtype.ext
      change (standardUnlinkExteriorEighthCollarHomeomorph 1 p).1 = q.1
      simpa only [p, z] using congrArg Subtype.val
        ((standardUnlinkExteriorEighthCollarHomeomorph 1).apply_symm_apply z)
    have hc : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        (coordinateUnlinkExteriorEighthCollarToExterior 1) :=
      rightCapping_isLocalDiffeomorph_coordinateUnlinkExteriorEighthCollarToExterior 1
    have ht : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        coordinateExteriorRightTubeStandardBoundaryCollar :=
      rightCapping_isLocalDiffeomorph_rightTubeStandardBoundaryCollar
    have hcomp : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        (rightCappingExteriorBaseToRightTube ∘
          coordinateUnlinkExteriorEighthCollarToExterior 1) := by
      intro x
      apply rightCapping_isLocalDiffeomorphAt_congr_of_eventuallyEq (ht x)
      filter_upwards [] with y
      apply Subtype.ext
      rfl
    have h := isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
      coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
      rightCappingExteriorBaseToRightTube
      (coordinateUnlinkExteriorEighthCollarToExterior 1) hc hcomp p
    rwa [hpq] at h
  · have hrightGt : (1 / 8 : ℝ) <
        ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1‖ := by
      have hnotOpen := q.2
      change q.1 ∉ standardUnlinkOpenTubes (1 / 8 : ℝ) at hnotOpen
      have hge : (1 / 8 : ℝ) ≤
          ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1‖ := by
        apply le_of_not_gt
        intro hlt
        apply hnotOpen
        exact Or.inr (by
          change dist (standardUnlinkNormalProjection q.1)
            (standardUnlinkNormalCenter 1) < 1 / 8
          simpa only [dist_eq_norm] using hlt)
      exact lt_of_le_of_ne hge (Ne.symm hright)
    have hleftGt : (1 / 8 : ℝ) <
        ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 0‖ := by
      have hnot := coordinateOpenCapOne_subset_leftClosedTubeExterior hqCap
      change q.1 ∉ standardUnlinkClosedTube 0 (1 / 8 : ℝ) at hnot
      change ¬ dist (standardUnlinkNormalProjection q.1)
        (standardUnlinkNormalCenter 0) ≤ 1 / 8 at hnot
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
      rightCapping_isOpen_rightTubeClosed_offBoundary
    let c : U → CoordinateUnlinkExteriorEighth := Subtype.val
    have hmem (x : U) : x.1.1 ∈ V := by
      change x.1.1 ∈ collaredCutSideOffBoundary
        coordinateExteriorRightTubeClosedCarrier
        coordinateExteriorRightTubeBoundary
      rw [coordinateExteriorRightTubeClosed_offBoundary]
      change ¬ dist (standardUnlinkNormalProjection x.1.1)
        (standardUnlinkNormalCenter 1) ≤ 1 / 8
      rw [dist_eq_norm]
      exact not_le.mpr
        ((mem_coordinateUnlinkExteriorEighthInteriorOpens_iff x.1).mp x.2 1)
    let r : U → V := fun x ↦ ⟨x.1.1, hmem x⟩
    let d : V → CoordinateExteriorRightTubeClosed :=
      collaredCutSideOffBoundaryOpensMap
        coordinateExteriorRightTubeClosedCarrier
        coordinateExteriorRightTubeBoundary
        rightCapping_isOpen_rightTubeClosed_offBoundary
    have hc : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞ c :=
      isLocalDiffeomorph_opensSubtypeVal
        coordinateUnlinkExteriorModel coordinateUnlinkExteriorEighthInteriorOpens
    have hd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞ d :=
      rightCapping_isLocalDiffeomorph_rightTubeStandardOffMap
    have hrContinuous : Continuous r := by
      exact ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
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
      have hOneTwo := hOne.comp
        (g := (Subtype.val : StandardUnlinkClosedTubeExterior → Sphere 4))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (Sphere 4) hTwo
      have hcomp := hOneTwo.comp
        (g := standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph)
        coordinateUnlinkExteriorModel (Sphere 4) hThree
      apply rightCapping_isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp
      filter_upwards [] with y
      rfl
    have hr : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞ r :=
      rightCapping_reflect_isLocalDiffeomorph
        (Subtype.val : V → Sphere 4) r hprojV hrContinuous hprojR
    have hrightMap : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞ (d ∘ r) := by
      intro x
      exact (hr x).comp coordinateUnlinkExteriorModel
        CoordinateExteriorRightTubeClosed (hd (r x))
    have hcomp : IsLocalDiffeomorph coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        (rightCappingExteriorBaseToRightTube ∘ c) := by
      intro x
      apply rightCapping_isLocalDiffeomorphAt_congr_of_eventuallyEq (hrightMap x)
      filter_upwards [] with y
      apply Subtype.ext
      rfl
    let p : U := ⟨q, hqInterior⟩
    have h := isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
      coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
      rightCappingExteriorBaseToRightTube c hc hcomp p
    simpa only [c] using h

private theorem rightCapping_isLocalDiffeomorphAt_cutBaseMap_of_offBoundary_standard
    (q : CompactNeckRightCut m)
    (hq : q.1 ∈ collaredCutSideOffBoundary
      (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)) :
    letI := compactNeckRightCutChartedSpace m
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (rightCappingCutBaseMap m) q := by
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
  let _ := compactNeckRightCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckRightCut m) :=
    isManifold_compactNeckRightCut m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  let U := collaredCutSideOffBoundaryOpens
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckRightCut_offBoundary m)
  let c : U → CompactNeckRightCut m :=
    collaredCutSideOffBoundaryOpensMap
      (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
      (isOpen_compactNeckRightCut_offBoundary m)
  have hc : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ c :=
    rightCapping_isLocalDiffeomorph_compactNeckRightCutOffMap m
  have hproj : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorEighthPowerPullbackProj m) :=
    isLocalDiffeomorph_coordinateUnlinkExteriorEighthPowerPullbackProj m
  have hbase : ∀ x : U, IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ rightCappingExteriorBaseToRightTube
      (coordinateUnlinkExteriorEighthPowerPullbackProj m x.1) := by
    intro x
    apply rightCapping_isLocalDiffeomorphAt_exteriorBaseToRightTube_standard
    have hx := x.2
    change x.1 ∈ collaredCutSideOffBoundary
      (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) at hx
    rcases hx with ⟨hxCarrier, hxNotSeam⟩
    have hnonnegative : 0 ≤
        (coordinateUnlinkExteriorEighthPowerPullbackProj m x.1 : Sphere 4).1 3 := by
      rw [coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier_eq_preimage_compl_cap_zero]
        at hxCarrier
      change (coordinateUnlinkExteriorEighthPowerPullbackProj m x.1 : Sphere 4) ∉
        coordinateOpenCap 0 at hxCarrier
      rw [mem_coordinateOpenCap_zero] at hxCarrier
      exact le_of_not_gt hxCarrier
    have hnonzero :
        (coordinateUnlinkExteriorEighthPowerPullbackProj m x.1 : Sphere 4).1 3 ≠ 0 := by
      intro hzero
      apply hxNotSeam
      rw [coordinateUnlinkExteriorPlanarCompactNeckStarSeam_eq_preimage_coordinateEquator]
      exact hzero
    rw [mem_coordinateOpenCap_one]
    exact lt_of_le_of_ne hnonnegative hnonzero.symm
  have hcomp : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (rightCappingCutBaseMap m ∘ c) := by
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
        (rightCappingExteriorBaseToRightTube ∘
          coordinateUnlinkExteriorEighthPowerPullbackProj m ∘
          (Subtype.val : U → CoordinateUnlinkExteriorEighthPowerPullback m)) x :=
      hsubproj.comp (g := rightCappingExteriorBaseToRightTube)
        coordinateUnlinkExteriorModel CoordinateExteriorRightTubeClosed (hbase x)
    apply rightCapping_isLocalDiffeomorphAt_congr_of_eventuallyEq h
    filter_upwards [] with y
    rfl
  let p : U := ⟨q.1, hq⟩
  have hp := isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    (rightCappingCutBaseMap m) c hc hcomp p
  simpa only [c, collaredCutSideOffBoundaryOpensMap] using hp

/-- The comparison is a local diffeomorphism on the compact-cut off-seam generator. -/
theorem isLocalDiffeomorph_coordinateExteriorPlanarNeckRightSmoothCappingRightTube_cutOffSeam :
    letI := compactNeckRightCutChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullbackStandard m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m ∘
        topologicalPushoutInlOffSeamMap'
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)) := by
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
  let _ := compactNeckRightCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckRightCut m) :=
    isManifold_compactNeckRightCut m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullbackStandard m
  let U := topologicalPushoutInlOffSeamOpens
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
  let F : U → CoordinateExteriorRightTubePowerPullback m :=
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m ∘
      topologicalPushoutInlOffSeamMap'
      (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
      (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
  have hF : Continuous F := by
    exact (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m).continuous.comp
      (isOpenEmbedding_topologicalPushoutInlOffSeamMap'
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap
          m)).continuous
  apply rightCapping_reflect_isLocalDiffeomorph
    (coordinateExteriorRightTubePowerPullbackProj m) F
    (isLocalDiffeomorph_coordinateExteriorRightTubePowerPullbackProj_standard m) hF
  intro x
  have hxOff : x.1.1 ∈ collaredCutSideOffBoundary
      (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) := by
    refine ⟨x.1.2, ?_⟩
    have hx := x.2
    change x.1 ∉ range
      (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m) at hx
    rw [range_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap] at hx
    exact hx
  have hOne : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Subtype.val : U → CompactNeckRightCut m) x :=
    isLocalDiffeomorph_opensSubtypeVal coordinateUnlinkExteriorModel U x
  have hTwo : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (rightCappingCutBaseMap m) x.1 :=
    rightCapping_isLocalDiffeomorphAt_cutBaseMap_of_offBoundary_standard m x.1 hxOff
  have hcomp : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (rightCappingCutBaseMap m ∘ (Subtype.val : U → CompactNeckRightCut m)) x :=
    hOne.comp (g := rightCappingCutBaseMap m) coordinateUnlinkExteriorModel
      CoordinateExteriorRightTubeClosed hTwo
  apply rightCapping_isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp
  filter_upwards [] with y
  rw [Function.comp_apply]
  change coordinateExteriorRightTubePowerPullbackProj m
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) y.1)) = _
  rw [coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph_inl]
  exact
    (rightCappingCutBaseMap_eq_coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap_proj
      m y.1).symm

private theorem rightCapping_equatorCollarNeg_not_mem_closedTubes_quarter
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

private def rightCapping_rightSmoothCappingSeamTargetBase
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :
    CoordinateExteriorRightTubeClosed :=
  coordinateExteriorRightTubePowerPullbackProj m
    (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m
      (coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m p))

private theorem rightCapping_rightSmoothCappingSeamTargetBase_coe_of_nonpositive
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : signedSeamTime m p ≤ 0)
    (hsmall : |(p.2.2.1 : ℝ)| < 1 / 8) :
    (rightCapping_rightSmoothCappingSeamTargetBase m p : Sphere 4) =
      equatorCollarSphereMap
        (p.2.1,
          coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2.2) := by
  rw [rightCapping_rightSmoothCappingSeamTargetBase,
    coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap_of_nonpositive m p hp,
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph_inl]
  simp only [coordinateExteriorRightTubePowerPullbackProj,
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap]
  rw [coordinateUnlinkExteriorPlanarNeckRightCutSeamBranch,
    coordinateUnlinkExteriorPlanarNeckRightCutCollar]
  change
    (compactNeckRightBoundaryCollarMap m (signedSeamHalfReparam m p)).1.1.1 = _
  rw [compactNeckRightBoundaryCollarMap]
  rw [coordinateUnlinkExteriorPlanarOrientedCompactCollarMap_eq_raw]
  rw [coordinateUnlinkExteriorPlanarTransportedNeckCompactCollarMap]
  have hparam :
      compactNeckRightHalfParameter (signedSeamHalfReparam m p).2 =
        (p.2.1,
          coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2.2) := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change |(p.2.2.1 : ℝ)| = -(p.2.2.1 : ℝ)
      exact abs_of_nonpos hp
  rw [hparam]
  rw [standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph_apply_base]
  rw [standardUnlinkClosedTubeExteriorToCoordinateExterior_coe,
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
  · change equatorCollarSphereMap
        (p.2.1,
          coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2.2) ∉
      standardUnlinkClosedTubes (1 / 4 : ℝ)
    exact rightCapping_equatorCollarNeg_not_mem_closedTubes_quarter p.2 hsmall

private theorem rightCapping_rightSmoothCappingSeamTargetBase_coe_of_positive
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : 0 < signedSeamTime m p) :
    (rightCapping_rightSmoothCappingSeamTargetBase m p : Sphere 4) =
      equatorCollarSphereMap
        (p.2.1,
          coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2.2) := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ := coordinateExteriorRoundedCapPowerPullbackChartedSpace m
  rw [rightCapping_rightSmoothCappingSeamTargetBase,
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

private def rightCapping_equatorCollarNegFamily
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :
    Sphere 4 :=
  equatorCollarSphereMap
    (p.2.1,
      coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph p.2.2)

omit [NeZero m] in
private theorem rightCapping_isLocalDiffeomorph_equatorCollarNegFamily :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := coordinateUnlinkExteriorCommonModelSphereChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (rightCapping_equatorCollarNegFamily m) := by
  let _ := signedSeamCommonModelChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCommonModel
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    isManifold_signedSeamFamilyCommonModel m
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  have hsnd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd :
        CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m →
          Sphere 3 × EquatorCollarInterval) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := Sphere 3 × EquatorCollarInterval))
  have hbase := isLocalDiffeomorph_equatorCollarNeg_common
  intro p
  have hcomp := (hsnd p).comp coordinateUnlinkExteriorModel (Sphere 4)
    (hbase p.2)
  change IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
    coordinateUnlinkExteriorModel ∞
    ((fun q : Sphere 3 × EquatorCollarInterval ↦
      equatorCollarSphereMap
        (q.1,
          coordinateUnlinkExteriorPlanarEquatorCollarIntervalNegHomeomorph q.2)) ∘
      Prod.snd) p
  exact hcomp

private theorem rightCapping_isLocalDiffeomorphAt_rightSmoothCappingSeamTargetBase_of_zero
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : signedSeamTime m p = 0) :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (rightCapping_rightSmoothCappingSeamTargetBase m) p := by
  let _ := signedSeamCommonModelChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCommonModel
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    isManifold_signedSeamFamilyCommonModel m
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  let U : Opens
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    ⟨{q | |signedSeamTime m q| < 1 / 8}, by
      have ht : Continuous (signedSeamTime m) :=
        (contMDiff_signedSeamFamilyTime m).continuous
      exact (_root_.continuous_abs.comp ht).isOpen_preimage _ isOpen_Iio⟩
  let V := collaredCutSideOffBoundaryOpens
    coordinateExteriorRightTubeClosedCarrier
    coordinateExteriorRightTubeBoundary
    isOpen_coordinateExteriorRightTubeClosed_offBoundary
  have hmem (q : U) : rightCapping_equatorCollarNegFamily m q.1 ∈ V := by
    change rightCapping_equatorCollarNegFamily m q.1 ∈
      collaredCutSideOffBoundary coordinateExteriorRightTubeClosedCarrier
        coordinateExteriorRightTubeBoundary
    rw [coordinateExteriorRightTubeClosed_offBoundary]
    intro hclosed
    have hnot := rightCapping_equatorCollarNeg_not_mem_closedTubes_quarter
      q.1.2 q.2
    apply hnot
    exact Or.inr (standardUnlinkClosedTube_mono 1 (by norm_num) hclosed)
  let r : U → V := restrictToOpens (rightCapping_equatorCollarNegFamily m) U V hmem
  have hr : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ r :=
    isLocalDiffeomorph_restrictToOpens coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel (rightCapping_equatorCollarNegFamily m) U V hmem
      (rightCapping_isLocalDiffeomorph_equatorCollarNegFamily m)
  let d : V → CoordinateExteriorRightTubeClosed :=
    collaredCutSideOffBoundaryOpensMap
      coordinateExteriorRightTubeClosedCarrier
      coordinateExteriorRightTubeBoundary
      isOpen_coordinateExteriorRightTubeClosed_offBoundary
  have hd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ d :=
    rightCapping_isLocalDiffeomorph_rightTubeStandardOffMap
  have hdr : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (d ∘ r) := by
    intro q
    exact (hr q).comp coordinateUnlinkExteriorModel
      CoordinateExteriorRightTubeClosed (hd (r q))
  have hactual : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (rightCapping_rightSmoothCappingSeamTargetBase m ∘ (Subtype.val : U → _)) := by
    intro q
    apply rightCapping_isLocalDiffeomorphAt_congr_of_eventuallyEq (hdr q)
    filter_upwards [] with z
    apply Subtype.ext
    by_cases hz : signedSeamTime m z.1 ≤ 0
    · exact rightCapping_rightSmoothCappingSeamTargetBase_coe_of_nonpositive
        m z.1 hz z.2
    · exact rightCapping_rightSmoothCappingSeamTargetBase_coe_of_positive
        m z.1 (lt_of_not_ge hz)
  let q : U := ⟨p, by
    change |signedSeamTime m p| < 1 / 8
    rw [hp, abs_zero]
    norm_num⟩
  have hdesc := isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    (rightCapping_rightSmoothCappingSeamTargetBase m)
    (Subtype.val : U →
      CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (isLocalDiffeomorph_opensSubtypeVal coordinateUnlinkExteriorModel U)
    hactual q
  exact hdesc

private theorem rightCapping_isLocalDiffeomorph_rightCutCollar :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    letI := compactNeckRightCutChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarNeckRightCutCollar m) := by
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
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckRightCut_offBoundary m)
    (compactNeckRightBoundaryCollarMap m)
    (compactNeckRightBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckRightBoundaryCollarMap_toCut m)
    (isLocalDiffeomorphOn_compactNeckRightBoundaryCollarMap m)
  exact isLocalDiffeomorph_collaredCutSideHalfCollarMap
    coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckRightCut_offBoundary m)
    (compactNeckRightBoundaryCollarMap m)
    (compactNeckRightBoundaryCollarMap_range_subset m)
    (isOpenEmbedding_compactNeckRightBoundaryCollarMap_toCut m)
    (compactNeckRightCut_collarCoverage m) hcompat

private theorem rightCapping_isLocalDiffeomorphAt_rightSmoothCappingSeamTargetBase_of_negative
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : signedSeamTime m p < 0) :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (rightCapping_rightSmoothCappingSeamTargetBase m) p := by
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
  let _ := compactNeckRightCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckRightCut m) :=
    isManifold_compactNeckRightCut m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  have hhalf : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (signedSeamHalfReparam m) p :=
    isLocalDiffeomorphOn_signedSeamHalfReparam_negative m ⟨p, hp⟩
  have hcollar : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
      (signedSeamHalfReparam m p) :=
    rightCapping_isLocalDiffeomorph_rightCutCollar m (signedSeamHalfReparam m p)
  have hbranch : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateUnlinkExteriorPlanarNeckRightCutCollar m ∘
        signedSeamHalfReparam m) p :=
    hhalf.comp coordinateUnlinkExteriorModel (CompactNeckRightCut m) hcollar
  have hoff :
      (coordinateUnlinkExteriorPlanarNeckRightCutCollar m
        (signedSeamHalfReparam m p)).1 ∈
        collaredCutSideOffBoundary
          (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
          (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m) := by
    change compactNeckRightBoundaryCollarMap m
      (signedSeamHalfReparam m p) ∈ _
    rw [compactNeckRightBoundaryCollarMap_mem_offBoundary_iff]
    change 0 < |signedSeamTime m p|
    exact abs_pos.mpr (ne_of_lt hp)
  have hbase : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (rightCappingCutBaseMap m)
      (coordinateUnlinkExteriorPlanarNeckRightCutCollar m
        (signedSeamHalfReparam m p)) :=
    rightCapping_isLocalDiffeomorphAt_cutBaseMap_of_offBoundary_standard m _ hoff
  have hcomp : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (rightCappingCutBaseMap m ∘
        coordinateUnlinkExteriorPlanarNeckRightCutCollar m ∘
        signedSeamHalfReparam m) p :=
    hbranch.comp coordinateUnlinkExteriorModel
      CoordinateExteriorRightTubeClosed hbase
  let W : Set
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    {q | signedSeamTime m q < 0}
  apply rightCapping_isLocalDiffeomorphAt_congr_of_eqOn_open hcomp W
  · exact isOpen_lt (contMDiff_signedSeamFamilyTime m).continuous continuous_const
  · exact hp
  · intro q hq
    rw [rightCapping_rightSmoothCappingSeamTargetBase,
      coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap_of_nonpositive
        m q (le_of_lt hq), coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph_inl]
    exact
      (rightCappingCutBaseMap_eq_coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap_proj
        m _).symm

private theorem rightCapping_isLocalDiffeomorphAt_rightSmoothCappingSeamTargetBase_of_positive
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (hp : 0 < signedSeamTime m p) :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (rightCapping_rightSmoothCappingSeamTargetBase m) p := by
  let _ := signedSeamCommonModelChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCommonModel
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    isManifold_signedSeamFamilyCommonModel m
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateExteriorRightTubeClosed :=
    isManifold_coordinateExteriorRightTubeStandard
  let U : Opens
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    ⟨{q | 0 < signedSeamTime m q},
      isOpen_lt continuous_const
        (contMDiff_signedSeamFamilyTime m).continuous⟩
  let V := collaredCutSideOffBoundaryOpens
    coordinateExteriorRightTubeClosedCarrier
    coordinateExteriorRightTubeBoundary
    isOpen_coordinateExteriorRightTubeClosed_offBoundary
  have hmem (q : U) : rightCapping_equatorCollarNegFamily m q.1 ∈ V := by
    apply coordinateOpenCapZero_subset_rightTubeClosedOffBoundary
    rw [mem_coordinateOpenCap_zero]
    change -(q.1.2.2.1 : ℝ) < 0
    exact neg_neg_of_pos q.2
  let r : U → V := restrictToOpens (rightCapping_equatorCollarNegFamily m) U V hmem
  have hr : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ r :=
    isLocalDiffeomorph_restrictToOpens coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel (rightCapping_equatorCollarNegFamily m) U V hmem
      (rightCapping_isLocalDiffeomorph_equatorCollarNegFamily m)
  let d : V → CoordinateExteriorRightTubeClosed :=
    collaredCutSideOffBoundaryOpensMap
      coordinateExteriorRightTubeClosedCarrier
      coordinateExteriorRightTubeBoundary
      isOpen_coordinateExteriorRightTubeClosed_offBoundary
  have hd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ d :=
    rightCapping_isLocalDiffeomorph_rightTubeStandardOffMap
  have hdr : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (d ∘ r) := by
    intro q
    exact (hr q).comp coordinateUnlinkExteriorModel
      CoordinateExteriorRightTubeClosed (hd (r q))
  have hactual : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (rightCapping_rightSmoothCappingSeamTargetBase m ∘ (Subtype.val : U → _)) := by
    intro q
    apply rightCapping_isLocalDiffeomorphAt_congr_of_eventuallyEq (hdr q)
    filter_upwards [] with z
    apply Subtype.ext
    exact rightCapping_rightSmoothCappingSeamTargetBase_coe_of_positive m z.1 z.2
  let q : U := ⟨p, hp⟩
  have hdesc := isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    (rightCapping_rightSmoothCappingSeamTargetBase m)
    (Subtype.val : U →
      CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m)
    (isLocalDiffeomorph_opensSubtypeVal coordinateUnlinkExteriorModel U)
    hactual q
  exact hdesc

private theorem rightCapping_isLocalDiffeomorph_rightSmoothCappingSeamTargetBase :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := coordinateExteriorRightTubeStandardChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (rightCapping_rightSmoothCappingSeamTargetBase m) := by
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ := coordinateExteriorRightTubeStandardChartedSpace
  intro p
  rcases lt_trichotomy (signedSeamTime m p) 0 with hp | hp | hp
  · exact
      rightCapping_isLocalDiffeomorphAt_rightSmoothCappingSeamTargetBase_of_negative m p hp
  · exact
      rightCapping_isLocalDiffeomorphAt_rightSmoothCappingSeamTargetBase_of_zero m p hp
  · exact
      rightCapping_isLocalDiffeomorphAt_rightSmoothCappingSeamTargetBase_of_positive m p hp

/-- The comparison is a local diffeomorphism on the signed seam generator. -/
theorem isLocalDiffeomorph_coordinateExteriorPlanarNeckRightSmoothCappingRightTube_seam :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        (CoordinateExteriorRightTubePowerPullback m) :=
      isManifold_coordinateExteriorRightTubePowerPullbackStandard m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m ∘
        coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m) := by
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
  let F := coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m ∘
    coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m
  have hF : Continuous F :=
    (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m).continuous.comp
      (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m).continuous
  apply rightCapping_reflect_isLocalDiffeomorph
    (coordinateExteriorRightTubePowerPullbackProj m) F
    (isLocalDiffeomorph_coordinateExteriorRightTubePowerPullbackProj_standard m)
    hF
  intro p
  change IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
    coordinateUnlinkExteriorModel ∞
    (rightCapping_rightSmoothCappingSeamTargetBase m) p
  exact rightCapping_isLocalDiffeomorph_rightSmoothCappingSeamTargetBase m p

/-- The direct right smooth capping is diffeomorphic to the right-tube power pullback equipped
with its literal standard-collar atlas. -/
noncomputable def coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph :
    letI := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel,
        coordinateUnlinkExteriorModel⟯
      CoordinateExteriorRightTubePowerPullback m := by
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    isManifold_signedSeamFamilyCommonModel m
  let _ := compactNeckRightCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckRightCut m) :=
    isManifold_compactNeckRightCut m
  let _ :=
    coordinateUnlinkExteriorCommonModelEuclideanFourBallFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBall) :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBallFamily m
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateExteriorRightTubePowerPullback m) :=
    isManifold_coordinateExteriorRightTubePowerPullbackStandard m
  exact diffeomorphOfCollaredPushoutHomeomorph
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap m)
    (coordinateUnlinkExteriorPlanarNeckRightSmoothCappingSeamMap_attaching_coverage m)
    (isManifold_coordinateUnlinkExteriorPlanarNeckRightSmoothCapping m)
    (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m)
    (isLocalDiffeomorph_coordinateExteriorPlanarNeckRightSmoothCappingRightTube_seam m)
    (isLocalDiffeomorph_coordinateExteriorPlanarNeckRightSmoothCappingRightTube_cutOffSeam m)
    (isLocalDiffeomorph_coordinateExteriorPlanarNeckRightSmoothCappingRightTube_capOffSeam m)

/-- The smooth comparison has the same forward function as the point-set comparison. -/
@[simp]
theorem coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph_apply
    (z : CoordinateUnlinkExteriorPlanarNeckRightSmoothCapping m) :
    letI := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph m z =
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m z := by
  rfl

/-- The inverse smooth comparison has the same function as the inverse point-set comparison. -/
@[simp]
theorem coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph_symm_apply
    (z : CoordinateExteriorRightTubePowerPullback m) :
    letI := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph m).symm z =
      (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m).symm z := by
  rfl

/-- The underlying homeomorphism of the smooth comparison is the point-set comparison. -/
theorem coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph_toHomeomorph :
    letI := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    (coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph m).toHomeomorph =
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m := by
  rfl

/-- The smooth comparison restricts on the compact-cut coprojection to the body map. -/
theorem coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph_inl
    (x : CompactNeckRightCut m) :
    letI := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x) =
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeBodyMap m x := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  change coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m
      (topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) x) = _
  exact coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph_inl m x

/-- The smooth comparison restricts on the rounded-cap coprojection to the cap map. -/
theorem coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph_inr
    (y : ZMod m × EuclideanFourBall) :
    letI := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
    letI := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
    coordinateExteriorPlanarNeckRightSmoothCappingRightTubeDiffeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) y) =
      coordinateExteriorPlanarNeckRightSmoothCappingRightTubeCapMap m y := by
  let _ := coordinateUnlinkExteriorPlanarNeckRightSmoothCappingChartedSpace m
  let _ := coordinateExteriorRightTubePowerPullbackStandardChartedSpace m
  change coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph m
      (topologicalPushoutInr
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckEuclideanFourBallAttachingMap m) y) = _
  exact coordinateExteriorPlanarNeckRightSmoothCappingRightTubeHomeomorph_inr m y

end SplittingSpheres
