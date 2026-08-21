/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.CoordinateUnlinkSignedSeamModel
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth strict halves of the signed seam reparametrization

The absolute-value reparametrization from the signed collar to the inward
four-ball collar is not smooth at time zero.  This file records precisely the
two statements needed by signed pushout seams: it is a local diffeomorphism on
the strict negative and strict positive time loci.
-/

@[expose] public section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

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
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.toContinuousLinearMap.contMDiff
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

private theorem contMDiff_signedSeamNegativeHalfReparamOpen_natural :
    letI := signedSeamCollarBoundaryChartedSpace
    ContMDiff coordinateUnlinkBoundaryCollarModel
      euclideanFourBallCollarModel ∞
      signedSeamNegativeHalfReparamOpen := by
  let _ := signedSeamIntervalChartedSpace
  let _ := signedSeamCollarBoundaryChartedSpace
  rw [← ContMDiff.subtypeVal_comp_iff signedSeamPositiveCollarOpens]
  unfold signedSeamNegativeHalfReparamOpen
  have hval : ContMDiff coordinateUnlinkBoundaryCollarModel
      coordinateUnlinkBoundaryCollarModel ∞
      (Subtype.val : signedSeamNegativeBaseOpens →
        Sphere 3 × EquatorCollarInterval) :=
    contMDiff_subtype_val
  have hfst : ContMDiff coordinateUnlinkBoundaryCollarModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
      (fun p : signedSeamNegativeBaseOpens ↦ p.1.1) :=
    contMDiff_fst.comp hval
  apply ContMDiff.prodMk hfst
  rw [← ContMDiff.subtypeVal_comp_iff euclideanFourBallCollarIntervalOpens]
  apply contMDiff_iff_comp_subtypeVal_Icc.mpr
  constructor
  · fun_prop
  · have hsnd : ContMDiff coordinateUnlinkBoundaryCollarModel
        (modelWithCornersEuclideanHalfSpace 1) ∞
        (fun p : signedSeamNegativeBaseOpens ↦ p.1.2) :=
      contMDiff_snd.comp hval
    have htime : ContMDiff coordinateUnlinkBoundaryCollarModel
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : signedSeamNegativeBaseOpens ↦ (p.1.2.1 : ℝ)) :=
      contMDiff_signedSeamInterval_value.comp hsnd
    exact htime.neg.congr fun _ ↦ rfl

private theorem contMDiff_signedSeamNegativeHalfReparamOpenInv_natural :
    letI := signedSeamCollarBoundaryChartedSpace
    ContMDiff euclideanFourBallCollarModel
      coordinateUnlinkBoundaryCollarModel ∞
      signedSeamNegativeHalfReparamOpenInv := by
  let _ := signedSeamIntervalChartedSpace
  let _ := signedSeamCollarBoundaryChartedSpace
  rw [← ContMDiff.subtypeVal_comp_iff signedSeamNegativeBaseOpens]
  unfold signedSeamNegativeHalfReparamOpenInv compactNeckLeftHalfParameter
  have hval : ContMDiff euclideanFourBallCollarModel
      euclideanFourBallCollarModel ∞
      (Subtype.val : signedSeamPositiveCollarOpens →
        EuclideanFourBallCollarDomain) :=
    contMDiff_subtype_val
  have hfst : ContMDiff euclideanFourBallCollarModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
      (fun p : signedSeamPositiveCollarOpens ↦ p.1.1) :=
    contMDiff_fst.comp hval
  have hsnd : ContMDiff euclideanFourBallCollarModel
      (modelWithCornersEuclideanHalfSpace 1) ∞
      (fun p : signedSeamPositiveCollarOpens ↦ p.1.2) :=
    contMDiff_snd.comp hval
  have hcollarValue : ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun t : EuclideanFourBallCollarInterval ↦ (t.1.1 : ℝ)) :=
    (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := (1 / 2 : ℝ))).comp
      contMDiff_subtype_val
  have htime : ContMDiff euclideanFourBallCollarModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : signedSeamPositiveCollarOpens ↦ -(p.1.2.1.1 : ℝ)) :=
    (hcollarValue.comp hsnd).neg
  have hinterval : ContMDiff euclideanFourBallCollarModel
      (modelWithCornersEuclideanHalfSpace 1) ∞
      (fun p : signedSeamPositiveCollarOpens ↦
        ⟨-(p.1.2.1.1 : ℝ), by
          constructor
          · exact neg_lt_neg p.1.2.2
          · linarith [p.1.2.1.2.1]⟩ :
          signedSeamPositiveCollarOpens → EquatorCollarInterval) :=
    contMDiff_to_signedSeamInterval_of_value
      euclideanFourBallCollarModel _ (by fun_prop) htime
  exact ContMDiff.prodMk hfst hinterval

private theorem contMDiff_signedSeamPositiveHalfReparamOpen_natural :
    letI := signedSeamCollarBoundaryChartedSpace
    ContMDiff coordinateUnlinkBoundaryCollarModel
      euclideanFourBallCollarModel ∞
      signedSeamPositiveHalfReparamOpen := by
  let _ := signedSeamIntervalChartedSpace
  let _ := signedSeamCollarBoundaryChartedSpace
  rw [← ContMDiff.subtypeVal_comp_iff signedSeamPositiveCollarOpens]
  unfold signedSeamPositiveHalfReparamOpen
  have hval : ContMDiff coordinateUnlinkBoundaryCollarModel
      coordinateUnlinkBoundaryCollarModel ∞
      (Subtype.val : signedSeamPositiveBaseOpens →
        Sphere 3 × EquatorCollarInterval) :=
    contMDiff_subtype_val
  have hfst : ContMDiff coordinateUnlinkBoundaryCollarModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
      (fun p : signedSeamPositiveBaseOpens ↦ p.1.1) :=
    contMDiff_fst.comp hval
  apply ContMDiff.prodMk hfst
  rw [← ContMDiff.subtypeVal_comp_iff euclideanFourBallCollarIntervalOpens]
  apply contMDiff_iff_comp_subtypeVal_Icc.mpr
  constructor
  · fun_prop
  · have hsnd : ContMDiff coordinateUnlinkBoundaryCollarModel
        (modelWithCornersEuclideanHalfSpace 1) ∞
        (fun p : signedSeamPositiveBaseOpens ↦ p.1.2) :=
      contMDiff_snd.comp hval
    have htime : ContMDiff coordinateUnlinkBoundaryCollarModel
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : signedSeamPositiveBaseOpens ↦ (p.1.2.1 : ℝ)) :=
      contMDiff_signedSeamInterval_value.comp hsnd
    exact htime.congr fun _ ↦ rfl

private theorem contMDiff_signedSeamPositiveHalfReparamOpenInv_natural :
    letI := signedSeamCollarBoundaryChartedSpace
    ContMDiff euclideanFourBallCollarModel
      coordinateUnlinkBoundaryCollarModel ∞
      signedSeamPositiveHalfReparamOpenInv := by
  let _ := signedSeamIntervalChartedSpace
  let _ := signedSeamCollarBoundaryChartedSpace
  rw [← ContMDiff.subtypeVal_comp_iff signedSeamPositiveBaseOpens]
  unfold signedSeamPositiveHalfReparamOpenInv compactNeckRightHalfParameter
  have hval : ContMDiff euclideanFourBallCollarModel
      euclideanFourBallCollarModel ∞
      (Subtype.val : signedSeamPositiveCollarOpens →
        EuclideanFourBallCollarDomain) :=
    contMDiff_subtype_val
  have hfst : ContMDiff euclideanFourBallCollarModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
      (fun p : signedSeamPositiveCollarOpens ↦ p.1.1) :=
    contMDiff_fst.comp hval
  have hsnd : ContMDiff euclideanFourBallCollarModel
      (modelWithCornersEuclideanHalfSpace 1) ∞
      (fun p : signedSeamPositiveCollarOpens ↦ p.1.2) :=
    contMDiff_snd.comp hval
  have hcollarValue : ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun t : EuclideanFourBallCollarInterval ↦ (t.1.1 : ℝ)) :=
    (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := (1 / 2 : ℝ))).comp
      contMDiff_subtype_val
  have htime : ContMDiff euclideanFourBallCollarModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : signedSeamPositiveCollarOpens ↦ (p.1.2.1.1 : ℝ)) :=
    hcollarValue.comp hsnd
  have hinterval : ContMDiff euclideanFourBallCollarModel
      (modelWithCornersEuclideanHalfSpace 1) ∞
      (fun p : signedSeamPositiveCollarOpens ↦
        ⟨(p.1.2.1.1 : ℝ), by
          constructor
          · linarith [p.1.2.1.2.1]
          · exact p.1.2.2⟩ :
          signedSeamPositiveCollarOpens → EquatorCollarInterval) :=
    contMDiff_to_signedSeamInterval_of_value
      euclideanFourBallCollarModel _ (by fun_prop) htime
  exact ContMDiff.prodMk hfst hinterval

private theorem contMDiff_signedSeamBaseOpenIdentity_commonToBoundary
    (U : Opens (Sphere 3 × EquatorCollarInterval)) :
    letI := signedSeamCommonModelChartedSpace
    letI := signedSeamCollarBoundaryChartedSpace
    ContMDiff coordinateUnlinkExteriorModel
      coordinateUnlinkBoundaryCollarModel ∞
      (id : U → U) := by
  let _ := signedSeamIntervalChartedSpace
  let _ := signedSeamCommonModelChartedSpace
  let _ := signedSeamCollarBoundaryChartedSpace
  rw [← ContMDiff.subtypeVal_comp_iff U]
  have h := signedSeamCommonBoundaryIdentityDiffeomorph.contMDiff.comp
    (contMDiff_subtype_val : ContMDiff coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Subtype.val : U →
        Sphere 3 × EquatorCollarInterval))
  simpa [Function.comp_def] using h

private theorem contMDiff_signedSeamBaseOpenIdentity_boundaryToCommon
    (U : Opens (Sphere 3 × EquatorCollarInterval)) :
    letI := signedSeamCollarBoundaryChartedSpace
    letI := signedSeamCommonModelChartedSpace
    ContMDiff coordinateUnlinkBoundaryCollarModel
      coordinateUnlinkExteriorModel ∞
      (id : U → U) := by
  let _ := signedSeamIntervalChartedSpace
  let _ := signedSeamCollarBoundaryChartedSpace
  let _ := signedSeamCommonModelChartedSpace
  rw [← ContMDiff.subtypeVal_comp_iff U]
  have h := signedSeamCommonBoundaryIdentityDiffeomorph.symm.contMDiff.comp
    (contMDiff_subtype_val : ContMDiff coordinateUnlinkBoundaryCollarModel
      coordinateUnlinkBoundaryCollarModel ∞
      (Subtype.val : U →
        Sphere 3 × EquatorCollarInterval))
  exact h.congr fun x ↦ by rfl

private theorem contMDiff_signedSeamPositiveCollarIdentity_naturalToCommon :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    ContMDiff euclideanFourBallCollarModel
      coordinateUnlinkExteriorModel ∞
      (id : signedSeamPositiveCollarOpens →
        signedSeamPositiveCollarOpens) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  rw [← ContMDiff.subtypeVal_comp_iff signedSeamPositiveCollarOpens]
  have h := coordinateUnlinkExteriorRechartedFourBallCollarIdentity_contMDiff.2.comp
    (contMDiff_subtype_val : ContMDiff euclideanFourBallCollarModel
      euclideanFourBallCollarModel ∞
      (Subtype.val : signedSeamPositiveCollarOpens →
        EuclideanFourBallCollarDomain))
  simpa [Function.comp_def] using h

private theorem contMDiff_signedSeamPositiveCollarIdentity_commonToNatural :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    ContMDiff coordinateUnlinkExteriorModel
      euclideanFourBallCollarModel ∞
      (id : signedSeamPositiveCollarOpens →
        signedSeamPositiveCollarOpens) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  rw [← ContMDiff.subtypeVal_comp_iff signedSeamPositiveCollarOpens]
  have h := coordinateUnlinkExteriorRechartedFourBallCollarIdentity_contMDiff.1.comp
    (contMDiff_subtype_val : ContMDiff coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Subtype.val : signedSeamPositiveCollarOpens →
        EuclideanFourBallCollarDomain))
  simpa [Function.comp_def] using h

private noncomputable def signedSeamNegativeHalfReparamOpenDiffeomorph :
    letI := signedSeamCommonModelChartedSpace
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    signedSeamNegativeBaseOpens ≃ₘ^∞⟮
      coordinateUnlinkExteriorModel,
      coordinateUnlinkExteriorModel⟯
      signedSeamPositiveCollarOpens := by
  let _ := signedSeamIntervalChartedSpace
  let _ := signedSeamCollarBoundaryChartedSpace
  let _ := signedSeamCommonModelChartedSpace
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  refine
    { toEquiv := signedSeamNegativeHalfReparamOpenEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · have h := contMDiff_signedSeamPositiveCollarIdentity_naturalToCommon.comp
      (contMDiff_signedSeamNegativeHalfReparamOpen_natural.comp
        (contMDiff_signedSeamBaseOpenIdentity_commonToBoundary
          signedSeamNegativeBaseOpens))
    exact h.congr fun _ ↦ rfl
  · have h := (contMDiff_signedSeamBaseOpenIdentity_boundaryToCommon
        signedSeamNegativeBaseOpens).comp
      (contMDiff_signedSeamNegativeHalfReparamOpenInv_natural.comp
        contMDiff_signedSeamPositiveCollarIdentity_commonToNatural)
    exact h.congr fun _ ↦ rfl

private noncomputable def signedSeamPositiveHalfReparamOpenDiffeomorph :
    letI := signedSeamCommonModelChartedSpace
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    signedSeamPositiveBaseOpens ≃ₘ^∞⟮
      coordinateUnlinkExteriorModel,
      coordinateUnlinkExteriorModel⟯
      signedSeamPositiveCollarOpens := by
  let _ := signedSeamIntervalChartedSpace
  let _ := signedSeamCollarBoundaryChartedSpace
  let _ := signedSeamCommonModelChartedSpace
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  refine
    { toEquiv := signedSeamPositiveHalfReparamOpenEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · have h := contMDiff_signedSeamPositiveCollarIdentity_naturalToCommon.comp
      (contMDiff_signedSeamPositiveHalfReparamOpen_natural.comp
        (contMDiff_signedSeamBaseOpenIdentity_commonToBoundary
          signedSeamPositiveBaseOpens))
    exact h.congr fun _ ↦ rfl
  · have h := (contMDiff_signedSeamBaseOpenIdentity_boundaryToCommon
        signedSeamPositiveBaseOpens).comp
      (contMDiff_signedSeamPositiveHalfReparamOpenInv_natural.comp
        contMDiff_signedSeamPositiveCollarIdentity_commonToNatural)
    exact h.congr fun _ ↦ rfl

private theorem isLocalDiffeomorphAt_of_openDiffeomorph
    {E F H K M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace K]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K)
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N]
    (U : Opens M) (V : Opens N) (f : M → N)
    (e : U ≃ₘ^∞⟮I, J⟯ V)
    (heq : ∀ p : U, (e p).1 = f p.1)
    (x : M) (hx : x ∈ U) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  let u : U := ⟨x, hx⟩
  let hU : IsLocalDiffeomorphAt I I ∞
      (Subtype.val : U → M) u :=
    isLocalDiffeomorph_opensSubtypeVal I U u
  let hV : IsLocalDiffeomorphAt J J ∞
      (Subtype.val : V → N) (e u) :=
    isLocalDiffeomorph_opensSubtypeVal J V (e u)
  let Φ0 : PartialDiffeomorph I J M V ∞ :=
    hU.localInverse.trans e.toPartialDiffeomorph
  let Φ : PartialDiffeomorph I J M N ∞ :=
    Φ0.trans (Classical.choose hV)
  refine ⟨Φ, ?_, ?_⟩
  · change x ∈ Φ0.source ∩ Φ0 ⁻¹' (Classical.choose hV).source
    refine ⟨?_, ?_⟩
    · change x ∈ hU.localInverse.source ∩
        hU.localInverse ⁻¹' e.toPartialDiffeomorph.source
      refine ⟨hU.localInverse_mem_source, ?_⟩
      change hU.localInverse x ∈ (Set.univ : Set U)
      trivial
    · change e (hU.localInverse x) ∈ (Classical.choose hV).source
      rw [hU.localInverse_left_inv hU.localInverse_mem_target]
      exact (Classical.choose_spec hV).1
  · intro y hy
    have hyInv : y ∈ hU.localInverse.source := hy.1.1
    have hyV : Φ0 y ∈ (Classical.choose hV).source := hy.2
    calc
      f y = f (hU.localInverse y : M) :=
        congrArg f (hU.localInverse_right_inv hyInv).symm
      _ = (e (hU.localInverse y) : N) := (heq _).symm
      _ = (Φ0 y : V) := rfl
      _ = (Classical.choose hV) (Φ0 y) :=
        (Classical.choose_spec hV).2 hyV
      _ = Φ y := rfl

private theorem isLocalDiffeomorphOn_signedSeamBaseHalfReparam_negative :
    letI := signedSeamCommonModelChartedSpace
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦
        (p.1, signedSeamUnsignedCollarInterval p.2))
      {p | (p.2.1 : ℝ) < 0} := by
  let _ := signedSeamCommonModelChartedSpace
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  intro p
  apply isLocalDiffeomorphAt_of_openDiffeomorph
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    signedSeamNegativeBaseOpens signedSeamPositiveCollarOpens
    (fun q : Sphere 3 × EquatorCollarInterval ↦
      (q.1, signedSeamUnsignedCollarInterval q.2))
    signedSeamNegativeHalfReparamOpenDiffeomorph
    _ p.1 p.2
  intro q
  change (signedSeamNegativeHalfReparamOpen q).1 =
    (q.1.1, signedSeamUnsignedCollarInterval q.1.2)
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply Subtype.ext
    change -(q.1.2.1 : ℝ) = |(q.1.2.1 : ℝ)|
    rw [abs_of_neg q.2]

private theorem isLocalDiffeomorphOn_signedSeamBaseHalfReparam_positive :
    letI := signedSeamCommonModelChartedSpace
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦
        (p.1, signedSeamUnsignedCollarInterval p.2))
      {p | 0 < (p.2.1 : ℝ)} := by
  let _ := signedSeamCommonModelChartedSpace
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  intro p
  apply isLocalDiffeomorphAt_of_openDiffeomorph
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    signedSeamPositiveBaseOpens signedSeamPositiveCollarOpens
    (fun q : Sphere 3 × EquatorCollarInterval ↦
      (q.1, signedSeamUnsignedCollarInterval q.2))
    signedSeamPositiveHalfReparamOpenDiffeomorph
    _ p.1 p.2
  intro q
  change (signedSeamPositiveHalfReparamOpen q).1 =
    (q.1.1, signedSeamUnsignedCollarInterval q.1.2)
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply Subtype.ext
    change (q.1.2.1 : ℝ) = |(q.1.2.1 : ℝ)|
    rw [abs_of_pos q.2]

private theorem isLocalDiffeomorphAt_congr_of_eqOn_open
    {E F H K M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace K]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K)
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N]
    {f g : M → N} {x : M} (hg : IsLocalDiffeomorphAt I J ∞ g x)
    (W : Set M) (hW : IsOpen W) (hxW : x ∈ W)
    (heq : EqOn f g W) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  let Ψ := Classical.choose hg
  let q := Ψ.toOpenPartialHomeomorph.restrOpen W hW
  let Φ : PartialDiffeomorph I J M N ∞ :=
    { toPartialEquiv := q.toPartialEquiv
      open_source := q.open_source
      open_target := q.open_target
      contMDiffOn_toFun := by
        apply Ψ.contMDiffOn_toFun.mono
        intro y hy
        change y ∈ Ψ.source ∩ W at hy
        exact hy.1
      contMDiffOn_invFun := by
        apply Ψ.contMDiffOn_invFun.mono
        intro y hy
        change y ∈ Ψ.target ∩ Ψ.symm ⁻¹' W at hy
        exact hy.1 }
  refine ⟨Φ, ?_, ?_⟩
  · change x ∈ Ψ.source ∩ W
    exact ⟨(Classical.choose_spec hg).1, hxW⟩
  · intro y hy
    change y ∈ Ψ.source ∩ W at hy
    exact (heq hy.2).trans ((Classical.choose_spec hg).2 hy.1)

private theorem isLocalDiffeomorphAt_congr_of_eventuallyEq
    {E F H K M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace K]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K)
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N]
    {f g : M → N} {x : M} (hg : IsLocalDiffeomorphAt I J ∞ g x)
    (heq : f =ᶠ[nhds x] g) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp heq
  exact isLocalDiffeomorphAt_congr_of_eqOn_open I J hg W hWopen hxW
    (fun y hy ↦ hWsub hy)

private theorem isLocalDiffeomorphAt_signedSeamFamilyMap_of_base
    (m : ℕ)
    (f : Sphere 3 × EquatorCollarInterval →
      EuclideanFourBallCollarDomain)
    (x : ZMod m × (Sphere 3 × EquatorCollarInterval))
    (hf :
      letI := signedSeamCommonModelChartedSpace
      letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
      IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞ f x.2) :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (fun z ↦ (z.1, f z.2)) x := by
  let _ := signedSeamCommonModelChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCommonModel
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × (Sphere 3 × EquatorCollarInterval)) :=
    isManifold_signedSeamFamilyCommonModel m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (ZMod m × EuclideanFourBallCollarDomain) :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarFamily m
  have hsndSource : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × (Sphere 3 × EquatorCollarInterval) →
        Sphere 3 × EquatorCollarInterval) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := Sphere 3 × EquatorCollarInterval))
  have hsndTarget : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd : ZMod m × EuclideanFourBallCollarDomain →
        EuclideanFourBallCollarDomain) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := EuclideanFourBallCollarDomain))
  let u : ZMod m × (Sphere 3 × EquatorCollarInterval) →
      EuclideanFourBallCollarDomain := fun z ↦ f z.2
  have hu : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ u x := by
    simpa [u, Function.comp_def] using
      (hsndSource x).comp coordinateUnlinkExteriorModel
        EuclideanFourBallCollarDomain hf
  let targetPoint : ZMod m × EuclideanFourBallCollarDomain :=
    (x.1, f x.2)
  let htarget := hsndTarget targetPoint
  let g : ZMod m × (Sphere 3 × EquatorCollarInterval) →
      ZMod m × EuclideanFourBallCollarDomain :=
    fun z ↦ htarget.localInverse (u z)
  have hg : IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ g x := by
    have hcomp := hu.comp coordinateUnlinkExteriorModel
      (ZMod m × EuclideanFourBallCollarDomain)
      htarget.localInverse_isLocalDiffeomorphAt
    simpa [g, Function.comp_def] using hcomp
  apply isLocalDiffeomorphAt_congr_of_eventuallyEq
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel hg
  have huCont : ContinuousAt u x := hu.contMDiffAt.continuousAt
  have hinvValue : htarget.localInverse (u x) = targetPoint :=
    htarget.localInverse_left_inv htarget.localInverse_mem_target
  have hsource : ∀ᶠ z in nhds x, u z ∈ htarget.localInverse.source :=
    huCont (htarget.localInverse.open_source.mem_nhds
      htarget.localInverse_mem_source)
  have hinvLabelAt :
      {z : ZMod m × EuclideanFourBallCollarDomain | z.1 = x.1} ∈
        nhds (htarget.localInverse (u x)) := by
    rw [hinvValue]
    exact ((isOpen_discrete ({x.1} : Set (ZMod m))).preimage
      continuous_fst).mem_nhds (by simp [targetPoint])
  have hinvLabel : ∀ᶠ z in nhds x,
      (htarget.localInverse (u z)).1 = x.1 :=
    huCont (htarget.localInverse_contMDiffAt.continuousAt hinvLabelAt)
  have hsourceLabel : ∀ᶠ z in nhds x, z.1 = x.1 :=
    ((isOpen_discrete ({x.1} : Set (ZMod m))).preimage
      continuous_fst).mem_nhds (by simp)
  filter_upwards [hsource, hinvLabel, hsourceLabel] with z hzSource hzInvLabel hzLabel
  apply Prod.ext
  · exact hzLabel.trans hzInvLabel.symm
  · exact (htarget.localInverse_right_inv hzSource).symm

/-- On the strict negative-time locus, forgetting the sign of signed seam time
is a local diffeomorphism to the labelled inward collar family. -/
theorem isLocalDiffeomorphOn_signedSeamHalfReparam_negative (m : ℕ) :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (signedSeamHalfReparam m)
      {p | signedSeamTime m p < 0} := by
  let _ := signedSeamCommonModelChartedSpace
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  intro p
  have hbase := isLocalDiffeomorphOn_signedSeamBaseHalfReparam_negative
    ⟨p.1.2, p.2⟩
  have hfamily := isLocalDiffeomorphAt_signedSeamFamilyMap_of_base m
    (fun q : Sphere 3 × EquatorCollarInterval ↦
      (q.1, signedSeamUnsignedCollarInterval q.2)) p.1 hbase
  change IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
    coordinateUnlinkExteriorModel ∞
    (fun z : ZMod m × (Sphere 3 × EquatorCollarInterval) ↦
      (z.1, (z.2.1, signedSeamUnsignedCollarInterval z.2.2))) p.1
  exact hfamily

/-- On the strict positive-time locus, forgetting the sign of signed seam time
is a local diffeomorphism to the labelled inward collar family. -/
theorem isLocalDiffeomorphOn_signedSeamHalfReparam_positive (m : ℕ) :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
    IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ (signedSeamHalfReparam m)
      {p | 0 < signedSeamTime m p} := by
  let _ := signedSeamCommonModelChartedSpace
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  intro p
  have hbase := isLocalDiffeomorphOn_signedSeamBaseHalfReparam_positive
    ⟨p.1.2, p.2⟩
  have hfamily := isLocalDiffeomorphAt_signedSeamFamilyMap_of_base m
    (fun q : Sphere 3 × EquatorCollarInterval ↦
      (q.1, signedSeamUnsignedCollarInterval q.2)) p.1 hbase
  change IsLocalDiffeomorphAt coordinateUnlinkExteriorModel
    coordinateUnlinkExteriorModel ∞
    (fun z : ZMod m × (Sphere 3 × EquatorCollarInterval) ↦
      (z.1, (z.2.1, signedSeamUnsignedCollarInterval z.2.2))) p.1
  exact hfamily

end SplittingSpheres

end
