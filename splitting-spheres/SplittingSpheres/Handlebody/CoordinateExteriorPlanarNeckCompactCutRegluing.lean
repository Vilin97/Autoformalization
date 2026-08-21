/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import
  SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckSmoothCappingDiffeomorphismRecognition
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckSmoothCappingRadialBoundary
import SplittingSpheres.Handlebody.CoordinateExteriorPowerCompactness
import SplittingSpheres.Foundations.TopologicalPushoutHomeomorph
import all SplittingSpheres.Geometry.CoordinateUnlinkSignedSeamSmoothHalves
import all SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckCompactCutSmooth
import all SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckSmoothCapping

/-!
# Regluing the two compact planar-neck cut sides

The compact coordinate exterior is recovered by gluing its two direct smooth cut sides along
their common labelled family `ZMod m × Sphere 3`.  The generated pushout atlas uses the literal
inward cut collars and the direct common-model signed seam.  Its comparison with the original
compact coordinate exterior is a genuine diffeomorphism: on both coprojections it is exactly
subtype inclusion.

No capped one-handle comparison or connected-sum classification is used here.  In particular,
the proof does not transport an atlas through a homeomorphism.
-/

@[expose] public section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

variable (m : ℕ) [NeZero m]

/-- The direct pushout of the two compact cut sides along their common labelled seam. -/
abbrev CoordinateUnlinkExteriorPlanarCompactCutPushout :=
  TopologicalPushout
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)

private theorem compactCutLeftAttaching_coe
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

private theorem compactCutRightAttaching_coe
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

private def compactCutLeftInclusion :
    C(CompactNeckLeftCut m,
      CoordinateUnlinkExteriorEighthPowerPullback m) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def compactCutRightInclusion :
    C(CompactNeckRightCut m,
      CoordinateUnlinkExteriorEighthPowerPullback m) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private theorem compactCutAttaching_compatible (p : ZMod m × Sphere 3) :
    compactCutLeftInclusion m
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m p) =
      compactCutRightInclusion m
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m p) :=
  (compactCutLeftAttaching_coe m p).trans
    (compactCutRightAttaching_coe m p).symm

private theorem compactCut_cross
    (x : CompactNeckLeftCut m) (y : CompactNeckRightCut m)
    (hxy : compactCutLeftInclusion m x = compactCutRightInclusion m y) :
    ∃ a, coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m a = x ∧
      coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m a = y := by
  have hxInter : x.1 ∈
      coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m ∩
        coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m := by
    refine ⟨x.2, ?_⟩
    change x.1 = y.1 at hxy
    rw [hxy]
    exact y.2
  have hxSeam : x.1 ∈ coordinateUnlinkExteriorPlanarCompactNeckStarSeam m := by
    rw [← inter_coordinateUnlinkExteriorPlanarCompactNeckStarCutCarriers m]
    exact hxInter
  have hxRange : x ∈
      range (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m) := by
    rw [range_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m]
    exact hxSeam
  obtain ⟨a, ha⟩ := hxRange
  refine ⟨a, ha, ?_⟩
  apply Subtype.ext
  calc
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m a).1 =
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m a).1 :=
      (compactCutAttaching_compatible m a).symm
    _ = x.1 := congrArg Subtype.val ha
    _ = y.1 := hxy

private theorem compactCut_cover :
    range (compactCutLeftInclusion m) ∪
        range (compactCutRightInclusion m) =
      (univ : Set (CoordinateUnlinkExteriorEighthPowerPullback m)) := by
  ext z
  constructor
  · intro _
    exact mem_univ z
  · intro _
    have hz : z ∈ coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m ∪
        coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m := by
      rw [union_coordinateUnlinkExteriorPlanarCompactNeckStarCutCarriers m]
      exact mem_univ z
    rcases hz with hz | hz
    · exact Or.inl ⟨⟨z, hz⟩, rfl⟩
    · exact Or.inr ⟨⟨z, hz⟩, rfl⟩

private noncomputable def compactCutPushoutHomeomorph :
    CoordinateUnlinkExteriorPlanarCompactCutPushout m ≃ₜ
      CoordinateUnlinkExteriorEighthPowerPullback m := by
  let _ : CompactSpace (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    compactSpace_coordinateUnlinkExteriorEighthPowerPullback m
  let _ : CompactSpace (CompactNeckLeftCut m) :=
    isCompact_iff_compactSpace.mp
      (isClosed_coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m).isCompact
  let _ : CompactSpace (CompactNeckRightCut m) :=
    isCompact_iff_compactSpace.mp
      (isClosed_coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m).isCompact
  exact topologicalPushoutHomeomorph
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (compactCutLeftInclusion m) (compactCutRightInclusion m)
    (compactCutAttaching_compatible m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m).injective
    Subtype.val_injective Subtype.val_injective (compactCut_cross m) (compactCut_cover m)

private theorem compactCutPushoutHomeomorph_inl
    (x : CompactNeckLeftCut m) :
    compactCutPushoutHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m) x) = x.1 := by
  let _ : CompactSpace (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    compactSpace_coordinateUnlinkExteriorEighthPowerPullback m
  let _ : CompactSpace (CompactNeckLeftCut m) :=
    isCompact_iff_compactSpace.mp
      (isClosed_coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m).isCompact
  let _ : CompactSpace (CompactNeckRightCut m) :=
    isCompact_iff_compactSpace.mp
      (isClosed_coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m).isCompact
  exact topologicalPushoutHomeomorph_inl
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (compactCutLeftInclusion m) (compactCutRightInclusion m)
    (compactCutAttaching_compatible m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m).injective
    Subtype.val_injective Subtype.val_injective (compactCut_cross m)
    (compactCut_cover m) x

private theorem compactCutPushoutHomeomorph_inr
    (x : CompactNeckRightCut m) :
    compactCutPushoutHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m) x) = x.1 := by
  let _ : CompactSpace (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    compactSpace_coordinateUnlinkExteriorEighthPowerPullback m
  let _ : CompactSpace (CompactNeckLeftCut m) :=
    isCompact_iff_compactSpace.mp
      (isClosed_coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m).isCompact
  let _ : CompactSpace (CompactNeckRightCut m) :=
    isCompact_iff_compactSpace.mp
      (isClosed_coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m).isCompact
  exact topologicalPushoutHomeomorph_inr
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (compactCutLeftInclusion m) (compactCutRightInclusion m)
    (compactCutAttaching_compatible m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m).injective
    Subtype.val_injective Subtype.val_injective (compactCut_cross m)
    (compactCut_cover m) x

/-- The signed seam chart built from the literal inward collars of the two cut sides. -/
def coordinateUnlinkExteriorPlanarCompactCutPushoutSeamMap :
    CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m →
      CoordinateUnlinkExteriorPlanarCompactCutPushout m :=
  topologicalPushoutSeamMap
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (signedSeamTime m)
    (coordinateUnlinkExteriorPlanarNeckLeftCutSeamBranch m)
    (coordinateUnlinkExteriorPlanarNeckRightCutSeamBranch m)

private theorem compactCutPushoutSeamMap_isOpenEmbedding :
    IsOpenEmbedding
      (coordinateUnlinkExteriorPlanarCompactCutPushoutSeamMap m) := by
  have hf : smoothCappingAttachingMapOfCollar m
      (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
      (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutCollar m).continuous =
    coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m := by
    apply ContinuousMap.ext
    intro p
    change coordinateUnlinkExteriorPlanarNeckLeftCutCollar m
      (p.1, (p.2, euclideanFourBallCollarZero)) = _
    rfl
  have hg : smoothCappingAttachingMapOfCollar m
      (coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
      (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutCollar m).continuous =
    coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m := by
    apply ContinuousMap.ext
    intro p
    change coordinateUnlinkExteriorPlanarNeckRightCutCollar m
      (p.1, (p.2, euclideanFourBallCollarZero)) = _
    rfl
  have hleft : smoothCappingBranchOfCollar m
      (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m) =
    coordinateUnlinkExteriorPlanarNeckLeftCutSeamBranch m := rfl
  have hright : smoothCappingBranchOfCollar m
      (coordinateUnlinkExteriorPlanarNeckRightCutCollar m) =
    coordinateUnlinkExteriorPlanarNeckRightCutSeamBranch m := rfl
  have h := isOpenEmbedding_smoothCappingSeamMapOfCollars m
    (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
    (coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
  rw [smoothCappingSeamMapOfCollars, hf, hg, hleft, hright] at h
  exact h

private theorem compactCutPushoutSeamMap_attaching_coverage
    (a : ZMod m × Sphere 3) :
    ∃ q, coordinateUnlinkExteriorPlanarCompactCutPushoutSeamMap m q =
      topologicalPushoutInl
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
        (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m a) := by
  have hf : smoothCappingAttachingMapOfCollar m
      (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
      (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutCollar m).continuous =
    coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m := by
    apply ContinuousMap.ext
    intro p
    change coordinateUnlinkExteriorPlanarNeckLeftCutCollar m
      (p.1, (p.2, euclideanFourBallCollarZero)) = _
    rfl
  have hg : smoothCappingAttachingMapOfCollar m
      (coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
      (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutCollar m).continuous =
    coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m := by
    apply ContinuousMap.ext
    intro p
    change coordinateUnlinkExteriorPlanarNeckRightCutCollar m
      (p.1, (p.2, euclideanFourBallCollarZero)) = _
    rfl
  have hleft : smoothCappingBranchOfCollar m
      (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m) =
    coordinateUnlinkExteriorPlanarNeckLeftCutSeamBranch m := rfl
  have hright : smoothCappingBranchOfCollar m
      (coordinateUnlinkExteriorPlanarNeckRightCutCollar m) =
    coordinateUnlinkExteriorPlanarNeckRightCutSeamBranch m := rfl
  have h := smoothCappingSeamMap_attaching_coverage m
    (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
    (coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutCollar m) a
  rw [smoothCappingSeamMapOfCollars, hf, hg, hleft, hright] at h
  exact h

@[instance_reducible]
private noncomputable def compactCutPushoutChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorPlanarCompactCutPushout m) := by
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ := compactNeckLeftCutChartedSpace m
  let _ := compactNeckRightCutChartedSpace m
  exact topologicalPushoutChartedSpace
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarCompactCutPushoutSeamMap m)
    (compactCutPushoutSeamMap_isOpenEmbedding m)
    (compactCutPushoutSeamMap_attaching_coverage m)

private theorem compactCutPushout_isManifold :
    letI := compactCutPushoutChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarCompactCutPushout m) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := compactNeckLeftCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckLeftCut m) :=
    isManifold_compactNeckLeftCut m
  let _ := compactNeckRightCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckRightCut m) :=
    isManifold_compactNeckRightCut m
  exact isManifold_smoothCappingPushoutOfCollars m
    (coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
    (isLocalDiffeomorph_coordinateUnlinkExteriorPlanarNeckLeftCutCollar m)
    (coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
    (isOpenEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutCollar m)
    (isLocalDiffeomorph_coordinateUnlinkExteriorPlanarNeckRightCutCollar m)

private theorem compactCut_isLocalDiffeomorphAt_congr_of_eqOn_open
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

private theorem compactCut_isLocalDiffeomorphAt_congr_of_eventuallyEq
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
  exact compactCut_isLocalDiffeomorphAt_congr_of_eqOn_open hg W hWopen hxW
    (fun y hy ↦ hWsub hy)

private theorem compactCut_reflect_isLocalDiffeomorph
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
  apply compactCut_isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp
  filter_upwards [hpx.localInverse_eventuallyEq_left.comp_tendsto
    hf.continuousAt] with y hy
  simpa only [Function.comp_apply, id_eq] using hy.symm

private theorem compactNeckLeftCutOffMap_isLocalDiffeomorph :
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

private theorem compactNeckRightCutOffMap_isLocalDiffeomorph :
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

private abbrev CompactCutPushoutLeftOffSeam :=
  ↑(topologicalPushoutInlOffSeamOpens
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m))

private abbrev CompactCutPushoutRightOffSeam :=
  ↑(topologicalPushoutInrOffSeamOpens
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m))

private abbrev CompactCutAmbientLeftOffSeam :=
  ↑(collaredCutSideOffBoundaryOpens
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckLeftCut_offBoundary m))

private abbrev CompactCutAmbientRightOffSeam :=
  ↑(collaredCutSideOffBoundaryOpens
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckRightCut_offBoundary m))

private def compactCutPushoutLeftOffSeamHomeomorphAmbient :
    CompactCutPushoutLeftOffSeam m ≃ₜ CompactCutAmbientLeftOffSeam m where
  toFun x := ⟨x.1.1, x.1.2, by
    intro hxSeam
    apply x.2
    rw [range_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m]
    exact hxSeam⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, by
    intro hxRange
    rw [range_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m] at hxRange
    exact x.2.2 hxRange⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def compactCutPushoutRightOffSeamHomeomorphAmbient :
    CompactCutPushoutRightOffSeam m ≃ₜ CompactCutAmbientRightOffSeam m where
  toFun x := ⟨x.1.1, x.1.2, by
    intro hxSeam
    apply x.2
    rw [range_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m]
    exact hxSeam⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, by
    intro hxRange
    rw [range_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m] at hxRange
    exact x.2.2 hxRange⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem compactCutPushoutLeftOffSeamHomeomorphAmbient_isLocalDiffeomorph :
    letI := compactNeckLeftCutChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      (compactCutPushoutLeftOffSeamHomeomorphAmbient m) := by
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := compactNeckLeftCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckLeftCut m) :=
    isManifold_compactNeckLeftCut m
  let p := collaredCutSideOffBoundaryOpensMap
    (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckLeftCut_offBoundary m)
  apply compactCut_reflect_isLocalDiffeomorph p
    (compactCutPushoutLeftOffSeamHomeomorphAmbient m)
    (compactNeckLeftCutOffMap_isLocalDiffeomorph m)
    (compactCutPushoutLeftOffSeamHomeomorphAmbient m).continuous
  have hval := isLocalDiffeomorph_opensSubtypeVal coordinateUnlinkExteriorModel
    (topologicalPushoutInlOffSeamOpens
      (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m))
  change IsLocalDiffeomorph coordinateUnlinkExteriorModel
    coordinateUnlinkExteriorModel ∞
    (Subtype.val : CompactCutPushoutLeftOffSeam m → CompactNeckLeftCut m)
  exact hval

private theorem compactCutPushoutRightOffSeamHomeomorphAmbient_isLocalDiffeomorph :
    letI := compactNeckRightCutChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      (compactCutPushoutRightOffSeamHomeomorphAmbient m) := by
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := compactNeckRightCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckRightCut m) :=
    isManifold_compactNeckRightCut m
  let p := collaredCutSideOffBoundaryOpensMap
    (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
    (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
    (isOpen_compactNeckRightCut_offBoundary m)
  apply compactCut_reflect_isLocalDiffeomorph p
    (compactCutPushoutRightOffSeamHomeomorphAmbient m)
    (compactNeckRightCutOffMap_isLocalDiffeomorph m)
    (compactCutPushoutRightOffSeamHomeomorphAmbient m).continuous
  have hval := isLocalDiffeomorph_opensSubtypeVal coordinateUnlinkExteriorModel
    (topologicalPushoutInrOffSeamOpens
      (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
      (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m))
  change IsLocalDiffeomorph coordinateUnlinkExteriorModel
    coordinateUnlinkExteriorModel ∞
    (Subtype.val : CompactCutPushoutRightOffSeam m → CompactNeckRightCut m)
  exact hval

private theorem compactCutPushoutHomeomorph_leftOffSeam_isLocalDiffeomorph :
    letI := compactNeckLeftCutChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      (compactCutPushoutHomeomorph m ∘
        topologicalPushoutInlOffSeamMap'
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)) := by
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := compactNeckLeftCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckLeftCut m) :=
    isManifold_compactNeckLeftCut m
  have hreparam :=
    compactCutPushoutLeftOffSeamHomeomorphAmbient_isLocalDiffeomorph m
  have hambient := isLocalDiffeomorph_opensSubtypeVal
    coordinateUnlinkExteriorModel
    (collaredCutSideOffBoundaryOpens
      (coordinateUnlinkExteriorPlanarCompactNeckStarLeftCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
      (isOpen_compactNeckLeftCut_offBoundary m))
  intro x
  have hcomp := (hreparam x).comp coordinateUnlinkExteriorModel
    (CoordinateUnlinkExteriorEighthPowerPullback m)
    (hambient (compactCutPushoutLeftOffSeamHomeomorphAmbient m x))
  apply compactCut_isLocalDiffeomorphAt_congr_of_eqOn_open hcomp
    univ isOpen_univ (mem_univ x)
  intro y _
  exact compactCutPushoutHomeomorph_inl m y.1

private theorem compactCutPushoutHomeomorph_rightOffSeam_isLocalDiffeomorph :
    letI := compactNeckRightCutChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      (compactCutPushoutHomeomorph m ∘
        topologicalPushoutInrOffSeamMap'
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)) := by
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := compactNeckRightCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckRightCut m) :=
    isManifold_compactNeckRightCut m
  have hreparam :=
    compactCutPushoutRightOffSeamHomeomorphAmbient_isLocalDiffeomorph m
  have hambient := isLocalDiffeomorph_opensSubtypeVal
    coordinateUnlinkExteriorModel
    (collaredCutSideOffBoundaryOpens
      (coordinateUnlinkExteriorPlanarCompactNeckStarRightCutCarrier m)
      (coordinateUnlinkExteriorPlanarCompactNeckStarSeam m)
      (isOpen_compactNeckRightCut_offBoundary m))
  intro x
  have hcomp := (hreparam x).comp coordinateUnlinkExteriorModel
    (CoordinateUnlinkExteriorEighthPowerPullback m)
    (hambient (compactCutPushoutRightOffSeamHomeomorphAmbient m x))
  apply compactCut_isLocalDiffeomorphAt_congr_of_eqOn_open hcomp
    univ isOpen_univ (mem_univ x)
  intro y _
  exact compactCutPushoutHomeomorph_inr m y.1

private abbrev CompactCutNaturalSignedModel :=
  (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
    (modelWithCornersSelf ℝ ℝ)

@[instance_reducible]
private noncomputable def compactCutSignedNaturalChartedSpace :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 3)) ℝ)
      (Sphere 3 × EquatorCollarInterval) := inferInstance

private theorem compactCutSignedIdentity_naturalToCommon_contMDiff :
    letI := compactCutSignedNaturalChartedSpace
    letI := signedSeamCommonModelChartedSpace
    ContMDiff CompactCutNaturalSignedModel coordinateUnlinkExteriorModel ∞
      (id : Sphere 3 × EquatorCollarInterval →
        Sphere 3 × EquatorCollarInterval) := by
  let _ := compactCutSignedNaturalChartedSpace
  let _ := signedSeamIntervalChartedSpace
  let _ := signedSeamCollarBoundaryChartedSpace
  let _ := signedSeamCommonModelChartedSpace
  have hfst : ContMDiff CompactCutNaturalSignedModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ p.1) := contMDiff_fst
  have hsnd : ContMDiff CompactCutNaturalSignedModel
      (modelWithCornersEuclideanHalfSpace 1) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ p.2) := by
    apply contMDiff_to_signedSeamInterval_of_value
      CompactCutNaturalSignedModel _ continuous_snd
    exact contMDiff_subtype_val.comp contMDiff_snd
  have hboundary : ContMDiff CompactCutNaturalSignedModel
      coordinateUnlinkBoundaryCollarModel ∞
      (id : Sphere 3 × EquatorCollarInterval →
        Sphere 3 × EquatorCollarInterval) := by
    exact (ContMDiff.prodMk hfst hsnd).congr fun _ ↦ rfl
  exact (signedSeamCommonBoundaryIdentityDiffeomorph.symm.contMDiff.comp
    hboundary).congr fun _ ↦ rfl

private theorem compactCutSignedIdentity_commonToNatural_contMDiff :
    letI := signedSeamCommonModelChartedSpace
    letI := compactCutSignedNaturalChartedSpace
    ContMDiff coordinateUnlinkExteriorModel CompactCutNaturalSignedModel ∞
      (id : Sphere 3 × EquatorCollarInterval →
        Sphere 3 × EquatorCollarInterval) := by
  let _ := signedSeamCommonModelChartedSpace
  let _ := signedSeamIntervalChartedSpace
  let _ := signedSeamCollarBoundaryChartedSpace
  let _ := compactCutSignedNaturalChartedSpace
  have hcommonBoundary := signedSeamCommonBoundaryIdentityDiffeomorph.contMDiff
  have hfst : ContMDiff coordinateUnlinkExteriorModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ p.1) :=
    (contMDiff_fst.comp hcommonBoundary).congr fun _ ↦ rfl
  have hsnd : ContMDiff coordinateUnlinkExteriorModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ (p.2.1 : ℝ)) :=
    contMDiff_signedSeamTime
  have hsndSubtype : ContMDiff coordinateUnlinkExteriorModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : Sphere 3 × EquatorCollarInterval ↦ p.2) := by
    rw [← ContMDiff.subtypeVal_comp_iff equatorCollarIntervalOpens]
    exact hsnd
  exact (ContMDiff.prodMk hfst hsndSubtype).congr fun _ ↦ rfl

private noncomputable def compactCutSignedCommonNaturalIdentityDiffeomorph :
    letI := signedSeamCommonModelChartedSpace
    letI := compactCutSignedNaturalChartedSpace
    (Sphere 3 × EquatorCollarInterval) ≃ₘ^∞⟮
      coordinateUnlinkExteriorModel, CompactCutNaturalSignedModel⟯
      (Sphere 3 × EquatorCollarInterval) := by
  let _ := signedSeamCommonModelChartedSpace
  let _ := compactCutSignedNaturalChartedSpace
  exact
    { toEquiv := Equiv.refl _
      contMDiff_toFun := compactCutSignedIdentity_commonToNatural_contMDiff
      contMDiff_invFun := compactCutSignedIdentity_naturalToCommon_contMDiff }

private def compactCutAmbientSignedCollarMap
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :
    CoordinateUnlinkExteriorEighthPowerPullback m :=
  coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1 p.2

private theorem compactCutAmbientSignedCollarMap_isLocalDiffeomorph :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      (compactCutAmbientSignedCollarMap m) := by
  let _ := signedSeamCommonModelChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (Sphere 3 × EquatorCollarInterval) :=
    isManifold_signedSeamCommonModel
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ := compactCutSignedNaturalChartedSpace
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  have hsnd : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (Prod.snd :
        CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m →
          Sphere 3 × EquatorCollarInterval) :=
    IsLocalHomeomorph.isLocalDiffeomorph_pullbackChartedSpace
      coordinateUnlinkExteriorModel ∞
      (isLocalHomeomorph_discreteProdSnd
        (D := ZMod m) (P := Sphere 3 × EquatorCollarInterval))
  intro p
  have hcommon := hsnd p
  have hnatural :=
    compactCutSignedCommonNaturalIdentityDiffeomorph.isLocalDiffeomorph p.2
  have hcommonNatural := hcommon.comp CompactCutNaturalSignedModel
    (Sphere 3 × EquatorCollarInterval) hnatural
  have horiented := isLocalDiffeomorph_compactNeckOrientedCollarMap m p.1 p.2
  have hcomp := hcommonNatural.comp coordinateUnlinkExteriorModel
    (CoordinateUnlinkExteriorEighthPowerPullback m) horiented
  let W : Set (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    {q | q.1 = p.1}
  have hWopen : IsOpen W :=
    (isOpen_discrete ({p.1} : Set (ZMod m))).preimage continuous_fst
  have hpW : p ∈ W := by simp [W]
  apply compactCut_isLocalDiffeomorphAt_congr_of_eqOn_open hcomp W hWopen hpW
  intro q hq
  change coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m q.1 q.2 =
    coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1 q.2
  rw [hq]

private theorem compactCutPushoutHomeomorph_seam_apply
    (p : CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :
    compactCutPushoutHomeomorph m
        (coordinateUnlinkExteriorPlanarCompactCutPushoutSeamMap m p) =
      compactCutAmbientSignedCollarMap m p := by
  by_cases hp : signedSeamTime m p ≤ 0
  · rw [show coordinateUnlinkExteriorPlanarCompactCutPushoutSeamMap m p =
        topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckLeftCutSeamBranch m p) by
      simp [coordinateUnlinkExteriorPlanarCompactCutPushoutSeamMap,
        topologicalPushoutSeamMap, hp]]
    rw [compactCutPushoutHomeomorph_inl]
    change coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1
        (compactNeckLeftHalfParameter (signedSeamHalfReparam m p).2) =
      coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1 p.2
    rw [compactNeckLeftHalfParameter_signedSeamHalfReparam m p hp]
  · have hpPos : 0 < signedSeamTime m p := lt_of_not_ge hp
    rw [show coordinateUnlinkExteriorPlanarCompactCutPushoutSeamMap m p =
        topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckRightCutSeamBranch m p) by
      simp [coordinateUnlinkExteriorPlanarCompactCutPushoutSeamMap,
        topologicalPushoutSeamMap, hp]]
    rw [compactCutPushoutHomeomorph_inr]
    change coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1
        (compactNeckRightHalfParameter (signedSeamHalfReparam m p).2) =
      coordinateUnlinkExteriorPlanarOrientedCompactCollarMap m p.1 p.2
    rw [compactNeckRightHalfParameter_signedSeamHalfReparam m p hpPos.le]

private theorem compactCutPushoutHomeomorph_seam_isLocalDiffeomorph :
    letI := signedSeamFamilyCommonModelChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    IsLocalDiffeomorph coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
      (compactCutPushoutHomeomorph m ∘
        coordinateUnlinkExteriorPlanarCompactCutPushoutSeamMap m) := by
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  have hbase := compactCutAmbientSignedCollarMap_isLocalDiffeomorph m
  intro p
  apply compactCut_isLocalDiffeomorphAt_congr_of_eqOn_open (hbase p)
    univ isOpen_univ (mem_univ p)
  intro q _
  exact compactCutPushoutHomeomorph_seam_apply m q

private noncomputable def compactCutPushoutDiffeomorph :
    letI := compactCutPushoutChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    CoordinateUnlinkExteriorPlanarCompactCutPushout m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, coordinateUnlinkExteriorModel⟯
        CoordinateUnlinkExteriorEighthPowerPullback m := by
  let _ := signedSeamFamilyCommonModelChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarNeckSmoothCappingSignedCollar m) :=
    isManifold_signedSeamFamilyCommonModel m
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarFamilyChartedSpace m
  let _ := compactNeckLeftCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckLeftCut m) :=
    isManifold_compactNeckLeftCut m
  let _ := compactNeckRightCutChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (CompactNeckRightCut m) :=
    isManifold_compactNeckRightCut m
  let _ := coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    isManifold_coordinateUnlinkExteriorEighthPowerPullback m
  exact diffeomorphOfCollaredPushoutHomeomorph
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel ∞
    (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
    (isClosedEmbedding_coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m)
    (coordinateUnlinkExteriorPlanarCompactCutPushoutSeamMap m)
    (compactCutPushoutSeamMap_isOpenEmbedding m)
    (compactCutPushoutSeamMap_attaching_coverage m)
    (compactCutPushout_isManifold m)
    (compactCutPushoutHomeomorph m)
    (compactCutPushoutHomeomorph_seam_isLocalDiffeomorph m)
    (compactCutPushoutHomeomorph_leftOffSeam_isLocalDiffeomorph m)
    (compactCutPushoutHomeomorph_rightOffSeam_isLocalDiffeomorph m)

namespace CoordinateExteriorPlanarNeckCompactCutRegluingInternal

/-- The minimal construction spine for direct compact-cut regluing.

The point-set separation and local smooth recharting arguments remain private to this module;
these fields retain only the resulting atlas, comparison maps, and exact coprojection laws. -/
structure Construction (m : ℕ) [NeZero m] where
  /-- The direct generated common-model atlas on the pushout. -/
  chartedSpace : ChartedSpace CoordinateUnlinkExteriorModelSpace
    (CoordinateUnlinkExteriorPlanarCompactCutPushout m)
  /-- The generated pushout atlas is a smooth manifold atlas. -/
  isManifold :
    letI := chartedSpace
    IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarCompactCutPushout m)
  /-- The point-set regluing comparison with the original compact cover. -/
  homeomorph : CoordinateUnlinkExteriorPlanarCompactCutPushout m ≃ₜ
    CoordinateUnlinkExteriorEighthPowerPullback m
  /-- The point-set comparison is literal inclusion on the left cut side. -/
  homeomorph_inl (x : CompactNeckLeftCut m) :
    homeomorph
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m) x) = x.1
  /-- The point-set comparison is literal inclusion on the right cut side. -/
  homeomorph_inr (x : CompactNeckRightCut m) :
    homeomorph
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m) x) = x.1
  /-- The direct smooth regluing comparison. -/
  diffeomorph :
    letI := chartedSpace
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    CoordinateUnlinkExteriorPlanarCompactCutPushout m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, coordinateUnlinkExteriorModel⟯
        CoordinateUnlinkExteriorEighthPowerPullback m
  /-- The smooth comparison has the point-set regluing map as forward function. -/
  diffeomorph_apply (z : CoordinateUnlinkExteriorPlanarCompactCutPushout m) :
    letI := chartedSpace
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    diffeomorph z = homeomorph z
  /-- Forgetting smoothness recovers the point-set regluing comparison. -/
  diffeomorph_toHomeomorph :
    letI := chartedSpace
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    diffeomorph.toHomeomorph = homeomorph

/-- The direct point-set, atlas, and smooth construction underlying compact-cut regluing. -/
noncomputable def construction (m : ℕ) [NeZero m] : Construction m :=
  Classical.choice (by
    exact ⟨{
      chartedSpace := compactCutPushoutChartedSpace m
      isManifold := compactCutPushout_isManifold m
      homeomorph := compactCutPushoutHomeomorph m
      homeomorph_inl := compactCutPushoutHomeomorph_inl m
      homeomorph_inr := compactCutPushoutHomeomorph_inr m
      diffeomorph := compactCutPushoutDiffeomorph m
      diffeomorph_apply := fun _ ↦ rfl
      diffeomorph_toHomeomorph := rfl }⟩)

end CoordinateExteriorPlanarNeckCompactCutRegluingInternal

/-- The direct common-model atlas generated by the signed seam and the two cut interiors. -/
@[instance_reducible]
noncomputable def coordinateUnlinkExteriorPlanarCompactCutPushoutChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CoordinateUnlinkExteriorPlanarCompactCutPushout m) :=
  (CoordinateExteriorPlanarNeckCompactCutRegluingInternal.construction m).chartedSpace

/-- The compact cut pushout with its literal two-collar atlas is a smooth manifold. -/
theorem isManifold_coordinateUnlinkExteriorPlanarCompactCutPushout :
    letI := coordinateUnlinkExteriorPlanarCompactCutPushoutChartedSpace m
    IsManifold coordinateUnlinkExteriorModel ∞
      (CoordinateUnlinkExteriorPlanarCompactCutPushout m) :=
  (CoordinateExteriorPlanarNeckCompactCutRegluingInternal.construction m).isManifold

/-- Reglue the two compact cut sides to recover the original compact coordinate exterior. -/
noncomputable def coordinateUnlinkExteriorPlanarCompactCutPushoutHomeomorph :
    CoordinateUnlinkExteriorPlanarCompactCutPushout m ≃ₜ
      CoordinateUnlinkExteriorEighthPowerPullback m :=
  (CoordinateExteriorPlanarNeckCompactCutRegluingInternal.construction m).homeomorph

/-- The direct two-collar pushout is genuinely diffeomorphic to the original compact coordinate
exterior, without transporting either atlas. -/
noncomputable def coordinateUnlinkExteriorPlanarCompactCutPushoutDiffeomorph :
    letI := coordinateUnlinkExteriorPlanarCompactCutPushoutChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    CoordinateUnlinkExteriorPlanarCompactCutPushout m
      ≃ₘ^∞⟮coordinateUnlinkExteriorModel, coordinateUnlinkExteriorModel⟯
        CoordinateUnlinkExteriorEighthPowerPullback m :=
  (CoordinateExteriorPlanarNeckCompactCutRegluingInternal.construction m).diffeomorph

/-- The smooth comparison has the point-set regluing map as forward function. -/
@[simp] theorem coordinateUnlinkExteriorPlanarCompactCutPushoutDiffeomorph_apply
    (z : CoordinateUnlinkExteriorPlanarCompactCutPushout m) :
    letI := coordinateUnlinkExteriorPlanarCompactCutPushoutChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarCompactCutPushoutDiffeomorph m z =
      coordinateUnlinkExteriorPlanarCompactCutPushoutHomeomorph m z :=
  (CoordinateExteriorPlanarNeckCompactCutRegluingInternal.construction
    m).diffeomorph_apply z

/-- Forgetting smoothness recovers the point-set regluing comparison. -/
@[simp] theorem
    coordinateUnlinkExteriorPlanarCompactCutPushoutDiffeomorph_toHomeomorph :
    letI := coordinateUnlinkExteriorPlanarCompactCutPushoutChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    (coordinateUnlinkExteriorPlanarCompactCutPushoutDiffeomorph m).toHomeomorph =
      coordinateUnlinkExteriorPlanarCompactCutPushoutHomeomorph m :=
  (CoordinateExteriorPlanarNeckCompactCutRegluingInternal.construction
    m).diffeomorph_toHomeomorph

/-- On the left coprojection, smooth regluing is literal subtype inclusion. -/
theorem coordinateUnlinkExteriorPlanarCompactCutPushoutDiffeomorph_inl
    (x : CompactNeckLeftCut m) :
    letI := coordinateUnlinkExteriorPlanarCompactCutPushoutChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarCompactCutPushoutDiffeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m) x) = x.1 := by
  rw [coordinateUnlinkExteriorPlanarCompactCutPushoutDiffeomorph_apply]
  exact (CoordinateExteriorPlanarNeckCompactCutRegluingInternal.construction
    m).homeomorph_inl x

/-- On the right coprojection, smooth regluing is literal subtype inclusion. -/
theorem coordinateUnlinkExteriorPlanarCompactCutPushoutDiffeomorph_inr
    (x : CompactNeckRightCut m) :
    letI := coordinateUnlinkExteriorPlanarCompactCutPushoutChartedSpace m
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    coordinateUnlinkExteriorPlanarCompactCutPushoutDiffeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckLeftCutAttachingMap m)
          (coordinateUnlinkExteriorPlanarNeckRightCutAttachingMap m) x) = x.1 := by
  rw [coordinateUnlinkExteriorPlanarCompactCutPushoutDiffeomorph_apply]
  exact (CoordinateExteriorPlanarNeckCompactCutRegluingInternal.construction
    m).homeomorph_inr x

end SplittingSpheres
