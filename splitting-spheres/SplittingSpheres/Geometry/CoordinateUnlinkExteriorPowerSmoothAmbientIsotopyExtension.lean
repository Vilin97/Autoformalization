/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CompactDiffeomorphismFamilyAmbientIsotopy
public import SplittingSpheres.Foundations.OpenDiffeomorphFamilyExtension
public import SplittingSpheres.Foundations.TopologicalCoverPullbackCompact
public import SplittingSpheres.Geometry.UnlinkPowerProper
public import SplittingSpheres.Geometry.UnlinkPowerSmoothAmbientIsotopyExtension
public import SplittingSpheres.Geometry.UnlinkPowerSmoothCoordinateExteriorDiffeomorph

/-!
# Smooth ambient isotopies of compact coordinate-exterior power covers

The compactly supported smooth ambient isotopy of the standard unlink power cover transports to
the strict part of the coordinate-exterior power cover.  Its support stays in a fixed compact
subset of that strict open set, so every transported time-slice extends by the identity across the
radial boundary.  Joint smoothness of the extended forward evaluation then packages the family as
an ambient isotopy of the full compact coordinate power pullback.

Only forward joint smoothness is asserted; no joint regularity of the inverse evaluation is used.
-/

@[expose] public section

noncomputable section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold unitInterval

namespace SplittingSpheres

variable {S : SmoothSphereEmbedding 3 4}

private def standardUnlinkComplementCoordinateExteriorInteriorDiffeomorph :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    StandardUnlinkComplement
      ≃ₘ^∞⟮𝓡 4, coordinateUnlinkExteriorModel⟯
        CoordinateUnlinkExteriorEighthInterior := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  exact standardUnlinkComplementSmoothExteriorDiffeomorph.trans
    coordinateUnlinkExteriorEighthInteriorSphereDiffeomorph.symm

private def coordinateUnlinkExteriorCompactSupportBase
    (K : Set StandardUnlinkComplement) :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    Set CoordinateUnlinkExteriorEighth := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  exact (fun x : StandardUnlinkComplement ↦
    ((standardUnlinkComplementCoordinateExteriorInteriorDiffeomorph x :
      CoordinateUnlinkExteriorEighthInterior) : CoordinateUnlinkExteriorEighth)) '' K

private theorem isCompact_coordinateUnlinkExteriorCompactSupportBase
    (K : Set StandardUnlinkComplement) (hK : IsCompact K) :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    IsCompact (coordinateUnlinkExteriorCompactSupportBase K) := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  exact hK.image (continuous_subtype_val.comp
    standardUnlinkComplementCoordinateExteriorInteriorDiffeomorph.continuous)

private def coordinateUnlinkExteriorPowerCompactSupport
    (m : ℕ) (K : Set StandardUnlinkComplement) :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    Set (CoordinateUnlinkExteriorEighthPowerPullback m) := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  exact coordinateUnlinkExteriorEighthPowerPullbackProj m ⁻¹'
    coordinateUnlinkExteriorCompactSupportBase K

private theorem isClosed_coordinateUnlinkExteriorPowerCompactSupport
    (m : ℕ) (K : Set StandardUnlinkComplement) (hK : IsCompact K) :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    IsClosed (coordinateUnlinkExteriorPowerCompactSupport m K) := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  exact (isCompact_coordinateUnlinkExteriorCompactSupportBase K hK).isClosed.preimage
    (continuous_topologicalCoverPullbackProj (nonzeroComplexPow m)
      coordinateUnlinkExteriorEighthRightNormalMap)

private theorem coordinateUnlinkExteriorPowerCompactSupport_subset_strict
    (m : ℕ) (K : Set StandardUnlinkComplement) :
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    coordinateUnlinkExteriorPowerCompactSupport m K ⊆
      coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m := by
  let _ := coordinateUnlinkExteriorEighthChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      CoordinateUnlinkExteriorEighth :=
    coordinateUnlinkExteriorEighth_isManifold
  intro z hz
  change coordinateUnlinkExteriorEighthPowerPullbackProj m z ∈
    coordinateUnlinkExteriorCompactSupportBase K at hz
  rcases hz with ⟨x, hxK, hx⟩
  change z.1.1.1 ∈ standardUnlinkClosedTubeExteriorOpens
  rw [mem_standardUnlinkClosedTubeExteriorOpens,
    ← mem_coordinateUnlinkExteriorEighthInteriorOpens_iff]
  change z.1.1 ∈ coordinateUnlinkExteriorEighthInteriorOpens
  rw [← coordinateUnlinkExteriorEighthPowerPullbackProj_apply]
  rw [← hx]
  exact (standardUnlinkComplementCoordinateExteriorInteriorDiffeomorph x).property

private theorem compactSpace_coordinateUnlinkExteriorEighthPowerPullback
    (m : ℕ) [NeZero m] :
    CompactSpace (CoordinateUnlinkExteriorEighthPowerPullback m) := by
  let _ : CompactSpace ↑(coordinateUnlinkExterior (1 / 8 : ℝ)) :=
    isCompact_iff_compactSpace.mp
      (isOpen_standardUnlinkOpenTubes (1 / 8 : ℝ)).isClosed_compl.isCompact
  exact topologicalCoverPullbackCompactSpace (nonzeroComplexPow m)
    coordinateUnlinkExteriorEighthRightNormalMap
    (isProperMap_nonzeroComplexPow m)
    continuous_coordinateUnlinkExteriorEighthRightNormalMap

private theorem standardUnlinkPowerPullbackProj_not_mem_of_coordinateSupport_not_mem
    (m : ℕ) [NeZero m] (K : Set StandardUnlinkComplement)
    (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m z).1 ∉
        coordinateUnlinkExteriorPowerCompactSupport m K →
      standardUnlinkPowerPullbackProj m z ∉ K := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
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
  intro hz hk
  apply hz
  change coordinateUnlinkExteriorEighthPowerPullbackProj m
      (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m z).1 ∈
    coordinateUnlinkExteriorCompactSupportBase K
  exact ⟨standardUnlinkPowerPullbackProj m z, hk,
    (coordinateUnlinkExteriorEighthPowerPullbackProj_coordinateExteriorStrictDiffeomorph
      m z).symm⟩

private theorem contMDiff_coordinateUnlinkExteriorConjugatedPowerFamily
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    ∀ (PsiLift : I →
        StandardUnlinkPowerPullback m ≃ₘ^∞⟮(𝓡 4), (𝓡 4)⟯
          StandardUnlinkPowerPullback m),
      ContMDiff ((𝓡∂ 1).prod (𝓡 4)) (𝓡 4) ∞
          (fun p : I × StandardUnlinkPowerPullback m ↦ PsiLift p.1 p.2) →
        ContMDiff ((𝓡∂ 1).prod coordinateUnlinkExteriorModel)
          coordinateUnlinkExteriorModel ∞
          (fun p : I × CoordinateUnlinkExteriorEighthPowerPullbackStrict m ↦
            standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m
              (PsiLift p.1
                ((standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m).symm
                  p.2))) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
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
  intro PsiLift hPsiLift
  let e := standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m
  have hin : ContMDiff ((𝓡∂ 1).prod coordinateUnlinkExteriorModel)
      ((𝓡∂ 1).prod (𝓡 4)) ∞
      (fun p : I × CoordinateUnlinkExteriorEighthPowerPullbackStrict m ↦
        (p.1, e.symm p.2)) :=
    contMDiff_fst.prodMk (e.symm.contMDiff.comp contMDiff_snd)
  exact e.contMDiff.comp (hPsiLift.comp hin)

/-- The endpoint-flattened normalized power-cover isotopy extends smoothly across the two radial
faces of the compact coordinate exterior.  Its full time-slices are identity extensions of the
strict conjugated time-slices, and the displayed `ContMDiff` assertion concerns only their forward
joint evaluation. -/
theorem exists_coordinateUnlinkExteriorNormalizedFlattenedPowerSmoothAmbientIsotopy_supported
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI := coordinateUnlinkExteriorEighthChartedSpace
    letI : IsManifold coordinateUnlinkExteriorModel ∞
        CoordinateUnlinkExteriorEighth :=
      coordinateUnlinkExteriorEighth_isManifold
    letI : ChartedSpace CoordinateUnlinkExteriorModelSpace
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
      coordinateUnlinkExteriorEighthPowerPullbackChartedSpace m
    let e := standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m
    ∃ (Kfull : Set (CoordinateUnlinkExteriorEighthPowerPullback m))
        (PsiLift : I →
          StandardUnlinkPowerPullback m ≃ₘ^∞⟮(𝓡 4), (𝓡 4)⟯
            StandardUnlinkPowerPullback m)
        (Psi : I →
          CoordinateUnlinkExteriorEighthPowerPullback m
            ≃ₘ^∞⟮coordinateUnlinkExteriorModel, coordinateUnlinkExteriorModel⟯
            CoordinateUnlinkExteriorEighthPowerPullback m)
        (Phi : TauCeti.AmbientIsotopy
          (CoordinateUnlinkExteriorEighthPowerPullback m)),
      IsCompact Kfull ∧
      Kfull ⊆ coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m ∧
      (∀ (t : I) (z : CoordinateUnlinkExteriorEighthPowerPullback m), z ∉ Kfull →
        Phi.toContinuousMap (t, z) = z) ∧
      (∀ (t : I) (z : CoordinateUnlinkExteriorEighthPowerPullback m),
        Phi.toContinuousMap (t, z) = Psi t z) ∧
      (∀ (t : I) (z : CoordinateUnlinkExteriorEighthPowerPullbackStrict m),
        Psi t z.1 = (e (PsiLift t (e.symm z))).1) ∧
      (∀ (t : I) (x : Sphere 3),
        Phi.toContinuousMap (t, (e (equatorUnlinkPowerLift m a x)).1) =
          (e (standardUnlinkPowerIsotopyLift m a H havoid
            (unitInterval.endpointFlatTime t, x))).1) ∧
      ContMDiff ((𝓡∂ 1).prod coordinateUnlinkExteriorModel)
        coordinateUnlinkExteriorModel ∞
        (fun p : I × CoordinateUnlinkExteriorEighthPowerPullback m ↦ Psi p.1 p.2) ∧
      (∀ (t : I) (z : CoordinateUnlinkExteriorEighthPowerPullback m),
        coordinateUnlinkExteriorEighthPowerPullbackProj m z ∈
            coordinateUnlinkExteriorEighthRadialBoundary →
          Phi.toContinuousMap (t, z) = z) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
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
  let _ : CompactSpace (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    compactSpace_coordinateUnlinkExteriorEighthPowerPullback m
  obtain ⟨K, PhiBase, PsiBase, PhiLift, PsiLift, hKcompact, _hPhiBaseFixed,
      hPhiLiftFixed, _hPhiLift, _hPhiBase, _hBaseTrace, hPhiLiftPsiLift, _hproj,
      hPsiLiftTrace, hPsiLiftJoint⟩ :=
    exists_standardUnlinkNormalizedFlattenedPowerSmoothAmbientIsotopy_supported
      m a H havoid
  let Kfull := coordinateUnlinkExteriorPowerCompactSupport m K
  have hKfullClosed : IsClosed Kfull :=
    isClosed_coordinateUnlinkExteriorPowerCompactSupport m K hKcompact
  have hKfullCompact : IsCompact Kfull := hKfullClosed.isCompact
  have hKfullStrict : Kfull ⊆
      coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m :=
    coordinateUnlinkExteriorPowerCompactSupport_subset_strict m K
  let e := standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m
  let PsiStrict : I →
      CoordinateUnlinkExteriorEighthPowerPullbackStrict m
        ≃ₘ^∞⟮coordinateUnlinkExteriorModel, coordinateUnlinkExteriorModel⟯
        CoordinateUnlinkExteriorEighthPowerPullbackStrict m := fun t ↦
    e.symm.trans ((PsiLift t).trans e)
  have hPsiStrictFixed : ∀ (t : I)
      (z : CoordinateUnlinkExteriorEighthPowerPullbackStrict m),
      z.1 ∉ Kfull → PsiStrict t z = z := by
    intro t z hz
    let w := e.symm z
    have hwCoordinate :
        (standardUnlinkPowerPullbackCoordinateExteriorStrictDiffeomorph m w).1 ∉
          coordinateUnlinkExteriorPowerCompactSupport m K := by
      change (e w).1 ∉ Kfull
      dsimp only [w]
      rw [e.apply_symm_apply]
      exact hz
    have hwK : standardUnlinkPowerPullbackProj m w ∉ K :=
      standardUnlinkPowerPullbackProj_not_mem_of_coordinateSupport_not_mem
        m K w hwCoordinate
    have hwFixed : PsiLift t w = w :=
      (hPhiLiftPsiLift t w).symm.trans (hPhiLiftFixed t w hwK)
    change e (PsiLift t (e.symm z)) = z
    rw [hwFixed]
    exact e.apply_symm_apply z
  have hPsiStrictJoint : ContMDiff
      ((𝓡∂ 1).prod coordinateUnlinkExteriorModel)
      coordinateUnlinkExteriorModel ∞
      (fun p : I × CoordinateUnlinkExteriorEighthPowerPullbackStrict m ↦
        PsiStrict p.1 p.2) := by
    exact contMDiff_coordinateUnlinkExteriorConjugatedPowerFamily m PsiLift hPsiLiftJoint
  let Psi : I →
      CoordinateUnlinkExteriorEighthPowerPullback m
        ≃ₘ^∞⟮coordinateUnlinkExteriorModel, coordinateUnlinkExteriorModel⟯
        CoordinateUnlinkExteriorEighthPowerPullback m := fun t ↦
    extendOpenDiffeomorphByIdentity
      (coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m) Kfull
      (PsiStrict t) hKfullClosed hKfullStrict (hPsiStrictFixed t)
  have hPsiJoint : ContMDiff
      ((𝓡∂ 1).prod coordinateUnlinkExteriorModel)
      coordinateUnlinkExteriorModel ∞
      (fun p : I × CoordinateUnlinkExteriorEighthPowerPullback m ↦
        Psi p.1 p.2) := by
    have hExt := contMDiff_extendOpenMapFamilyByIdentity
      (coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m) Kfull
      (fun p : I × CoordinateUnlinkExteriorEighthPowerPullbackStrict m ↦
        PsiStrict p.1 p.2)
      hPsiStrictJoint hKfullClosed hKfullStrict
      (fun p hp ↦ hPsiStrictFixed p.1 p.2 hp)
    apply hExt.congr
    intro p
    rfl
  have hPsiLiftZero : ∀ z : StandardUnlinkPowerPullback m, PsiLift 0 z = z := by
    intro z
    exact (hPhiLiftPsiLift 0 z).symm.trans (PhiLift.map_zero_left z)
  have hPsiStrictZero : ∀ z : CoordinateUnlinkExteriorEighthPowerPullbackStrict m,
      PsiStrict 0 z = z := by
    intro z
    change e (PsiLift 0 (e.symm z)) = z
    rw [hPsiLiftZero]
    exact e.apply_symm_apply z
  have hPsiZero : ∀ z : CoordinateUnlinkExteriorEighthPowerPullback m,
      Psi 0 z = z := by
    intro z
    by_cases hz : z ∈ coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m
    · rw [show Psi 0 z =
          (PsiStrict 0 ⟨z, hz⟩ : CoordinateUnlinkExteriorEighthPowerPullback m) by
        exact extendOpenDiffeomorphByIdentity_apply_of_mem
          (coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m) Kfull
          (PsiStrict 0) hKfullClosed hKfullStrict (hPsiStrictFixed 0) hz]
      exact congrArg Subtype.val (hPsiStrictZero ⟨z, hz⟩)
    · exact extendOpenMapByIdentity_of_not_mem
        (coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m)
        (PsiStrict 0) hz
  let Phi : TauCeti.AmbientIsotopy
      (CoordinateUnlinkExteriorEighthPowerPullback m) :=
    ambientIsotopyOfDiffeomorphismFamily
      coordinateUnlinkExteriorModel
      (CoordinateUnlinkExteriorEighthPowerPullback m) Psi hPsiJoint hPsiZero
  refine ⟨Kfull, PsiLift, Psi, Phi, hKfullCompact, hKfullStrict, ?_, ?_, ?_, ?_,
    hPsiJoint, ?_⟩
  · intro t z hz
    change Psi t z = z
    exact extendOpenDiffeomorphByIdentity_apply_of_not_mem
      (coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m) Kfull
      (PsiStrict t) hKfullClosed hKfullStrict (hPsiStrictFixed t) hz
  · intro t z
    rfl
  · intro t z
    rw [show Psi t z.1 =
          (PsiStrict t z : CoordinateUnlinkExteriorEighthPowerPullback m) by
      exact extendOpenDiffeomorphByIdentity_apply_of_mem
        (coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m) Kfull
        (PsiStrict t) hKfullClosed hKfullStrict (hPsiStrictFixed t) z.2]
    rfl
  · intro t x
    change Psi t (e (equatorUnlinkPowerLift m a x)).1 = _
    rw [show Psi t (e (equatorUnlinkPowerLift m a x)).1 =
          (PsiStrict t (e (equatorUnlinkPowerLift m a x)) :
            CoordinateUnlinkExteriorEighthPowerPullback m) by
      exact extendOpenDiffeomorphByIdentity_apply_of_mem
        (coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m) Kfull
        (PsiStrict t) hKfullClosed hKfullStrict (hPsiStrictFixed t)
        (e (equatorUnlinkPowerLift m a x)).2]
    rw [show PsiStrict t (e (equatorUnlinkPowerLift m a x)) =
          e (PsiLift t (equatorUnlinkPowerLift m a x)) by
      change e (PsiLift t (e.symm (e (equatorUnlinkPowerLift m a x)))) = _
      rw [e.symm_apply_apply]]
    exact congrArg (fun z : CoordinateUnlinkExteriorEighthPowerPullbackStrict m ↦ z.1)
      (congrArg e
        ((hPhiLiftPsiLift t (equatorUnlinkPowerLift m a x)).symm.trans
          (hPsiLiftTrace t x)))
  · intro t z hzBoundary
    apply extendOpenDiffeomorphByIdentity_apply_of_not_mem
      (coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m) Kfull
      (PsiStrict t) hKfullClosed hKfullStrict (hPsiStrictFixed t)
    intro hzK
    have hzStrict := hKfullStrict hzK
    have hzInterior : coordinateUnlinkExteriorEighthPowerPullbackProj m z ∈
        coordinateUnlinkExteriorEighthInteriorOpens := by
      change z.1.1.1 ∈ standardUnlinkClosedTubeExteriorOpens at hzStrict
      rw [mem_standardUnlinkClosedTubeExteriorOpens,
        ← mem_coordinateUnlinkExteriorEighthInteriorOpens_iff] at hzStrict
      exact hzStrict
    rw [coordinateUnlinkExteriorEighthRadialBoundary_eq_compl_interior] at hzBoundary
    exact hzBoundary hzInterior

end SplittingSpheres

end
