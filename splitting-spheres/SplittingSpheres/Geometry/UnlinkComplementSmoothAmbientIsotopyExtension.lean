/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.RadialDiffeomorph
public import SplittingSpheres.Foundations.SmoothCompactlySupportedTimeDependentFlow
public import SplittingSpheres.Geometry.UnlinkComplementAmbientIsotopyExtension
public import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Smooth ambient-isotopy slices on the standard-unlink complement

The compactly supported smooth spacetime field extending the endpoint-flattened normalized trace
has smooth full-space flow slices.  Because the field is supported over the stereographic image,
the ambient flow fixes its complement.  Each full-space diffeomorphism and its inverse therefore
preserve the image and restrict to a diffeomorphism of the open submanifold.  Conjugating these
restricted slices through the smooth stereographic coordinates gives genuine `C∞`
diffeomorphisms of `StandardUnlinkComplement`.

The returned diffeomorphism slices agree pointwise with the simultaneously constructed continuous
ambient isotopy, whose action on the equatorial unlink-complement sphere is the exact
endpoint-flattened normalized homotopy.  Their forward evaluation is jointly smooth in time and
space; no joint smoothness of the inverse evaluation is asserted.
-/

@[expose] public section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold Topology unitInterval

noncomputable section

namespace SplittingSpheres

variable {S : SmoothSphereEmbedding 3 4}

private theorem contMDiff_unitInterval_prod_of_contDiffOn
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (Set.univ ×ˢ Set.Icc (-(1 : ℝ)) 1)) :
    ContMDiff ((𝓡∂ 1).prod (modelWithCornersSelf ℝ E))
      (modelWithCornersSelf ℝ F) ∞
      (fun p : I × E ↦ f (p.2, (p.1 : ℝ))) := by
  have hfM : ContMDiffOn (modelWithCornersSelf ℝ (E × ℝ))
      (modelWithCornersSelf ℝ F) ∞ f
      (Set.univ ×ˢ Set.Icc (-(1 : ℝ)) 1) := hf.contMDiffOn
  have hg : ContMDiff ((𝓡∂ 1).prod (modelWithCornersSelf ℝ E))
      (modelWithCornersSelf ℝ (E × ℝ)) ∞
      (fun p : I × E ↦ (p.2, (p.1 : ℝ))) := by
    have ht : ContMDiff ((𝓡∂ 1).prod (modelWithCornersSelf ℝ E))
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : I × E ↦ (p.1 : ℝ)) := by
      have hp : ContMDiff ((𝓡∂ 1).prod (modelWithCornersSelf ℝ E))
          (𝓡∂ 1) ∞ (Prod.fst : I × E → I) := contMDiff_fst
      exact (contMDiff_subtypeVal_Icc (x := 0) (y := 1)).comp hp
    have he : ContMDiff ((𝓡∂ 1).prod (modelWithCornersSelf ℝ E))
        (modelWithCornersSelf ℝ E) ∞ (Prod.snd : I × E → E) :=
      contMDiff_snd
    rw [contMDiff_prod_module_iff]
    exact ⟨he, ht⟩
  apply hfM.comp_contMDiff hg
  intro p
  exact ⟨Set.mem_univ _, ⟨by linarith [p.1.2.1], by linarith [p.1.2.2]⟩⟩

private theorem contMDiff_restrict_open_unitInterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Opens E)
    (f : I × E → E)
    (hf : ContMDiff ((𝓡∂ 1).prod (modelWithCornersSelf ℝ E))
      (modelWithCornersSelf ℝ E) ∞ f)
    (hmem : ∀ p : I × U, f (p.1, (p.2 : E)) ∈ U) :
    ContMDiff ((𝓡∂ 1).prod (modelWithCornersSelf ℝ E))
      (modelWithCornersSelf ℝ E) ∞
      (fun p : I × U ↦ (⟨f (p.1, (p.2 : E)), hmem p⟩ : U)) := by
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  have hincl : ContMDiff ((𝓡∂ 1).prod (modelWithCornersSelf ℝ E))
      ((𝓡∂ 1).prod (modelWithCornersSelf ℝ E)) ∞
      (fun p : I × U ↦ (p.1, (p.2 : E))) := by
    exact contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
  exact hf.comp hincl

private theorem contMDiff_stereographic_conjugate
    (f : I × standardUnlinkComplementStereographicImage →
      standardUnlinkComplementStereographicImage)
    (hf : ContMDiff ((𝓡∂ 1).prod (𝓡 4)) (𝓡 4) ∞ f) :
    ContMDiff ((𝓡∂ 1).prod (𝓡 4)) (𝓡 4) ∞
      (fun p : I × StandardUnlinkComplement ↦
        standardUnlinkComplementStereographicDiffeomorph.symm
          (f (p.1, standardUnlinkComplementStereographicDiffeomorph p.2))) := by
  have hin : ContMDiff ((𝓡∂ 1).prod (𝓡 4))
      ((𝓡∂ 1).prod (𝓡 4)) ∞
      (fun p : I × StandardUnlinkComplement ↦
        (p.1, standardUnlinkComplementStereographicDiffeomorph p.2)) := by
    exact contMDiff_fst.prodMk
      (standardUnlinkComplementStereographicDiffeomorph.contMDiff.comp contMDiff_snd)
  exact standardUnlinkComplementStereographicDiffeomorph.symm.contMDiff.comp
    (hf.comp hin)

private theorem hasDerivAt_standardUnlinkNormalizedFlattenedStereographic_smoothSlices
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier)
    (x : Sphere 3) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦ standardUnlinkNormalizedFlattenedStereographic H havoid (u, x))
      (standardUnlinkNormalizedFlattenedStereographicVelocity H havoid (t, x)) t := by
  have hsmooth : ContDiff ℝ ∞
      (fun u : ℝ ↦ standardUnlinkNormalizedFlattenedStereographic H havoid (u, x)) := by
    exact ((contMDiff_standardUnlinkNormalizedFlattenedStereographic H havoid).comp
      (contMDiff_id.prodMk contMDiff_const)).contDiff
  have hd := (hsmooth.differentiable (by simp) t).hasFDerivAt.hasDerivAt
  simpa only [standardUnlinkNormalizedFlattenedStereographicVelocity,
    realTimeVelocity] using hd

/-- The normalized unlink-avoiding sphere isotopy extends to a compactly supported continuous
ambient isotopy of the strict unlink complement whose every time slice is exactly a smooth
diffeomorphism. -/
theorem exists_standardUnlinkNormalizedFlattenedComplementSmoothAmbientIsotopy_supported
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier) :
    ∃ (K : Set StandardUnlinkComplement)
        (Phi : TauCeti.AmbientIsotopy StandardUnlinkComplement)
        (Psi : I →
          StandardUnlinkComplement
            ≃ₘ^∞⟮(modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))),
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))⟯
            StandardUnlinkComplement),
      IsCompact K ∧
      (∀ (t : I) (y : StandardUnlinkComplement), y ∉ K →
        Phi.toContinuousMap (t, y) = y) ∧
      (∀ (t : I) (y : StandardUnlinkComplement),
        Phi.toContinuousMap (t, y) = Psi t y) ∧
      (∀ (t : I) (x : Sphere 3),
        Phi.toContinuousMap (t, equatorUnlinkComplementMap x) =
          standardUnlinkNormalizedComplementHomotopy H havoid
            (unitInterval.endpointFlatTime t, x)) ∧
      ContMDiff ((𝓡∂ 1).prod (𝓡 4)) (𝓡 4) ∞
        (fun p : I × StandardUnlinkComplement ↦ Psi p.1 p.2) := by
  obtain ⟨V, hVsmooth, hVcompact, hVsupport, hVtrace⟩ :=
    exists_standardUnlinkNormalizedFlattenedStereographicSpacetimeField H havoid
  let C : Set (EuclideanSpace ℝ (Fin 4)) := Prod.snd '' tsupport V
  have hCcompact : IsCompact C := hVcompact.image continuous_snd
  have hCsubset : C ⊆ standardUnlinkComplementStereographicImage := by
    rintro y ⟨p, hp, rfl⟩
    exact (hVsupport hp).2
  have hVzeroOutsideC : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 4)),
      y ∉ C → V (t, y) = 0 := by
    intro t y hy
    by_contra hne
    exact hy ⟨(t, y), subset_tsupport V hne, rfl⟩
  obtain ⟨PhiFull, eFlow, PsiFull, hPhiFull, hPsiFull, heFlowSmooth, hflow⟩ :=
    TimeDependentFlow.exists_ambientIsotopy_diffeomorph_of_contDiff_hasCompactSupport
      V hVsmooth hVcompact
  have hJointFull : ContMDiff ((𝓡∂ 1).prod (𝓡 4)) (𝓡 4) ∞
      (fun p : I × EuclideanSpace ℝ (Fin 4) ↦ eFlow (p.2, (p.1 : ℝ))) :=
    contMDiff_unitInterval_prod_of_contDiffOn heFlowSmooth
  obtain ⟨L, hVlip⟩ :=
    hVsmooth.lipschitzWith_of_hasCompactSupport hVcompact (by norm_num)
  have hflowZero (y : EuclideanSpace ℝ (Fin 4)) : eFlow (y, 0) = y := by
    calc
      eFlow (y, 0) = PhiFull.toContinuousMap (0, y) := (hPhiFull 0 y).symm
      _ = y := PhiFull.map_zero_left y
  have heFlowFixedC : ∀ (t : I) (y : EuclideanSpace ℝ (Fin 4)),
      y ∉ C → eFlow (y, (t : ℝ)) = y := by
    intro t y hy
    apply TimeDependentFlow.trajectory_eq_const_of_field_eq_zero
      V L hVlip eFlow y (hflowZero y) (hflow y)
    · intro s _
      exact hVzeroOutsideC s y hy
    · exact ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
  have heFlowFixed : ∀ (t : I) (y : EuclideanSpace ℝ (Fin 4)),
      y ∉ standardUnlinkComplementStereographicImage →
        eFlow (y, (t : ℝ)) = y := by
    intro t y hy
    exact heFlowFixedC t y (fun hC ↦ hy (hCsubset hC))
  have hPhiFixed : ∀ (t : I) (y : EuclideanSpace ℝ (Fin 4)),
      y ∉ standardUnlinkComplementStereographicImage →
        PhiFull.toContinuousMap (t, y) = y := by
    intro t y hy
    rw [hPhiFull]
    exact heFlowFixed t y hy
  have hPsiPhi : ∀ (t : I) (y : EuclideanSpace ℝ (Fin 4)),
      PsiFull t y = PhiFull.toContinuousMap (t, y) := by
    intro t y
    rw [hPsiFull, hPhiFull]
  have hPsiMem : ∀ (t : I) (y : EuclideanSpace ℝ (Fin 4)),
      PsiFull t y ∈ standardUnlinkComplementStereographicImage ↔
        y ∈ standardUnlinkComplementStereographicImage := by
    intro t y
    rw [hPsiPhi]
    exact PhiFull.mem_iff_of_fixed_complement
      standardUnlinkComplementStereographicImage hPhiFixed t y
  have hPsiSymmMem : ∀ (t : I) (y : EuclideanSpace ℝ (Fin 4)),
      y ∈ standardUnlinkComplementStereographicImage →
        (PsiFull t).symm y ∈ standardUnlinkComplementStereographicImage := by
    intro t y hy
    apply (hPsiMem t ((PsiFull t).symm y)).mp
    simpa using hy
  let PhiChart : TauCeti.AmbientIsotopy
      standardUnlinkComplementStereographicImage :=
    PhiFull.restrictOpensOfFixedComplement
      standardUnlinkComplementStereographicImage hPhiFixed
  let PsiChart : I →
      standardUnlinkComplementStereographicImage
        ≃ₘ^∞⟮(modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))),
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))⟯
        standardUnlinkComplementStereographicImage := fun t ↦
    restrictOpenDiffeomorph standardUnlinkComplementStereographicImage (PsiFull t)
      (fun y hy ↦ (hPsiMem t y).mpr hy) (hPsiSymmMem t)
  have hChartSlices : ∀ (t : I)
      (y : standardUnlinkComplementStereographicImage),
      PhiChart.toContinuousMap (t, y) = PsiChart t y := by
    intro t y
    apply Subtype.ext
    change PhiFull.toContinuousMap (t, (y : EuclideanSpace ℝ (Fin 4))) =
      PsiFull t (y : EuclideanSpace ℝ (Fin 4))
    exact (hPsiPhi t y).symm
  have hJointChart : ContMDiff ((𝓡∂ 1).prod (𝓡 4)) (𝓡 4) ∞
      (fun p : I × standardUnlinkComplementStereographicImage ↦
        PsiChart p.1 p.2) := by
    have hmem : ∀ p : I × standardUnlinkComplementStereographicImage,
        eFlow ((p.2 : EuclideanSpace ℝ (Fin 4)), (p.1 : ℝ)) ∈
          standardUnlinkComplementStereographicImage := by
      intro p
      rw [← hPhiFull]
      exact (PhiFull.mem_iff_of_fixed_complement
        standardUnlinkComplementStereographicImage hPhiFixed
          p.1 (p.2 : EuclideanSpace ℝ (Fin 4))).mpr p.2.property
    have hrestrict := contMDiff_restrict_open_unitInterval
      standardUnlinkComplementStereographicImage
      (fun p : I × EuclideanSpace ℝ (Fin 4) ↦ eFlow (p.2, (p.1 : ℝ)))
      hJointFull hmem
    apply hrestrict.congr
    intro p
    apply Subtype.ext
    change PsiFull p.1 (p.2 : EuclideanSpace ℝ (Fin 4)) =
      eFlow ((p.2 : EuclideanSpace ℝ (Fin 4)), (p.1 : ℝ))
    exact hPsiFull p.1 p.2
  have hTrace : ∀ (t : I) (x : Sphere 3),
      (((PhiChart.toContinuousMap
        (t, standardUnlinkNormalizedFlattenedStereographicPoint H havoid (0, x))) :
          standardUnlinkComplementStereographicImage) :
            EuclideanSpace ℝ (Fin 4)) =
        standardUnlinkNormalizedFlattenedStereographic H havoid ((t : ℝ), x) := by
    intro t x
    let x₀ : EuclideanSpace ℝ (Fin 4) :=
      standardUnlinkNormalizedFlattenedStereographic H havoid (0, x)
    let g : ℝ → EuclideanSpace ℝ (Fin 4) := fun s ↦
      standardUnlinkNormalizedFlattenedStereographic H havoid (s, x)
    have hspaceLip : ∀ s : ℝ,
        LipschitzWith L (fun y : EuclideanSpace ℝ (Fin 4) ↦ V (s, y)) := by
      intro s
      refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
      simpa [Prod.dist_eq] using hVlip.dist_le_mul (s, y) (s, z)
    have hg : ContDiff ℝ ∞ g := by
      exact ((contMDiff_standardUnlinkNormalizedFlattenedStereographic H havoid).comp
        (contMDiff_id.prodMk contMDiff_const)).contDiff
    have hinterval : Icc (-(1 : ℝ)) 2 ⊆ Icc (-(3 : ℝ)) 3 := by
      intro s hs
      constructor <;> linarith [hs.1, hs.2]
    have hEq : EqOn
        (fun s : ℝ ↦ eFlow (x₀, s)) g (Icc (-(1 : ℝ)) 2) := by
      apply ODE_solution_unique_of_mem_Icc
        (v := fun s y ↦ V (s, y)) (s := fun _ ↦ Set.univ) (K := L) (t₀ := 0)
        (fun s _ ↦ (hspaceLip s).lipschitzOnWith)
        (by norm_num)
      · exact HasDerivWithinAt.continuousOn fun s hs ↦
          (hflow x₀ s (hinterval hs)).mono hinterval
      · intro s hs
        exact (hflow x₀ s (hinterval (Ioo_subset_Icc_self hs))).hasDerivAt
          (Icc_mem_nhds (by linarith [hs.1]) (by linarith [hs.2]))
      · simp
      · exact hg.continuous.continuousOn
      · intro s _
        have hvg : V (s, g s) =
            standardUnlinkNormalizedFlattenedStereographicVelocity H havoid (s, x) := by
          exact hVtrace (s, x)
        rw [hvg]
        exact hasDerivAt_standardUnlinkNormalizedFlattenedStereographic_smoothSlices
          H havoid x s
      · simp
      · exact hflowZero x₀
    calc
      (((PhiChart.toContinuousMap
          (t, standardUnlinkNormalizedFlattenedStereographicPoint H havoid (0, x)) :
            standardUnlinkComplementStereographicImage) :
              EuclideanSpace ℝ (Fin 4))) = eFlow (x₀, (t : ℝ)) := by
                rw [TauCeti.AmbientIsotopy.coe_restrictOpensOfFixedComplement_apply,
                  hPhiFull]
                rfl
      _ = g (t : ℝ) := hEq ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
      _ = standardUnlinkNormalizedFlattenedStereographic H havoid ((t : ℝ), x) := rfl
  let e := standardUnlinkComplementStereographicDiffeomorph
  let CChart : Set standardUnlinkComplementStereographicImage :=
    (Subtype.val : standardUnlinkComplementStereographicImage →
      EuclideanSpace ℝ (Fin 4)) ⁻¹' C
  have hCChartCompact : IsCompact CChart := by
    apply IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hCcompact
    intro y hy
    exact ⟨⟨y, hCsubset hy⟩, rfl⟩
  let K : Set StandardUnlinkComplement := e ⁻¹' CChart
  have hKcompact : IsCompact K :=
    e.toHomeomorph.isProperMap.isCompact_preimage hCChartCompact
  let Phi : TauCeti.AmbientIsotopy StandardUnlinkComplement :=
    PhiChart.pullbackHomeomorph e.toHomeomorph
  let Psi : I →
      StandardUnlinkComplement
        ≃ₘ^∞⟮(modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))),
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))⟯
        StandardUnlinkComplement := fun t ↦
    e.trans ((PsiChart t).trans e.symm)
  have hJoint : ContMDiff ((𝓡∂ 1).prod (𝓡 4)) (𝓡 4) ∞
      (fun p : I × StandardUnlinkComplement ↦ Psi p.1 p.2) := by
    change ContMDiff ((𝓡∂ 1).prod (𝓡 4)) (𝓡 4) ∞
      (fun p : I × StandardUnlinkComplement ↦
        e.symm (PsiChart p.1 (e p.2)))
    exact contMDiff_stereographic_conjugate
      (fun p ↦ PsiChart p.1 p.2) hJointChart
  have hPhiSupport : ∀ (t : I) (y : StandardUnlinkComplement), y ∉ K →
      Phi.toContinuousMap (t, y) = y := by
    intro t y hy
    have hyC : (e y : EuclideanSpace ℝ (Fin 4)) ∉ C := by
      intro heyC
      apply hy
      change e y ∈ CChart
      exact heyC
    have hchart : PhiChart.toContinuousMap (t, e y) = e y := by
      apply Subtype.ext
      change PhiFull.toContinuousMap
          (t, (e y : EuclideanSpace ℝ (Fin 4))) =
        (e y : EuclideanSpace ℝ (Fin 4))
      rw [hPhiFull]
      exact heFlowFixedC t (e y) hyC
    change e.symm (PhiChart.toContinuousMap (t, e y)) = y
    rw [hchart, e.symm_apply_apply]
  refine ⟨K, Phi, Psi, hKcompact, hPhiSupport, ?_, ?_, hJoint⟩
  · intro t y
    change e.symm (PhiChart.toContinuousMap (t, e y)) =
      e.symm (PsiChart t (e y))
    rw [hChartSlices]
  · intro t x
    have hpoint : PhiChart.toContinuousMap
          (t, standardUnlinkComplementStereographicDiffeomorph
            (equatorUnlinkComplementMap x)) =
        standardUnlinkNormalizedFlattenedStereographicPoint H havoid ((t : ℝ), x) := by
      apply Subtype.ext
      rw [← standardUnlinkNormalizedFlattenedStereographicPoint_zero H havoid x]
      exact hTrace t x
    change standardUnlinkComplementStereographicDiffeomorph.symm
        (PhiChart.toContinuousMap
          (t, standardUnlinkComplementStereographicDiffeomorph
            (equatorUnlinkComplementMap x))) = _
    rw [hpoint]
    change standardUnlinkComplementStereographicDiffeomorph.symm
        (standardUnlinkComplementStereographicDiffeomorph
          (standardUnlinkNormalizedFlattenedRealComplement H havoid ((t : ℝ), x))) = _
    rw [standardUnlinkComplementStereographicDiffeomorph.symm_apply_apply]
    exact standardUnlinkNormalizedFlattenedRealComplement_interval H havoid (t, x)

/-- The normalized unlink-avoiding sphere isotopy extends to a continuous ambient isotopy of the
strict unlink complement whose every time slice is exactly a smooth diffeomorphism. -/
theorem exists_standardUnlinkNormalizedFlattenedComplementSmoothAmbientIsotopy
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier) :
    ∃ (Phi : TauCeti.AmbientIsotopy StandardUnlinkComplement)
        (Psi : I →
          StandardUnlinkComplement
            ≃ₘ^∞⟮(modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))),
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))⟯
            StandardUnlinkComplement),
      (∀ (t : I) (y : StandardUnlinkComplement),
        Phi.toContinuousMap (t, y) = Psi t y) ∧
      (∀ (t : I) (x : Sphere 3),
        Phi.toContinuousMap (t, equatorUnlinkComplementMap x) =
          standardUnlinkNormalizedComplementHomotopy H havoid
            (unitInterval.endpointFlatTime t, x)) ∧
      ContMDiff ((𝓡∂ 1).prod (𝓡 4)) (𝓡 4) ∞
        (fun p : I × StandardUnlinkComplement ↦ Psi p.1 p.2) := by
  obtain ⟨_, Phi, Psi, _, _, hPhi, htrace, hPsi⟩ :=
    exists_standardUnlinkNormalizedFlattenedComplementSmoothAmbientIsotopy_supported
      H havoid
  exact ⟨Phi, Psi, hPhi, htrace, hPsi⟩

end SplittingSpheres

end
