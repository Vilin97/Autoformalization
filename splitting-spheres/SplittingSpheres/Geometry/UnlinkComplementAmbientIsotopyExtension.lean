/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.AmbientIsotopyHomeomorphTransport
public import SplittingSpheres.Foundations.CompactlySupportedSmoothEmbeddedExtension
public import SplittingSpheres.Foundations.TimeDependentFlowFixedPoints
public import SplittingSpheres.Geometry.UnlinkComplementStereographicTrace
public import SplittingSpheres.Geometry.UnlinkPowerAmbientIsotopyLift
public import SplittingSpheres.Foundations.SmoothIsotopyTraceEmbedding

/-!
# Ambient extension of unlink-avoiding sphere isotopies

The normalized sphere isotopy is flattened near its time endpoints, written in the global
stereographic chart on the strict standard-unlink complement, and extended from its closed
spacetime trace to a compactly supported smooth time-dependent vector field.  The selected flow
restricts to the stereographic image because it fixes the complement, and ODE uniqueness identifies
its trajectories on the trace with the prescribed flattened isotopy.

Conjugating by stereographic coordinates gives an ambient isotopy of
`StandardUnlinkComplement`.  Its canonical lift to every finite cyclic power cover agrees with the
existing labelled lift after endpoint flattening.  At time one the time change is the identity, so
this constructs the endpoint ambient-extension witness used by complement transport.

The ambient isotopies constructed here are continuous; no smoothness of their individual slices is
asserted.
-/

@[expose] public section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold Topology unitInterval

noncomputable section

namespace SplittingSpheres

local instance standardUnlinkTraceStereographicFinrankFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (4 + 1))) = 4 + 1) :=
  ⟨by simp⟩

/-- The chosen stereographic chart as a smooth partial diffeomorphism. -/
private def standardUnlinkStereographicPartialDiffeomorph :
    PartialDiffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (Sphere 4) (EuclideanSpace ℝ (Fin 4)) ∞ where
  __ := (stereographic' 4 standardUnlinkStereographicPole).toPartialEquiv
  open_source := (stereographic' 4 standardUnlinkStereographicPole).open_source
  open_target := (stereographic' 4 standardUnlinkStereographicPole).open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas
    (show stereographic' 4 standardUnlinkStereographicPole ∈
      IsManifold.maximalAtlas
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞ (Sphere 4) from
        IsManifold.subset_maximalAtlas
          ⟨standardUnlinkStereographicPole, rfl⟩)
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas
    (show stereographic' 4 standardUnlinkStereographicPole ∈
      IsManifold.maximalAtlas
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞ (Sphere 4) from
        IsManifold.subset_maximalAtlas
          ⟨standardUnlinkStereographicPole, rfl⟩)

/-- Product of the identity real-time chart with the chosen stereographic chart. -/
private def standardUnlinkStereographicTracePartialDiffeomorph :
    PartialDiffeomorph
      ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (ℝ × Sphere 4) (ℝ × EuclideanSpace ℝ (Fin 4)) ∞ where
  __ := (PartialEquiv.refl ℝ).prod
    standardUnlinkStereographicPartialDiffeomorph.toPartialEquiv
  open_source := by
    rw [PartialEquiv.prod_source]
    exact isOpen_univ.prod standardUnlinkStereographicPartialDiffeomorph.open_source
  open_target := by
    rw [PartialEquiv.prod_target]
    exact isOpen_univ.prod standardUnlinkStereographicPartialDiffeomorph.open_target
  contMDiffOn_toFun := by
    rw [PartialEquiv.prod_source]
    exact contMDiff_id.contMDiffOn.prodMap
      standardUnlinkStereographicPartialDiffeomorph.contMDiffOn_toFun
  contMDiffOn_invFun := by
    rw [PartialEquiv.prod_target]
    exact contMDiff_id.contMDiffOn.prodMap
      standardUnlinkStereographicPartialDiffeomorph.contMDiffOn_invFun

abbrev StandardUnlinkTraceDomainModel : Type :=
  ℝ × EuclideanSpace ℝ (Fin 3)

abbrev StandardUnlinkStereographicSpacetime : Type :=
  ℝ × EuclideanSpace ℝ (Fin 4)

local instance standardUnlinkTraceRawChartedSpace :
    ChartedSpace StandardUnlinkTraceDomainModel (ℝ × Sphere 3) :=
  inferInstanceAs
    (ChartedSpace (ModelProd ℝ (EuclideanSpace ℝ (Fin 3))) (ℝ × Sphere 3))

local instance standardUnlinkTraceRawManifold :
    IsManifold (modelWithCornersSelf ℝ StandardUnlinkTraceDomainModel) ∞
      (ℝ × Sphere 3) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod ℝ (Sphere 3)

variable {S : SmoothSphereEmbedding 3 4}

private theorem standardUnlinkNormalizedSphereTrace_mem_stereographicSource
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier)
    (p : ℝ × Sphere 3) :
    (standardUnlinkNormalizedSphereIsotopy H).flattenedRealTimeTrace p ∈
      standardUnlinkStereographicTracePartialDiffeomorph.source := by
  change p.1 ∈ (Set.univ : Set ℝ) ∧
    (standardUnlinkNormalizedSphereIsotopy H).flattenedRealTime p ∈
      (stereographic' 4 standardUnlinkStereographicPole).source
  refine ⟨Set.mem_univ _, ?_⟩
  rw [stereographic'_source]
  intro hpole
  have ha := standardUnlinkNormalizedSphereIsotopy_avoids H havoid
    (unitInterval.endpointFlatTimeReal p.1, p.2)
  apply ha
  change (standardUnlinkNormalizedSphereIsotopy H).flattenedRealTime p ∈
    standardUnlinkCarrier
  rw [hpole]
  exact standardUnlinkStereographicPole_mem_carrier

private theorem standardUnlinkStereographicTracePartialDiffeomorph_comp_apply
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier)
    (p : ℝ × Sphere 3) :
    standardUnlinkStereographicTracePartialDiffeomorph
        ((standardUnlinkNormalizedSphereIsotopy H).flattenedRealTimeTrace p) =
      standardUnlinkNormalizedFlattenedStereographicTrace H havoid p := by
  apply Prod.ext
  · rfl
  · rfl

/-- The concrete endpoint-flattened trace in stereographic coordinates is a smooth embedding. -/
theorem isSmoothEmbedding_standardUnlinkNormalizedFlattenedStereographicTrace
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier) :
    Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ StandardUnlinkTraceDomainModel)
      (modelWithCornersSelf ℝ StandardUnlinkStereographicSpacetime) ∞
      (standardUnlinkNormalizedFlattenedStereographicTrace H havoid) := by
  have himmProd : Manifold.IsImmersion
      ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))))
      ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))) ∞
      (standardUnlinkNormalizedFlattenedStereographicTrace H havoid) := by
    have himmC : Manifold.IsImmersionOfComplement ℝ
        ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))))
        ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))) ∞
        (standardUnlinkNormalizedFlattenedStereographicTrace H havoid) := by
      intro p
      have hp :=
        SmoothSphereIsotopy.isImmersionOfComplement_flattenedRealTimeTrace
          (standardUnlinkNormalizedSphereIsotopy H) p
      have hpost := hp.postcomp_partialDiffeomorph
        standardUnlinkStereographicTracePartialDiffeomorph
        (standardUnlinkNormalizedSphereTrace_mem_stereographicSource H havoid p)
      apply hpost.congr_of_eventuallyEq
      filter_upwards [] with q
      exact standardUnlinkStereographicTracePartialDiffeomorph_comp_apply H havoid q
    exact himmC.isImmersion
  apply Manifold.IsSmoothEmbedding.mk
  · rw [← modelWithCornersSelf_prod, ← modelWithCornersSelf_prod,
      chartedSpaceSelf_prod] at himmProd
    exact himmProd
  · exact (isClosedEmbedding_standardUnlinkNormalizedFlattenedStereographicTrace
      H havoid).isEmbedding

theorem exists_standardUnlinkNormalizedFlattenedStereographicSpacetimeField
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier) :
    ∃ V : StandardUnlinkStereographicSpacetime → EuclideanSpace ℝ (Fin 4),
      ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
        tsupport V ⊆ standardUnlinkComplementStereographicSpacetime ∧
        ∀ p,
          V (standardUnlinkNormalizedFlattenedStereographicTrace H havoid p) =
            standardUnlinkNormalizedFlattenedStereographicVelocity H havoid p := by
  apply exists_contDiff_compactSupport_extension_of_isClosed_range_isSmoothEmbedding
    (isSmoothEmbedding_standardUnlinkNormalizedFlattenedStereographicTrace H havoid)
    (isClosedEmbedding_standardUnlinkNormalizedFlattenedStereographicTrace
      H havoid).isClosed_range
  · exact contMDiff_standardUnlinkNormalizedFlattenedStereographicVelocity H havoid
  · exact isCompact_standardUnlinkNormalizedFlattenedStereographicActiveTrace H havoid
  · exact isOpen_standardUnlinkComplementStereographicSpacetime
  · exact standardUnlinkNormalizedFlattenedStereographicActiveTrace_subset_spacetime H havoid
  · intro p hp
    exact standardUnlinkNormalizedFlattenedStereographicTrace_mem_active_of_velocity_ne_zero
      H havoid p hp

private theorem hasDerivAt_standardUnlinkNormalizedFlattenedStereographic
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

/-- The flattened stereographic family is the exact restriction of an ambient isotopy of the
unlink-complement chart image. -/
theorem exists_standardUnlinkNormalizedFlattenedStereographicAmbientIsotopy
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier) :
    ∃ Ψ : TauCeti.AmbientIsotopy standardUnlinkComplementStereographicImage,
      ∀ (t : I) (x : Sphere 3),
        (((Ψ.toContinuousMap
          (t, standardUnlinkNormalizedFlattenedStereographicPoint H havoid (0, x))) :
            standardUnlinkComplementStereographicImage) :
              EuclideanSpace ℝ (Fin 4)) =
          standardUnlinkNormalizedFlattenedStereographic H havoid ((t : ℝ), x) := by
  obtain ⟨V, hVsmooth, hVcompact, hVsupport, hVtrace⟩ :=
    exists_standardUnlinkNormalizedFlattenedStereographicSpacetimeField H havoid
  have hVzeroOutside : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 4)),
      y ∉ standardUnlinkComplementStereographicImage → V (t, y) = 0 := by
    intro t y hy
    by_contra hne
    have hmem : (t, y) ∈ tsupport V := subset_tsupport V hne
    exact hy (hVsupport hmem).2
  obtain ⟨Ψ, eFlow, happly, hflow, _⟩ :=
    TimeDependentFlow.exists_restrictedAmbientIsotopy_of_contDiff_hasCompactSupport
      standardUnlinkComplementStereographicImage V
      (hVsmooth.of_le (by norm_num)) hVcompact hVzeroOutside
  refine ⟨Ψ, ?_⟩
  intro t x
  let x₀ : EuclideanSpace ℝ (Fin 4) :=
    standardUnlinkNormalizedFlattenedStereographic H havoid (0, x)
  let g : ℝ → EuclideanSpace ℝ (Fin 4) := fun s ↦
    standardUnlinkNormalizedFlattenedStereographic H havoid (s, x)
  obtain ⟨K, hVlip⟩ :=
    hVsmooth.lipschitzWith_of_hasCompactSupport hVcompact (by norm_num)
  have hspaceLip : ∀ s : ℝ, LipschitzWith K (fun y : EuclideanSpace ℝ (Fin 4) ↦ V (s, y)) := by
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
      (v := fun s y ↦ V (s, y)) (s := fun _ ↦ Set.univ) (K := K) (t₀ := 0)
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
      exact hasDerivAt_standardUnlinkNormalizedFlattenedStereographic H havoid x s
    · simp
    · calc
        eFlow (x₀, 0) =
            (((Ψ.toContinuousMap
              (0, standardUnlinkNormalizedFlattenedStereographicPoint H havoid (0, x)) :
                standardUnlinkComplementStereographicImage) :
                  EuclideanSpace ℝ (Fin 4))) := by
                    rw [happly]
                    rfl
        _ = x₀ := by
          rw [Ψ.map_zero_left]
          rfl
        _ = g 0 := rfl
  calc
    (((Ψ.toContinuousMap
        (t, standardUnlinkNormalizedFlattenedStereographicPoint H havoid (0, x)) :
          standardUnlinkComplementStereographicImage) :
            EuclideanSpace ℝ (Fin 4))) = eFlow (x₀, (t : ℝ)) := happly t _
    _ = g (t : ℝ) := hEq ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
    _ = standardUnlinkNormalizedFlattenedStereographic H havoid ((t : ℝ), x) := rfl

@[simp]
theorem standardUnlinkNormalizedFlattenedStereographicPoint_zero
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier) (x : Sphere 3) :
    standardUnlinkNormalizedFlattenedStereographicPoint H havoid (0, x) =
      standardUnlinkComplementStereographicDiffeomorph
        (equatorUnlinkComplementMap x) := by
  change standardUnlinkComplementStereographicDiffeomorph
      (standardUnlinkNormalizedFlattenedRealComplement H havoid (0, x)) =
    standardUnlinkComplementStereographicDiffeomorph
      (equatorUnlinkComplementMap x)
  congr 1
  simpa using standardUnlinkNormalizedFlattenedRealComplement_interval
    H havoid ((0 : I), x)

/-- Pull the stereographic ambient isotopy back to the strict unlink complement. -/
theorem exists_standardUnlinkNormalizedFlattenedComplementAmbientIsotopy
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier) :
    ∃ Φ : TauCeti.AmbientIsotopy StandardUnlinkComplement,
      ∀ (t : I) (x : Sphere 3),
        Φ.toContinuousMap (t, equatorUnlinkComplementMap x) =
          standardUnlinkNormalizedComplementHomotopy H havoid
            (unitInterval.endpointFlatTime t, x) := by
  obtain ⟨Ψ, hΨ⟩ :=
    exists_standardUnlinkNormalizedFlattenedStereographicAmbientIsotopy H havoid
  let e := standardUnlinkComplementStereographicDiffeomorph.toHomeomorph
  let Φ : TauCeti.AmbientIsotopy StandardUnlinkComplement :=
    Ψ.pullbackHomeomorph e
  refine ⟨Φ, ?_⟩
  intro t x
  have hpoint : Ψ.toContinuousMap
        (t, standardUnlinkComplementStereographicDiffeomorph
          (equatorUnlinkComplementMap x)) =
      standardUnlinkNormalizedFlattenedStereographicPoint H havoid ((t : ℝ), x) := by
    apply Subtype.ext
    rw [← standardUnlinkNormalizedFlattenedStereographicPoint_zero H havoid x]
    exact hΨ t x
  change standardUnlinkComplementStereographicDiffeomorph.symm
      (Ψ.toContinuousMap
        (t, standardUnlinkComplementStereographicDiffeomorph
          (equatorUnlinkComplementMap x))) = _
  rw [hpoint]
  change standardUnlinkComplementStereographicDiffeomorph.symm
      (standardUnlinkComplementStereographicDiffeomorph
        (standardUnlinkNormalizedFlattenedRealComplement H havoid ((t : ℝ), x))) = _
  rw [standardUnlinkComplementStereographicDiffeomorph.symm_apply_apply]
  exact standardUnlinkNormalizedFlattenedRealComplement_interval H havoid (t, x)

/-- The canonical lift of an ambient extension of the flattened complement isotopy agrees with
the already constructed lift after the same time change. -/
theorem liftAmbientIsotopy_agrees_standardUnlinkPowerIsotopyLift_endpointFlatTime
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier)
    (Φ : TauCeti.AmbientIsotopy StandardUnlinkComplement)
    (hΦ : ∀ t x,
      Φ.toContinuousMap (t, equatorUnlinkComplementMap x) =
        standardUnlinkNormalizedComplementHomotopy H havoid
          (unitInterval.endpointFlatTime t, x))
    (t : I) (x : Sphere 3) :
    (IsCoveringMap.liftAmbientIsotopy
      (isCoveringMap_standardUnlinkPowerPullbackProj m) Φ).toContinuousMap
        (t, equatorUnlinkPowerLift m a x) =
      standardUnlinkPowerIsotopyLift m a H havoid
        (unitInterval.endpointFlatTime t, x) := by
  let g₁ : I → StandardUnlinkPowerPullback m := fun s ↦
    (IsCoveringMap.liftAmbientIsotopy
      (isCoveringMap_standardUnlinkPowerPullbackProj m) Φ).toContinuousMap
        (s, equatorUnlinkPowerLift m a x)
  let g₂ : I → StandardUnlinkPowerPullback m := fun s ↦
    standardUnlinkPowerIsotopyLift m a H havoid
      (unitInterval.endpointFlatTime s, x)
  have hg₁ : Continuous g₁ := by
    exact (IsCoveringMap.liftAmbientIsotopy
      (isCoveringMap_standardUnlinkPowerPullbackProj m) Φ).continuous.comp
        (continuous_id.prodMk continuous_const)
  have hg₂ : Continuous g₂ := by
    exact (standardUnlinkPowerIsotopyLift m a H havoid).continuous.comp
      (unitInterval.contMDiff_endpointFlatTime.continuous.prodMk continuous_const)
  have hcomp : standardUnlinkPowerPullbackProj m ∘ g₁ =
      standardUnlinkPowerPullbackProj m ∘ g₂ := by
    funext s
    change standardUnlinkPowerPullbackProj m
        ((IsCoveringMap.liftAmbientIsotopy
          (isCoveringMap_standardUnlinkPowerPullbackProj m) Φ).toContinuousMap
            (s, equatorUnlinkPowerLift m a x)) =
      standardUnlinkPowerPullbackProj m
        (standardUnlinkPowerIsotopyLift m a H havoid
          (unitInterval.endpointFlatTime s, x))
    rw [IsCoveringMap.proj_liftAmbientIsotopy
          (isCoveringMap_standardUnlinkPowerPullbackProj m) Φ
          (s, equatorUnlinkPowerLift m a x),
      equatorUnlinkPowerLift_proj, hΦ,
      standardUnlinkPowerIsotopyLift_proj]
  have hzero : g₁ 0 = g₂ 0 := by
    simp [g₁, g₂]
  have heq : g₁ = g₂ :=
    (isCoveringMap_standardUnlinkPowerPullbackProj m).eq_of_comp_eq
      hg₁ hg₂ hcomp 0 hzero
  exact congrFun heq t

/-- An ambient extension of the endpoint-flattened downstairs isotopy is enough for the
endpoint-only witness used in the power cover. -/
noncomputable def
    standardUnlinkPowerIsotopyLiftAmbientExtension_of_flattenedComplementAmbientIsotopy
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier)
    (Φ : TauCeti.AmbientIsotopy StandardUnlinkComplement)
    (hΦ : ∀ t x,
      Φ.toContinuousMap (t, equatorUnlinkComplementMap x) =
        standardUnlinkNormalizedComplementHomotopy H havoid
          (unitInterval.endpointFlatTime t, x)) :
    StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid where
  ambientIsotopy :=
    IsCoveringMap.liftAmbientIsotopy
      (isCoveringMap_standardUnlinkPowerPullbackProj m) Φ
  final_agrees x := by
    rw [TauCeti.AmbientIsotopy.final_apply]
    simpa using
      liftAmbientIsotopy_agrees_standardUnlinkPowerIsotopyLift_endpointFlatTime
        m a H havoid Φ hΦ 1 x

/-- The normalized unlink-avoiding sphere isotopy has the endpoint ambient-extension witness
required for complement transport in every finite cyclic power cover and on every sheet. -/
noncomputable def standardUnlinkPowerIsotopyLiftAmbientExtension
    (m : ℕ) [NeZero m] (a : ZMod m)
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ q, H.toFun q ∉ standardUnlinkCarrier) :
    StandardUnlinkPowerIsotopyLiftAmbientExtension m a H havoid := by
  let hex := exists_standardUnlinkNormalizedFlattenedComplementAmbientIsotopy H havoid
  let Φ := Classical.choose hex
  let hΦ := Classical.choose_spec hex
  exact standardUnlinkPowerIsotopyLiftAmbientExtension_of_flattenedComplementAmbientIsotopy
    m a H havoid Φ hΦ

end SplittingSpheres
