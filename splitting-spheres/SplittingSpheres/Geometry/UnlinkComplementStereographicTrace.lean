/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import SplittingSpheres.Foundations.SmoothIsotopyRealTimeExtension
public import SplittingSpheres.Geometry.UnlinkComplementStereographic
public import SplittingSpheres.Geometry.UnlinkSphereIsotopyPowerLift

/-!
# The flattened unlink-complement trace in stereographic coordinates

The normalized unlink-avoiding sphere isotopy is flattened at its time endpoints, extended to all
real times, and expressed in the global stereographic chart on the unlink complement.  Its
time-preserving spacetime trace is smooth, proper, injective, and therefore a closed topological
embedding.  The time velocity is smooth and vanishes off the compact active-time trace.

This file does not assert that the trace is a smooth embedding; the immersion normal-form proof is
a separate layer.
-/

@[expose] public section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold Topology unitInterval

noncomputable section

namespace SplittingSpheres

variable {S : SmoothSphereEmbedding 3 4}

/-- The normalized endpoint-flattened real-time family, valued in the strict unlink complement. -/
def standardUnlinkNormalizedFlattenedRealComplement
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ℝ × Sphere 3 → StandardUnlinkComplement := fun p ↦
  ⟨(standardUnlinkNormalizedSphereIsotopy H).flattenedRealTime p,
    standardUnlinkNormalizedSphereIsotopy_avoids H havoid
      (unitInterval.endpointFlatTimeReal p.1, p.2)⟩

theorem contMDiff_standardUnlinkNormalizedFlattenedRealComplement
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 4) ∞
      (standardUnlinkNormalizedFlattenedRealComplement H havoid) := by
  rw [← ContMDiff.subtypeVal_comp_iff standardUnlinkComplementOpens]
  exact (standardUnlinkNormalizedSphereIsotopy H).contMDiff_flattenedRealTime

@[simp]
theorem standardUnlinkNormalizedFlattenedRealComplement_coe
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) (p : ℝ × Sphere 3) :
    (standardUnlinkNormalizedFlattenedRealComplement H havoid p : Sphere 4) =
      (standardUnlinkNormalizedSphereIsotopy H).flattenedRealTime p := rfl

@[simp]
theorem standardUnlinkNormalizedFlattenedRealComplement_interval
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) (p : I × Sphere 3) :
    standardUnlinkNormalizedFlattenedRealComplement H havoid ((p.1 : ℝ), p.2) =
      standardUnlinkNormalizedComplementHomotopy H havoid
        (unitInterval.endpointFlatTime p.1, p.2) := by
  apply Subtype.ext
  rfl

/-- The real-time family as a point of the open stereographic image. -/
def standardUnlinkNormalizedFlattenedStereographicPoint
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ℝ × Sphere 3 → standardUnlinkComplementStereographicImage := fun p ↦
  standardUnlinkComplementStereographicDiffeomorph
    (standardUnlinkNormalizedFlattenedRealComplement H havoid p)

theorem contMDiff_standardUnlinkNormalizedFlattenedStereographicPoint
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ContMDiff (𝓘(ℝ).prod (𝓡 3))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (standardUnlinkNormalizedFlattenedStereographicPoint H havoid) :=
  standardUnlinkComplementStereographicDiffeomorph.contMDiff.comp
    (contMDiff_standardUnlinkNormalizedFlattenedRealComplement H havoid)

/-- The underlying Euclidean stereographic-coordinate family. -/
def standardUnlinkNormalizedFlattenedStereographic
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ℝ × Sphere 3 → EuclideanSpace ℝ (Fin 4) := fun p ↦
  standardUnlinkNormalizedFlattenedStereographicPoint H havoid p

theorem contMDiff_standardUnlinkNormalizedFlattenedStereographic
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ContMDiff (𝓘(ℝ).prod (𝓡 3))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (standardUnlinkNormalizedFlattenedStereographic H havoid) := by
  exact contMDiff_subtype_val.comp
    (contMDiff_standardUnlinkNormalizedFlattenedStereographicPoint H havoid)

/-- The ordinary real-time velocity of the stereographic-coordinate family. -/
def standardUnlinkNormalizedFlattenedStereographicVelocity
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ℝ × Sphere 3 → EuclideanSpace ℝ (Fin 4) :=
  realTimeVelocity (standardUnlinkNormalizedFlattenedStereographic H havoid)

theorem contMDiff_standardUnlinkNormalizedFlattenedStereographicVelocity
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ContMDiff (𝓘(ℝ).prod (𝓡 3))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (standardUnlinkNormalizedFlattenedStereographicVelocity H havoid) :=
  contMDiff_realTimeVelocity _
    (contMDiff_standardUnlinkNormalizedFlattenedStereographic H havoid)

theorem standardUnlinkNormalizedFlattenedStereographicVelocity_eq_zero_of_lt
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier)
    (p : ℝ × Sphere 3) (hp : p.1 < 1 / 4) :
    standardUnlinkNormalizedFlattenedStereographicVelocity H havoid p = 0 := by
  apply realTimeVelocity_eq_zero_of_eventuallyEq_const
    (c := standardUnlinkNormalizedFlattenedStereographic H havoid (0, p.2))
  filter_upwards [Iio_mem_nhds hp] with t ht
  have hc :
      standardUnlinkNormalizedFlattenedRealComplement H havoid (t, p.2) =
        standardUnlinkNormalizedFlattenedRealComplement H havoid (0, p.2) := by
    apply Subtype.ext
    change (standardUnlinkNormalizedSphereIsotopy H).flattenedRealTime (t, p.2) =
      (standardUnlinkNormalizedSphereIsotopy H).flattenedRealTime (0, p.2)
    exact ((standardUnlinkNormalizedSphereIsotopy H).flattenedRealTime_eq_zero
      ht.le p.2).trans
        ((standardUnlinkNormalizedSphereIsotopy H).flattenedRealTime_eq_zero
          (by norm_num) p.2).symm
  exact congrArg Subtype.val <|
    congrArg standardUnlinkComplementStereographicDiffeomorph hc

theorem standardUnlinkNormalizedFlattenedStereographicVelocity_eq_zero_of_gt
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier)
    (p : ℝ × Sphere 3) (hp : 3 / 4 < p.1) :
    standardUnlinkNormalizedFlattenedStereographicVelocity H havoid p = 0 := by
  apply realTimeVelocity_eq_zero_of_eventuallyEq_const
    (c := standardUnlinkNormalizedFlattenedStereographic H havoid (1, p.2))
  filter_upwards [Ioi_mem_nhds hp] with t ht
  have hc :
      standardUnlinkNormalizedFlattenedRealComplement H havoid (t, p.2) =
        standardUnlinkNormalizedFlattenedRealComplement H havoid (1, p.2) := by
    apply Subtype.ext
    change (standardUnlinkNormalizedSphereIsotopy H).flattenedRealTime (t, p.2) =
      (standardUnlinkNormalizedSphereIsotopy H).flattenedRealTime (1, p.2)
    exact ((standardUnlinkNormalizedSphereIsotopy H).flattenedRealTime_eq_one
      ht.le p.2).trans
        ((standardUnlinkNormalizedSphereIsotopy H).flattenedRealTime_eq_one
          (by norm_num) p.2).symm
  exact congrArg Subtype.val <|
    congrArg standardUnlinkComplementStereographicDiffeomorph hc

/-- The time-preserving trace of the stereographic-coordinate family. -/
def standardUnlinkNormalizedFlattenedStereographicTrace
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ℝ × Sphere 3 → ℝ × EuclideanSpace ℝ (Fin 4) := fun p ↦
  (p.1, standardUnlinkNormalizedFlattenedStereographic H havoid p)

@[simp]
theorem standardUnlinkNormalizedFlattenedStereographicTrace_fst
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) (p : ℝ × Sphere 3) :
    (standardUnlinkNormalizedFlattenedStereographicTrace H havoid p).1 = p.1 := rfl

@[simp]
theorem standardUnlinkNormalizedFlattenedStereographicTrace_snd
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) (p : ℝ × Sphere 3) :
    (standardUnlinkNormalizedFlattenedStereographicTrace H havoid p).2 =
      standardUnlinkNormalizedFlattenedStereographic H havoid p := rfl

theorem contMDiff_standardUnlinkNormalizedFlattenedStereographicTrace
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    ContMDiff (𝓘(ℝ).prod (𝓡 3))
      (𝓘(ℝ).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))) ∞
      (standardUnlinkNormalizedFlattenedStereographicTrace H havoid) :=
  contMDiff_fst.prodMk
    (contMDiff_standardUnlinkNormalizedFlattenedStereographic H havoid)

theorem injective_standardUnlinkNormalizedFlattenedStereographicTrace
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    Injective (standardUnlinkNormalizedFlattenedStereographicTrace H havoid) := by
  rintro ⟨t, x⟩ ⟨u, y⟩ h
  have htu : t = u := congrArg Prod.fst h
  subst u
  apply Prod.ext
  · rfl
  have hraw :
      standardUnlinkNormalizedFlattenedStereographic H havoid (t, x) =
        standardUnlinkNormalizedFlattenedStereographic H havoid (t, y) :=
    congrArg Prod.snd h
  have hpoint :
      standardUnlinkNormalizedFlattenedStereographicPoint H havoid (t, x) =
        standardUnlinkNormalizedFlattenedStereographicPoint H havoid (t, y) :=
    Subtype.ext hraw
  have hcomp := standardUnlinkComplementStereographicDiffeomorph.injective hpoint
  have hsphere :
      (standardUnlinkNormalizedSphereIsotopy H).flattenedRealTime (t, x) =
        (standardUnlinkNormalizedSphereIsotopy H).flattenedRealTime (t, y) :=
    congrArg Subtype.val hcomp
  exact ((standardUnlinkNormalizedSphereIsotopy H).isSmoothEmbedding_slice
    (unitInterval.endpointFlatTimeReal t)).isEmbedding.injective hsphere

theorem isProperMap_standardUnlinkNormalizedFlattenedStereographicTrace
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    IsProperMap (standardUnlinkNormalizedFlattenedStereographicTrace H havoid) := by
  apply isProperMap_of_comp_of_t2
    (contMDiff_standardUnlinkNormalizedFlattenedStereographicTrace H havoid).continuous
    continuous_fst
  simpa [standardUnlinkNormalizedFlattenedStereographicTrace, Function.comp_def] using
    (isProperMap_fst_of_compactSpace :
      IsProperMap (Prod.fst : ℝ × Sphere 3 → ℝ))

theorem isClosedEmbedding_standardUnlinkNormalizedFlattenedStereographicTrace
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    IsClosedEmbedding (standardUnlinkNormalizedFlattenedStereographicTrace H havoid) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (contMDiff_standardUnlinkNormalizedFlattenedStereographicTrace H havoid).continuous
    (injective_standardUnlinkNormalizedFlattenedStereographicTrace H havoid)
    (isProperMap_standardUnlinkNormalizedFlattenedStereographicTrace H havoid).isClosedMap

/-- The compact part of the spacetime trace on which its time velocity can be nonzero. -/
def standardUnlinkNormalizedFlattenedStereographicActiveTrace
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    Set (ℝ × EuclideanSpace ℝ (Fin 4)) :=
  standardUnlinkNormalizedFlattenedStereographicTrace H havoid ''
    (Icc (1 / 4 : ℝ) (3 / 4) ×ˢ (Set.univ : Set (Sphere 3)))

theorem isCompact_standardUnlinkNormalizedFlattenedStereographicActiveTrace
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    IsCompact (standardUnlinkNormalizedFlattenedStereographicActiveTrace H havoid) := by
  apply (isCompact_Icc.prod isCompact_univ).image
  exact (contMDiff_standardUnlinkNormalizedFlattenedStereographicTrace H havoid).continuous

/-- The Euclidean spacetime open set over the stereographic image of the unlink complement. -/
def standardUnlinkComplementStereographicSpacetime :
    Set (ℝ × EuclideanSpace ℝ (Fin 4)) :=
  Set.univ ×ˢ (standardUnlinkComplementStereographicImage :
    Set (EuclideanSpace ℝ (Fin 4)))

theorem isOpen_standardUnlinkComplementStereographicSpacetime :
    IsOpen standardUnlinkComplementStereographicSpacetime :=
  isOpen_univ.prod standardUnlinkComplementStereographicImage.isOpen

theorem standardUnlinkNormalizedFlattenedStereographicActiveTrace_subset_spacetime
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) :
    standardUnlinkNormalizedFlattenedStereographicActiveTrace H havoid ⊆
      standardUnlinkComplementStereographicSpacetime := by
  rintro _ ⟨p, _, rfl⟩
  exact ⟨Set.mem_univ p.1,
    (standardUnlinkNormalizedFlattenedStereographicPoint H havoid p).property⟩

theorem standardUnlinkNormalizedFlattenedStereographicTrace_mem_active_of_velocity_ne_zero
    (H : SmoothSphereIsotopy standardSplittingSphere S)
    (havoid : ∀ p, H.toFun p ∉ standardUnlinkCarrier) (p : ℝ × Sphere 3)
    (hp : standardUnlinkNormalizedFlattenedStereographicVelocity H havoid p ≠ 0) :
    standardUnlinkNormalizedFlattenedStereographicTrace H havoid p ∈
      standardUnlinkNormalizedFlattenedStereographicActiveTrace H havoid := by
  have hlower : (1 / 4 : ℝ) ≤ p.1 := by
    by_contra h
    exact hp (standardUnlinkNormalizedFlattenedStereographicVelocity_eq_zero_of_lt
      H havoid p (lt_of_not_ge h))
  have hupper : p.1 ≤ (3 / 4 : ℝ) := by
    by_contra h
    exact hp (standardUnlinkNormalizedFlattenedStereographicVelocity_eq_zero_of_gt
      H havoid p (lt_of_not_ge h))
  exact ⟨p, ⟨⟨hlower, hupper⟩, Set.mem_univ p.2⟩, rfl⟩

end SplittingSpheres
