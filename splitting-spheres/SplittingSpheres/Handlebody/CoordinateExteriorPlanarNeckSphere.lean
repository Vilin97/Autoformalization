/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarCapComplement
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckArc
public import SplittingSpheres.Handlebody.ProductFourBoundaryAttachment

/-!
# Spinning a lifted neck arc to a three-sphere

A cut arc times `S²` is only a cylinder.  Its two boundary copies of `S²` are capped by the two
`B³` fibers in the one-handle face.  The resulting domain is the full boundary of `D¹ × B³`, hence
an honest `S³` by `ProductFourBoundaryAttachment`.

This file constructs the compatible side and end maps into the flower partial spin and descends
them to that boundary pushout.  No local-flatness, separation, connected-sum, or smooth-embedding
claim is made here.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped Topology

namespace SplittingSpheres

/-! ## Endpoint coordinates on the retained outer circle -/

/-- A point of `S⁰` regarded as the corresponding endpoint of the unit interval. -/
def productFourEndUnitInterval
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) : Set.Icc (0 : ℝ) 1 :=
  euclideanClosedBallOneToUnitInterval
    ⟨e.1, sphere_subset_closedBall e.2⟩

@[simp]
theorem productFourEndUnitInterval_coe
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    (productFourEndUnitInterval e : ℝ) = (e.1 0 + 1) / 2 :=
  rfl

theorem productFourEndUnitInterval_eq_zero_or_one
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    productFourEndUnitInterval e = 0 ∨ productFourEndUnitInterval e = 1 :=
  euclideanClosedBallOneToUnitInterval_of_mem_sphere
    ⟨e.1, sphere_subset_closedBall e.2⟩ e.2

theorem continuous_productFourEndUnitInterval :
    Continuous productFourEndUnitInterval := by
  exact euclideanClosedBallOneHomeomorphUnitInterval.continuous.comp <|
    continuous_subtype_val.subtype_mk _

/-- The endpoint of a labelled neck arc, bundled in the exact polynomial outer boundary. -/
def coordinateUnlinkExteriorPlanarNeckEndpointBoundary
    (m : ℕ) [NeZero m] (a : ZMod m)
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    ↑(coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m) :=
  ⟨(coordinateUnlinkExteriorPlanarNeckArcTranslate m a
      (productFourEndUnitInterval e)).1.1, by
    rcases productFourEndUnitInterval_eq_zero_or_one e with h | h
    · simpa only [h] using
        coordinateUnlinkExteriorPlanarNeckArcTranslate_zero_mem_outerBoundary m a
    · simpa only [h] using
        coordinateUnlinkExteriorPlanarNeckArcTranslate_one_mem_outerBoundary m a⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckEndpointBoundary_coe
    (m : ℕ) [NeZero m] (a : ZMod m)
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    (coordinateUnlinkExteriorPlanarNeckEndpointBoundary m a e : ℂ) =
      (coordinateUnlinkExteriorPlanarNeckArcTranslate m a
        (productFourEndUnitInterval e)).1.1 :=
  rfl

theorem continuous_coordinateUnlinkExteriorPlanarNeckEndpointBoundary
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous (coordinateUnlinkExteriorPlanarNeckEndpointBoundary m a) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp <| continuous_subtype_val.comp <|
    (continuous_coordinateUnlinkExteriorPlanarNeckArcTranslate m a).comp
      continuous_productFourEndUnitInterval

/-- The retained-outer-circle parameter of a labelled neck endpoint. -/
def coordinateUnlinkExteriorPlanarNeckOuterParameter
    (m : ℕ) [NeZero m] (a : ZMod m)
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) : Sphere 1 :=
  (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m).symm
    (coordinateUnlinkExteriorPlanarNeckEndpointBoundary m a e)

theorem continuous_coordinateUnlinkExteriorPlanarNeckOuterParameter
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous (coordinateUnlinkExteriorPlanarNeckOuterParameter m a) :=
  (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m).symm.continuous.comp
    (continuous_coordinateUnlinkExteriorPlanarNeckEndpointBoundary m a)

/-- The retained outer circle at the selected endpoint parameter is exactly the labelled neck
endpoint in flower coordinates. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerOuter_neckOuterParameter
    (m : ℕ) [NeZero m] (a : ZMod m)
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    coordinateUnlinkExteriorPlanarFlowerOuter m
        (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e) =
      coordinateUnlinkExteriorPlanarNeckArcTranslate m a
        (productFourEndUnitInterval e) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coordinateUnlinkExteriorPlanarFlowerOuter_val]
  rw [← coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph_coe]
  unfold coordinateUnlinkExteriorPlanarNeckOuterParameter
  rw [(coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m).apply_symm_apply]
  rfl

theorem injective_coordinateUnlinkExteriorPlanarFlowerOuter
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarFlowerOuter m) := by
  intro u v h
  apply injective_coordinateUnlinkExteriorPlanarOuterLift m
  apply (coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph m).injective
  exact h

-- Distinct labels or distinct ends give distinct retained-outer-circle parameters.
set_option maxHeartbeats 2000000 in
-- The nested outer-boundary and flower homeomorphisms are expensive to normalize.
theorem injective_coordinateUnlinkExteriorPlanarNeckOuterParameterFamily
    (m : ℕ) [NeZero m] :
    Injective (fun x : ZMod m × sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ↦
      coordinateUnlinkExteriorPlanarNeckOuterParameter m x.1 x.2) := by
  rintro ⟨a, e⟩ ⟨b, f⟩ h
  have hparameter : coordinateUnlinkExteriorPlanarNeckOuterParameter m a e =
      coordinateUnlinkExteriorPlanarNeckOuterParameter m b f := by
    simpa only [] using h
  have harc : coordinateUnlinkExteriorPlanarNeckArcTranslate m a
        (productFourEndUnitInterval e) =
      coordinateUnlinkExteriorPlanarNeckArcTranslate m b
        (productFourEndUnitInterval f) := by
    rw [← coordinateUnlinkExteriorPlanarFlowerOuter_neckOuterParameter m a e,
      ← coordinateUnlinkExteriorPlanarFlowerOuter_neckOuterParameter m b f]
    exact congrArg (coordinateUnlinkExteriorPlanarFlowerOuter m) hparameter
  have hp : (a, productFourEndUnitInterval e) =
      (b, productFourEndUnitInterval f) :=
    injective_coordinateUnlinkExteriorPlanarNeckArcTranslate m harc
  have hab : a = b := congrArg Prod.fst hp
  have hefInterval : productFourEndUnitInterval e = productFourEndUnitInterval f :=
    congrArg Prod.snd hp
  have hefBall :
      (⟨e.1, sphere_subset_closedBall e.2⟩ : EuclideanClosedBall 1) =
        ⟨f.1, sphere_subset_closedBall f.2⟩ :=
    euclideanClosedBallOneHomeomorphUnitInterval.injective hefInterval
  have hef : e = f := Subtype.ext <|
    congrArg (fun d : EuclideanClosedBall 1 ↦ d.1) hefBall
  exact Prod.ext hab hef

/-! ## Compatible side and end maps -/

/-- The spun side cylinder of a labelled neck sphere. -/
def coordinateUnlinkExteriorPlanarNeckSideMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(ProductFourSidePiece,
      CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) where
  toFun x :=
    partialSphereSpinInr (coordinateUnlinkExteriorPlanarFlowerOuter m)
      (coordinateUnlinkExteriorPlanarNeckArcTranslate m a
        (euclideanClosedBallOneHomeomorphUnitInterval x.1), x.2)
  continuous_toFun :=
    (partialSphereSpinInr (coordinateUnlinkExteriorPlanarFlowerOuter m)).continuous.comp <|
      (((continuous_coordinateUnlinkExteriorPlanarNeckArcTranslate m a).comp
        (euclideanClosedBallOneHomeomorphUnitInterval.continuous.comp continuous_fst)).prodMk
          continuous_snd)

/-- The two one-handle end balls of a labelled neck sphere. -/
def coordinateUnlinkExteriorPlanarNeckEndMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(ProductFourEndPiece,
      CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) where
  toFun x :=
    partialSphereSpinInl (coordinateUnlinkExteriorPlanarFlowerOuter m)
      (coordinateUnlinkExteriorPlanarNeckOuterParameter m a x.1, x.2)
  continuous_toFun :=
    (partialSphereSpinInl (coordinateUnlinkExteriorPlanarFlowerOuter m)).continuous.comp <|
      (((continuous_coordinateUnlinkExteriorPlanarNeckOuterParameter m a).comp
        continuous_fst).prodMk continuous_snd)

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckSideMap_apply
    (m : ℕ) [NeZero m] (a : ZMod m) (x : ProductFourSidePiece) :
    coordinateUnlinkExteriorPlanarNeckSideMap m a x =
      partialSphereSpinInr (coordinateUnlinkExteriorPlanarFlowerOuter m)
        (coordinateUnlinkExteriorPlanarNeckArcTranslate m a
          (euclideanClosedBallOneHomeomorphUnitInterval x.1), x.2) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckEndMap_apply
    (m : ℕ) [NeZero m] (a : ZMod m) (x : ProductFourEndPiece) :
    coordinateUnlinkExteriorPlanarNeckEndMap m a x =
      partialSphereSpinInl (coordinateUnlinkExteriorPlanarFlowerOuter m)
        (coordinateUnlinkExteriorPlanarNeckOuterParameter m a x.1, x.2) :=
  rfl

set_option maxHeartbeats 1000000 in
-- The pushout coprojection and the two nested flower subtypes expand during injectivity.
theorem coordinateUnlinkExteriorPlanarNeckSideMap_eq
    (m : ℕ) [NeZero m] (a b : ZMod m) (x y : ProductFourSidePiece)
    (h : coordinateUnlinkExteriorPlanarNeckSideMap m a x =
      coordinateUnlinkExteriorPlanarNeckSideMap m b y) :
    a = b ∧ x = y := by
  have hpair :
      (coordinateUnlinkExteriorPlanarNeckArcTranslate m a
          (euclideanClosedBallOneHomeomorphUnitInterval x.1), x.2) =
        (coordinateUnlinkExteriorPlanarNeckArcTranslate m b
          (euclideanClosedBallOneHomeomorphUnitInterval y.1), y.2) :=
    topologicalPushoutInr_injective
      oneHandleBoundaryInclusion
      (partialSphereSpinBoundaryInclusion
        (coordinateUnlinkExteriorPlanarFlowerOuter m))
      oneHandleBoundaryInclusion_injective h
  have harc : coordinateUnlinkExteriorPlanarNeckArcTranslate m a
        (euclideanClosedBallOneHomeomorphUnitInterval x.1) =
      coordinateUnlinkExteriorPlanarNeckArcTranslate m b
        (euclideanClosedBallOneHomeomorphUnitInterval y.1) :=
    congrArg (fun q : CoordinateUnlinkExteriorPlanarFlower m × Sphere 2 ↦ q.1) hpair
  have hp : (a, euclideanClosedBallOneHomeomorphUnitInterval x.1) =
      (b, euclideanClosedBallOneHomeomorphUnitInterval y.1) :=
    injective_coordinateUnlinkExteriorPlanarNeckArcTranslate m harc
  have hab : a = b := congrArg
    (fun q : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval ↦ q.1) hp
  have hxyInterval : euclideanClosedBallOneHomeomorphUnitInterval x.1 =
      euclideanClosedBallOneHomeomorphUnitInterval y.1 := congrArg
    (fun q : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval ↦ q.2) hp
  have hxy : x.1 = y.1 :=
    euclideanClosedBallOneHomeomorphUnitInterval.injective hxyInterval
  have hs : x.2 = y.2 :=
    congrArg (fun q : CoordinateUnlinkExteriorPlanarFlower m × Sphere 2 ↦ q.2) hpair
  exact ⟨hab, Prod.ext hxy hs⟩

theorem injective_coordinateUnlinkExteriorPlanarFlowerSpinBoundaryInclusion
    (m : ℕ) [NeZero m] :
    Injective (partialSphereSpinBoundaryInclusion
      (coordinateUnlinkExteriorPlanarFlowerOuter m)) := by
  intro x y h
  change (coordinateUnlinkExteriorPlanarFlowerOuter m x.1, x.2) =
    (coordinateUnlinkExteriorPlanarFlowerOuter m y.1, y.2) at h
  exact Prod.ext
    (injective_coordinateUnlinkExteriorPlanarFlowerOuter m <|
      congrArg (fun q : CoordinateUnlinkExteriorPlanarFlower m × Sphere 2 ↦ q.1) h)
    (congrArg (fun q : CoordinateUnlinkExteriorPlanarFlower m × Sphere 2 ↦ q.2) h)

set_option maxHeartbeats 1000000 in
-- The pushout coprojection and outer-parameter homeomorphism expand during injectivity.
theorem coordinateUnlinkExteriorPlanarNeckEndMap_eq
    (m : ℕ) [NeZero m] (a b : ZMod m) (x y : ProductFourEndPiece)
    (h : coordinateUnlinkExteriorPlanarNeckEndMap m a x =
      coordinateUnlinkExteriorPlanarNeckEndMap m b y) :
    a = b ∧ x = y := by
  have hpair :
      (coordinateUnlinkExteriorPlanarNeckOuterParameter m a x.1, x.2) =
        (coordinateUnlinkExteriorPlanarNeckOuterParameter m b y.1, y.2) :=
    topologicalPushoutInl_injective
      oneHandleBoundaryInclusion
      (partialSphereSpinBoundaryInclusion
        (coordinateUnlinkExteriorPlanarFlowerOuter m))
      (injective_coordinateUnlinkExteriorPlanarFlowerSpinBoundaryInclusion m) h
  have hparameter : coordinateUnlinkExteriorPlanarNeckOuterParameter m a x.1 =
      coordinateUnlinkExteriorPlanarNeckOuterParameter m b y.1 :=
    congrArg (fun q : Sphere 1 × EuclideanClosedBall 3 ↦ q.1) hpair
  have hae : (a, x.1) = (b, y.1) :=
    injective_coordinateUnlinkExteriorPlanarNeckOuterParameterFamily m hparameter
  have hab : a = b :=
    congrArg (fun q : ZMod m × sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ↦ q.1) hae
  have he : x.1 = y.1 :=
    congrArg (fun q : ZMod m × sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ↦ q.2) hae
  have hb : x.2 = y.2 :=
    congrArg (fun q : Sphere 1 × EuclideanClosedBall 3 ↦ q.2) hpair
  exact ⟨hab, Prod.ext he hb⟩

set_option maxHeartbeats 2000000 in
-- Both partial-spin faces and their nested subtype coordinates expand in the cross calculation.
theorem coordinateUnlinkExteriorPlanarNeckSideEnd_cross
    (m : ℕ) [NeZero m] (a b : ZMod m)
    (x : ProductFourSidePiece) (y : ProductFourEndPiece)
    (h : coordinateUnlinkExteriorPlanarNeckSideMap m a x =
      coordinateUnlinkExteriorPlanarNeckEndMap m b y) :
    a = b ∧ ∃ z : ProductFourCorner,
      productFourCornerToSide z = x ∧ productFourCornerToEnd z = y := by
  have hinter : ∃ z : OneHandleCapBoundary,
      oneHandleBoundaryInclusion z =
          (coordinateUnlinkExteriorPlanarNeckOuterParameter m b y.1, y.2) ∧
        partialSphereSpinBoundaryInclusion
            (coordinateUnlinkExteriorPlanarFlowerOuter m) z =
          (coordinateUnlinkExteriorPlanarNeckArcTranslate m a
            (euclideanClosedBallOneHomeomorphUnitInterval x.1), x.2) :=
    (topologicalPushoutInl_eq_inr_iff
      oneHandleBoundaryInclusion
      (partialSphereSpinBoundaryInclusion
        (coordinateUnlinkExteriorPlanarFlowerOuter m))
      oneHandleBoundaryInclusion_injective
      (coordinateUnlinkExteriorPlanarNeckOuterParameter m b y.1, y.2)
      (coordinateUnlinkExteriorPlanarNeckArcTranslate m a
        (euclideanClosedBallOneHomeomorphUnitInterval x.1), x.2)).mp h.symm
  obtain ⟨z, hzEnd, hzSide⟩ := hinter
  change (z.1, ⟨z.2.1, sphere_subset_closedBall z.2.2⟩) =
      (coordinateUnlinkExteriorPlanarNeckOuterParameter m b y.1, y.2) at hzEnd
  change (coordinateUnlinkExteriorPlanarFlowerOuter m z.1, z.2) =
      (coordinateUnlinkExteriorPlanarNeckArcTranslate m a
        (euclideanClosedBallOneHomeomorphUnitInterval x.1), x.2) at hzSide
  have hzParameter : z.1 =
      coordinateUnlinkExteriorPlanarNeckOuterParameter m b y.1 :=
    congrArg (fun q : Sphere 1 × EuclideanClosedBall 3 ↦ q.1) hzEnd
  have hzBall : (⟨z.2.1, sphere_subset_closedBall z.2.2⟩ : EuclideanClosedBall 3) = y.2 :=
    congrArg (fun q : Sphere 1 × EuclideanClosedBall 3 ↦ q.2) hzEnd
  have hzOuter : coordinateUnlinkExteriorPlanarFlowerOuter m z.1 =
      coordinateUnlinkExteriorPlanarNeckArcTranslate m a
        (euclideanClosedBallOneHomeomorphUnitInterval x.1) :=
    congrArg (fun q : CoordinateUnlinkExteriorPlanarFlower m × Sphere 2 ↦ q.1) hzSide
  have hzSphere : z.2 = x.2 :=
    congrArg (fun q : CoordinateUnlinkExteriorPlanarFlower m × Sphere 2 ↦ q.2) hzSide
  have harc : coordinateUnlinkExteriorPlanarNeckArcTranslate m b
        (productFourEndUnitInterval y.1) =
      coordinateUnlinkExteriorPlanarNeckArcTranslate m a
        (euclideanClosedBallOneHomeomorphUnitInterval x.1) := by
    rw [← coordinateUnlinkExteriorPlanarFlowerOuter_neckOuterParameter m b y.1,
      ← hzParameter]
    exact hzOuter
  have hp : (b, productFourEndUnitInterval y.1) =
      (a, euclideanClosedBallOneHomeomorphUnitInterval x.1) :=
    injective_coordinateUnlinkExteriorPlanarNeckArcTranslate m harc
  have hba : b = a := congrArg
    (fun q : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval ↦ q.1) hp
  have ht : productFourEndUnitInterval y.1 =
      euclideanClosedBallOneHomeomorphUnitInterval x.1 := congrArg
    (fun q : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval ↦ q.2) hp
  have hballOne :
      (⟨y.1.1, sphere_subset_closedBall y.1.2⟩ : EuclideanClosedBall 1) = x.1 :=
    euclideanClosedBallOneHomeomorphUnitInterval.injective ht
  refine ⟨hba.symm, ⟨(y.1, x.2), ?_, ?_⟩⟩
  · exact Prod.ext hballOne rfl
  · exact Prod.ext rfl <| by
      apply Subtype.ext
      calc
        x.2.1 = z.2.1 := congrArg Subtype.val hzSphere.symm
        _ = y.2.1 := congrArg Subtype.val hzBall

theorem coordinateUnlinkExteriorPlanarNeckFace_compatibility
    (m : ℕ) [NeZero m] (a : ZMod m) (z : ProductFourCorner) :
    coordinateUnlinkExteriorPlanarNeckSideMap m a (productFourCornerToSide z) =
      coordinateUnlinkExteriorPlanarNeckEndMap m a (productFourCornerToEnd z) := by
  rw [coordinateUnlinkExteriorPlanarNeckSideMap_apply,
    coordinateUnlinkExteriorPlanarNeckEndMap_apply]
  change
    partialSphereSpinInr (coordinateUnlinkExteriorPlanarFlowerOuter m)
        (coordinateUnlinkExteriorPlanarNeckArcTranslate m a
          (productFourEndUnitInterval z.1), z.2) =
      partialSphereSpinInl (coordinateUnlinkExteriorPlanarFlowerOuter m)
        (coordinateUnlinkExteriorPlanarNeckOuterParameter m a z.1,
          ⟨z.2.1, sphere_subset_closedBall z.2.2⟩)
  rw [← coordinateUnlinkExteriorPlanarFlowerOuter_neckOuterParameter m a z.1]
  exact (partialSphereSpin_condition
    (coordinateUnlinkExteriorPlanarFlowerOuter m)
    (coordinateUnlinkExteriorPlanarNeckOuterParameter m a z.1, z.2)).symm

/-- The continuous map of the boundary of `D¹ × B³` obtained by spinning and capping a labelled
neck arc. -/
def coordinateUnlinkExteriorPlanarNeckBoundaryMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(ProductFourBoundaryPushout,
      CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) :=
  topologicalPushoutDesc productFourCornerToSide productFourCornerToEnd
    (coordinateUnlinkExteriorPlanarNeckSideMap m a)
    (coordinateUnlinkExteriorPlanarNeckEndMap m a)
    (coordinateUnlinkExteriorPlanarNeckFace_compatibility m a)

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckBoundaryMap_inl
    (m : ℕ) [NeZero m] (a : ZMod m) (x : ProductFourSidePiece) :
    coordinateUnlinkExteriorPlanarNeckBoundaryMap m a
        (topologicalPushoutInl productFourCornerToSide productFourCornerToEnd x) =
      coordinateUnlinkExteriorPlanarNeckSideMap m a x :=
  topologicalPushoutDesc_inl _ _ _ _ _ x

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckBoundaryMap_inr
    (m : ℕ) [NeZero m] (a : ZMod m) (x : ProductFourEndPiece) :
    coordinateUnlinkExteriorPlanarNeckBoundaryMap m a
        (topologicalPushoutInr productFourCornerToSide productFourCornerToEnd x) =
      coordinateUnlinkExteriorPlanarNeckEndMap m a x :=
  topologicalPushoutDesc_inr _ _ _ _ _ x

set_option maxHeartbeats 2000000 in
-- The four pushout face cases repeatedly normalize the nested partial-spin coprojections.
theorem coordinateUnlinkExteriorPlanarNeckBoundaryMap_eq
    (m : ℕ) [NeZero m] (a b : ZMod m) (x y : ProductFourBoundaryPushout)
    (h : coordinateUnlinkExteriorPlanarNeckBoundaryMap m a x =
      coordinateUnlinkExteriorPlanarNeckBoundaryMap m b y) :
    a = b ∧ x = y := by
  rcases topologicalPushout_jointly_surjective
      productFourCornerToSide productFourCornerToEnd x with
    ⟨sx, rfl⟩ | ⟨ex, rfl⟩
  · rcases topologicalPushout_jointly_surjective
        productFourCornerToSide productFourCornerToEnd y with
      ⟨sy, rfl⟩ | ⟨ey, rfl⟩
    · rw [coordinateUnlinkExteriorPlanarNeckBoundaryMap_inl,
        coordinateUnlinkExteriorPlanarNeckBoundaryMap_inl] at h
      obtain ⟨hab, hxy⟩ :=
        coordinateUnlinkExteriorPlanarNeckSideMap_eq m a b sx sy h
      exact ⟨hab, congrArg
        (topologicalPushoutInl productFourCornerToSide productFourCornerToEnd) hxy⟩
    · rw [coordinateUnlinkExteriorPlanarNeckBoundaryMap_inl,
        coordinateUnlinkExteriorPlanarNeckBoundaryMap_inr] at h
      obtain ⟨hab, z, hzSide, hzEnd⟩ :=
        coordinateUnlinkExteriorPlanarNeckSideEnd_cross m a b sx ey h
      refine ⟨hab, ?_⟩
      rw [← hzSide, ← hzEnd]
      exact topologicalPushout_condition productFourCornerToSide productFourCornerToEnd z
  · rcases topologicalPushout_jointly_surjective
        productFourCornerToSide productFourCornerToEnd y with
      ⟨sy, rfl⟩ | ⟨ey, rfl⟩
    · rw [coordinateUnlinkExteriorPlanarNeckBoundaryMap_inr,
        coordinateUnlinkExteriorPlanarNeckBoundaryMap_inl] at h
      obtain ⟨hba, z, hzSide, hzEnd⟩ :=
        coordinateUnlinkExteriorPlanarNeckSideEnd_cross m b a sy ex h.symm
      refine ⟨hba.symm, ?_⟩
      rw [← hzEnd, ← hzSide]
      exact (topologicalPushout_condition
        productFourCornerToSide productFourCornerToEnd z).symm
    · rw [coordinateUnlinkExteriorPlanarNeckBoundaryMap_inr,
        coordinateUnlinkExteriorPlanarNeckBoundaryMap_inr] at h
      obtain ⟨hab, hxy⟩ :=
        coordinateUnlinkExteriorPlanarNeckEndMap_eq m a b ex ey h
      exact ⟨hab, congrArg
        (topologicalPushoutInr productFourCornerToSide productFourCornerToEnd) hxy⟩

theorem injective_coordinateUnlinkExteriorPlanarNeckBoundaryMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Injective (coordinateUnlinkExteriorPlanarNeckBoundaryMap m a) := by
  intro x y h
  exact (coordinateUnlinkExteriorPlanarNeckBoundaryMap_eq m a a x y h).2

theorem pairwise_disjoint_range_coordinateUnlinkExteriorPlanarNeckBoundaryMap
    (m : ℕ) [NeZero m] :
    Pairwise fun a b : ZMod m ↦
      Disjoint (range (coordinateUnlinkExteriorPlanarNeckBoundaryMap m a))
        (range (coordinateUnlinkExteriorPlanarNeckBoundaryMap m b)) := by
  intro a b hab
  rw [Set.disjoint_left]
  rintro q ⟨x, rfl⟩ ⟨y, hy⟩
  apply hab
  exact (coordinateUnlinkExteriorPlanarNeckBoundaryMap_eq m a b x y hy.symm).1

/-! ## Literal three-sphere parametrizations -/

/-- The labelled neck sphere, parametrized by the project's literal `Sphere 3`. -/
def coordinateUnlinkExteriorPlanarNeckSphereMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(Sphere 3, CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) where
  toFun s := coordinateUnlinkExteriorPlanarNeckBoundaryMap m a
    (productFourBoundaryPushoutHomeomorphSphere.symm s)
  continuous_toFun :=
    (coordinateUnlinkExteriorPlanarNeckBoundaryMap m a).continuous.comp
      productFourBoundaryPushoutHomeomorphSphere.symm.continuous

theorem injective_coordinateUnlinkExteriorPlanarNeckSphereMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Injective (coordinateUnlinkExteriorPlanarNeckSphereMap m a) :=
  (injective_coordinateUnlinkExteriorPlanarNeckBoundaryMap m a).comp
    productFourBoundaryPushoutHomeomorphSphere.symm.injective

/-- Each displayed neck `S³` is a topological embedding in the flower partial spin. -/
theorem isEmbedding_coordinateUnlinkExteriorPlanarNeckSphereMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsEmbedding (coordinateUnlinkExteriorPlanarNeckSphereMap m a) := by
  let _ : T2Space (CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) :=
    (coordinateUnlinkExteriorPlanarFlowerSpinCapComplementHomeomorphSphere m).symm.t2Space
  exact (coordinateUnlinkExteriorPlanarNeckSphereMap m a).continuous.isClosedEmbedding
    (injective_coordinateUnlinkExteriorPlanarNeckSphereMap m a) |>.isEmbedding

/-- The `m` labelled neck spheres have pairwise-disjoint full images. -/
theorem pairwise_disjoint_range_coordinateUnlinkExteriorPlanarNeckSphereMap
    (m : ℕ) [NeZero m] :
    Pairwise fun a b : ZMod m ↦
      Disjoint (range (coordinateUnlinkExteriorPlanarNeckSphereMap m a))
        (range (coordinateUnlinkExteriorPlanarNeckSphereMap m b)) := by
  intro a b hab
  rw [Set.disjoint_left]
  rintro q ⟨x, rfl⟩ ⟨y, hy⟩
  apply hab
  exact (coordinateUnlinkExteriorPlanarNeckBoundaryMap_eq m a b
    (productFourBoundaryPushoutHomeomorphSphere.symm x)
    (productFourBoundaryPushoutHomeomorphSphere.symm y) hy.symm).1

/-! ## Transport to the completely capped four-sphere -/

/-- The same neck sphere in the literal cap-complement subtype of the completely capped `S⁴`. -/
def coordinateUnlinkExteriorPlanarNeckSphereCapComplementMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(Sphere 3, ↑(coordinateUnlinkExteriorPlanarCapInteriorsSphere m)ᶜ) where
  toFun s := coordinateUnlinkExteriorPlanarFlowerSpinCapComplementHomeomorphSphere m
    (coordinateUnlinkExteriorPlanarNeckSphereMap m a s)
  continuous_toFun :=
    (coordinateUnlinkExteriorPlanarFlowerSpinCapComplementHomeomorphSphere m).continuous.comp
      (coordinateUnlinkExteriorPlanarNeckSphereMap m a).continuous

theorem isEmbedding_coordinateUnlinkExteriorPlanarNeckSphereCapComplementMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsEmbedding (coordinateUnlinkExteriorPlanarNeckSphereCapComplementMap m a) :=
  (coordinateUnlinkExteriorPlanarFlowerSpinCapComplementHomeomorphSphere m).isEmbedding.comp
    (isEmbedding_coordinateUnlinkExteriorPlanarNeckSphereMap m a)

/-- Forget the complement proof and regard the neck sphere as an ambient `S⁴` map. -/
def coordinateUnlinkExteriorPlanarNeckSphereAmbientMap
    (m : ℕ) [NeZero m] (a : ZMod m) : C(Sphere 3, Sphere 4) where
  toFun s := (coordinateUnlinkExteriorPlanarNeckSphereCapComplementMap m a s).1
  continuous_toFun := continuous_subtype_val.comp
    (coordinateUnlinkExteriorPlanarNeckSphereCapComplementMap m a).continuous

theorem isEmbedding_coordinateUnlinkExteriorPlanarNeckSphereAmbientMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsEmbedding (coordinateUnlinkExteriorPlanarNeckSphereAmbientMap m a) :=
  IsEmbedding.subtypeVal.comp
    (isEmbedding_coordinateUnlinkExteriorPlanarNeckSphereCapComplementMap m a)

theorem coordinateUnlinkExteriorPlanarNeckSphereAmbientMap_avoids_capInteriors
    (m : ℕ) [NeZero m] (a : ZMod m) (s : Sphere 3) :
    coordinateUnlinkExteriorPlanarNeckSphereAmbientMap m a s ∉
      coordinateUnlinkExteriorPlanarCapInteriorsSphere m :=
  (coordinateUnlinkExteriorPlanarNeckSphereCapComplementMap m a s).2

/-- Ambient transport preserves pairwise disjointness of the labelled neck spheres. -/
theorem pairwise_disjoint_range_coordinateUnlinkExteriorPlanarNeckSphereAmbientMap
    (m : ℕ) [NeZero m] :
    Pairwise fun a b : ZMod m ↦
      Disjoint (range (coordinateUnlinkExteriorPlanarNeckSphereAmbientMap m a))
        (range (coordinateUnlinkExteriorPlanarNeckSphereAmbientMap m b)) := by
  intro a b hab
  rw [Set.disjoint_left]
  rintro q ⟨x, rfl⟩ ⟨y, hy⟩
  apply hab
  have hsubtype :
      coordinateUnlinkExteriorPlanarNeckSphereCapComplementMap m b y =
        coordinateUnlinkExteriorPlanarNeckSphereCapComplementMap m a x :=
    Subtype.ext hy
  have hspin :=
    (coordinateUnlinkExteriorPlanarFlowerSpinCapComplementHomeomorphSphere m).injective hsubtype
  exact (coordinateUnlinkExteriorPlanarNeckBoundaryMap_eq m a b
    (productFourBoundaryPushoutHomeomorphSphere.symm x)
    (productFourBoundaryPushoutHomeomorphSphere.symm y) hspin.symm).1

end SplittingSpheres
