/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutHomeomorph
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarLeftLeafBoundary
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckNormalizedPushout
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarOuterDeck
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarOuterParameterSplit

/-!
# The outer boundary of the normalized right node

The outer circle of the normalized right annulus alternates between the `m` lifted neck arcs
and the `m` retained right sectors.  This file expresses both families in the literal circle
coordinate of that annulus.  The upper endpoint of sector `a` meets neck `a + c`, where `c` is
the canonical but deliberately unevaluated endpoint offset supplied by covering-path lifting.

All constructions are point-set topological.  In particular, no cyclic orientation, smooth
gluing, separation, or connected-sum statement is made.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## The two families in the normalized annulus circle -/

/-- Bundle every retained right sector in the actual closed right flower half. -/
def coordinateUnlinkExteriorPlanarRightOuterSectorToRightHalf
    (m : ℕ) [NeZero m] :
    C(ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval,
      CoordinateUnlinkExteriorPlanarFlowerRightHalf m) where
  toFun x := ⟨coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m x.1 x.2, by
    change -1 / 2 ≤
      ((coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m x.1 x.2).1.1 ^ m).re
    rw [coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_pow]
    exact coordinateUnlinkExteriorPlanarBaseRightOuterArc_re_ge x.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_prod_of_discrete_left]
    exact fun a ↦ (coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m a).continuous

@[simp]
theorem coordinateUnlinkExteriorPlanarRightOuterSectorToRightHalf_apply
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarRightOuterSectorToRightHalf m x).1 =
      coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m x.1 x.2 :=
  rfl

/-- The lifted neck arcs, in the literal outer-circle coordinate of the normalized right
annulus. -/
def coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle
    (m : ℕ) [NeZero m] :
    C(ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval, Sphere 1) where
  toFun x := (coordinateUnlinkExteriorPlanarNormalizedRightSeam m x).1
  continuous_toFun :=
    continuous_fst.comp (coordinateUnlinkExteriorPlanarNormalizedRightSeam m).continuous

@[simp]
theorem coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle_apply
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle m x =
      (coordinateUnlinkExteriorPlanarNormalizedRightSeam m x).1 :=
  rfl

/-- The retained right sectors, in the literal outer-circle coordinate of the normalized right
annulus. -/
def coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle
    (m : ℕ) [NeZero m] :
    C(ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval, Sphere 1) where
  toFun x := ((coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m).symm
    (coordinateUnlinkExteriorPlanarRightOuterSectorToRightHalf m x)).1
  continuous_toFun := continuous_fst.comp <|
    (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m).symm.continuous.comp
      (coordinateUnlinkExteriorPlanarRightOuterSectorToRightHalf m).continuous

@[simp]
theorem coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle_apply
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m x =
      ((coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m).symm
        (coordinateUnlinkExteriorPlanarRightOuterSectorToRightHalf m x)).1 :=
  rfl

/-- Every retained right sector lies at annulus time `1`. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNormalizedRightOuter_time
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    ((coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m).symm
      (coordinateUnlinkExteriorPlanarRightOuterSectorToRightHalf m x)).2 = 1 := by
  let w := coordinateUnlinkExteriorPlanarRightOuterSectorToRightHalf m x
  have hw : w ∈ coordinateUnlinkExteriorPlanarFlowerRightHalfOuterEndpointSet m := by
    right
    change ‖(coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m x.1 x.2).1.1 ^ m +
      (1 / 2 : ℂ)‖ = sphereHandleRadius
    rw [coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_pow,
      coordinateUnlinkExteriorPlanarBaseRightOuterArc_add_half_norm]
  have hwRange : w ∈ range (fun u : Sphere 1 ↦
      coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m (u, 1)) := by
    rw [range_coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_one]
    exact hw
  obtain ⟨u, hu⟩ := hwRange
  have hinv : (u, 1) =
      (coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m).symm w := by
    rw [← hu]
    exact (coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m).symm_apply_apply _
      |>.symm
  simpa only [w] using congrArg Prod.snd hinv.symm

/-- Realizing the normalized seam circle at time `1` recovers the actual right-half seam. -/
theorem coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle_realize
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m
        (coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle m x, 1) =
      coordinateUnlinkExteriorPlanarNeckArcToRightHalf m x := by
  rw [← coordinateUnlinkExteriorPlanarNormalizedRightSeam_conjugacy m x]
  apply congrArg (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m)
  exact Prod.ext rfl (coordinateUnlinkExteriorPlanarNormalizedRightSeam_time m x).symm

/-- Realizing a normalized retained-sector circle point at time `1` recovers the actual
right-half sector. -/
theorem coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle_realize
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m
        (coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m x, 1) =
      coordinateUnlinkExteriorPlanarRightOuterSectorToRightHalf m x := by
  rw [coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle_apply]
  let y := (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m).symm
    (coordinateUnlinkExteriorPlanarRightOuterSectorToRightHalf m x)
  have hy : (y.1, 1) = y :=
    Prod.ext rfl (coordinateUnlinkExteriorPlanarNormalizedRightOuter_time m x).symm
  rw [hy]
  exact (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m).apply_symm_apply _

theorem injective_coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle m) := by
  intro x y h
  apply injective_coordinateUnlinkExteriorPlanarNormalizedRightSeam m
  exact Prod.ext h <|
    (coordinateUnlinkExteriorPlanarNormalizedRightSeam_time m x).trans
      (coordinateUnlinkExteriorPlanarNormalizedRightSeam_time m y).symm

theorem injective_coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m) := by
  intro x y h
  apply injective_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorFamily m
  have hhalf : coordinateUnlinkExteriorPlanarRightOuterSectorToRightHalf m x =
      coordinateUnlinkExteriorPlanarRightOuterSectorToRightHalf m y := by
    rw [← coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle_realize m x,
      ← coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle_realize m y, h]
  exact congrArg (fun z : CoordinateUnlinkExteriorPlanarFlowerRightHalf m ↦ z.1) hhalf

/-! ## Endpoint attachment -/

local instance productFourEndSphereDiscreteTopology :
    DiscreteTopology (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) := by
  apply DiscreteTopology.of_forall_le_dist (r := 1) zero_lt_one
  intro x y hxy
  have hxabs : |x.1 0| = 1 := by
    rw [← norm_euclideanSpace_fin_one]
    exact mem_sphere_zero_iff_norm.mp x.2
  have hyabs : |y.1 0| = 1 := by
    rw [← norm_euclideanSpace_fin_one]
    exact mem_sphere_zero_iff_norm.mp y.2
  have hcoord : x.1 0 ≠ y.1 0 := by
    intro h
    apply hxy
    apply Subtype.ext
    apply (EuclideanSpace.equiv (Fin 1) ℝ).injective
    funext i
    fin_cases i
    exact h
  rcases (abs_eq zero_le_one).mp hxabs with hx | hx <;>
    rcases (abs_eq zero_le_one).mp hyabs with hy | hy
  · exact (hcoord (hx.trans hy.symm)).elim
  · change 1 ≤ ‖x.1 - y.1‖
    rw [norm_euclideanSpace_fin_one]
    norm_num [hx, hy]
  · change 1 ≤ ‖x.1 - y.1‖
    rw [norm_euclideanSpace_fin_one]
    norm_num [hx, hy]
  · exact (hcoord (hx.trans hy.symm)).elim

/-- The common endpoints of the seam and retained-sector interval families. -/
abbrev CoordinateUnlinkExteriorPlanarRightNodeEndpoint (m : ℕ) : Type :=
  ZMod m × sphere (0 : EuclideanSpace ℝ (Fin 1)) 1

/-- Include a labelled endpoint in its retained right sector. -/
def coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarRightNodeEndpoint m,
      ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) where
  toFun x := (x.1, productFourEndUnitInterval x.2)
  continuous_toFun := continuous_fst.prodMk <|
    continuous_productFourEndUnitInterval.comp continuous_snd

/-- Include a labelled endpoint in the adjacent neck arc.  At the upper endpoint the neck
label is translated by the canonical right-sector offset. -/
def coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarRightNodeEndpoint m,
      ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) where
  toFun x :=
    (if productFourEndUnitInterval x.2 = 0 then x.1
      else x.1 + coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m,
      productFourEndUnitInterval x.2)
  continuous_toFun := continuous_of_discreteTopology

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter_apply
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarRightNodeEndpoint m) :
    coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m x =
      (x.1, productFourEndUnitInterval x.2) :=
  rfl

theorem coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam_apply_of_zero
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarRightNodeEndpoint m)
    (hx : productFourEndUnitInterval x.2 = 0) :
    coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x = (x.1, 0) := by
  simp [coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam, hx]

theorem coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam_apply_of_one
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarRightNodeEndpoint m)
    (hx : productFourEndUnitInterval x.2 = 1) :
    coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x =
      (x.1 + coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m, 1) := by
  simp [coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam, hx]

/-- The endpoint inclusions have identical images in the normalized right annulus circle. -/
theorem coordinateUnlinkExteriorPlanarRightNodeEndpoint_compatibility
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarRightNodeEndpoint m) :
    coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle m
        (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x) =
      coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m
        (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m x) := by
  have hpair :
      ((coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle m
          (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x), 1) :
        PartialSphereSpinAnnulus) =
      ((coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m
          (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m x), 1) :
        PartialSphereSpinAnnulus) := by
    apply (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m).injective
    rw [coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle_realize,
      coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle_realize]
    rcases productFourEndUnitInterval_eq_zero_or_one x.2 with hx | hx
    · rw [coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam_apply_of_zero m x hx,
        coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter_apply, hx]
      apply Subtype.ext
      exact coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_zero m x.1 |>.symm
    · rw [coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam_apply_of_one m x hx,
        coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter_apply, hx]
      apply Subtype.ext
      exact coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_one m x.1 |>.symm
  have hfst := congrArg (fun p : PartialSphereSpinAnnulus ↦ p.1) hpair
  exact hfst

theorem injective_coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m) := by
  intro x y h
  exact Prod.ext (congrArg (fun z ↦ z.1) h) <|
    injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam <|
      congrArg (fun z ↦ z.2) h

theorem injective_coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m) := by
  rintro ⟨a, e⟩ ⟨b, f⟩ h
  have hef : e = f := by
    apply injective_coordinateUnlinkExteriorPlanarLeftLeafEndpointToSeam
    exact congrArg Prod.snd h
  subst f
  have hab : a = b := by
    have hfst := congrArg Prod.fst h
    rcases productFourEndUnitInterval_eq_zero_or_one e with he | he
    · simpa [coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam, he] using hfst
    · have hadd :
          a + coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m =
            b + coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m := by
        simpa [coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam, he] using hfst
      exact add_right_cancel hadd
  exact Prod.ext hab rfl

/-! ## Exact overlap and coverage -/

/-- A cross equality between a lifted seam and a retained right sector comes from one common
labelled endpoint. -/
theorem coordinateUnlinkExteriorPlanarRightNodeBoundary_cross
    (m : ℕ) [NeZero m]
    (x y : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (hxy : coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle m x =
      coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m y) :
    ∃ e : CoordinateUnlinkExteriorPlanarRightNodeEndpoint m,
      coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m e = x ∧
        coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m e = y := by
  have hhalf : coordinateUnlinkExteriorPlanarNeckArcToRightHalf m x =
      coordinateUnlinkExteriorPlanarRightOuterSectorToRightHalf m y := by
    rw [← coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle_realize m x,
      ← coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle_realize m y, hxy]
  have hflower : coordinateUnlinkExteriorPlanarNeckArcTranslate m x.1 x.2 =
      coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m y.1 y.2 := by
    exact congrArg (fun z : CoordinateUnlinkExteriorPlanarFlowerRightHalf m ↦ z.1) hhalf
  have houter :
      ‖(coordinateUnlinkExteriorPlanarNeckArcTranslate m x.1 x.2).1.1 ^ m +
        (1 / 2 : ℂ)‖ = sphereHandleRadius := by
    rw [hflower, coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_pow,
      coordinateUnlinkExteriorPlanarBaseRightOuterArc_add_half_norm]
  rcases
      coordinateUnlinkExteriorPlanarNeckArcTranslate_parameter_eq_endpoint_of_outerNorm
        m x.1 x.2 houter with hx | hx
  · have hy : (x.1, (0 : CoordinateUnlinkExteriorPlanarNeckInterval)) = y := by
      apply injective_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorFamily m
      calc
        coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m x.1 0 =
            coordinateUnlinkExteriorPlanarNeckArcTranslate m x.1 0 :=
          coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_zero m x.1
        _ = coordinateUnlinkExteriorPlanarNeckArcTranslate m x.1 x.2 := by rw [hx]
        _ = coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m y.1 y.2 := hflower
    refine ⟨(x.1, coordinateUnlinkExteriorPlanarNeckLowerEnd), ?_, ?_⟩
    · rw [coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam_apply_of_zero m _
          productFourEndUnitInterval_neckLowerEnd]
      exact Prod.ext rfl hx.symm
    · rw [coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter_apply,
        productFourEndUnitInterval_neckLowerEnd]
      exact hy
  · let a := x.1 - coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m
    have ha : a + coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m = x.1 :=
      sub_add_cancel _ _
    have hy : (a, (1 : CoordinateUnlinkExteriorPlanarNeckInterval)) = y := by
      apply injective_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorFamily m
      calc
        coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m a 1 =
            coordinateUnlinkExteriorPlanarNeckArcTranslate m
              (a + coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m) 1 :=
          coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_one m a
        _ = coordinateUnlinkExteriorPlanarNeckArcTranslate m x.1 1 := by rw [ha]
        _ = coordinateUnlinkExteriorPlanarNeckArcTranslate m x.1 x.2 := by rw [hx]
        _ = coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m y.1 y.2 := hflower
    refine ⟨(a, coordinateUnlinkExteriorPlanarNeckUpperEnd), ?_, ?_⟩
    · rw [coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam_apply_of_one m _
          productFourEndUnitInterval_neckUpperEnd, ha]
      exact Prod.ext rfl hx.symm
    · rw [coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter_apply,
        productFourEndUnitInterval_neckUpperEnd]
      exact hy

/-- The lifted seam arcs and retained right sectors exhaust the literal outer circle of the
normalized right annulus. -/
theorem coordinateUnlinkExteriorPlanarRightNodeBoundary_cover
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle m) ∪
        range (coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m) = univ := by
  apply Set.eq_univ_of_forall
  intro u
  let w : CoordinateUnlinkExteriorPlanarFlowerRightHalf m :=
    coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m (u, 1)
  have hwEndpoint : w ∈ coordinateUnlinkExteriorPlanarFlowerRightHalfOuterEndpointSet m := by
    rw [← range_coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_one]
    exact ⟨u, rfl⟩
  rcases hwEndpoint with hwSeam | hwOuter
  · left
    have hzCommon : w.1 ∈
        coordinateUnlinkExteriorPlanarFlowerLeftHalfSet m ∩
          coordinateUnlinkExteriorPlanarFlowerRightHalfSet m := ⟨hwSeam.le, w.2⟩
    rw [← range_coordinateUnlinkExteriorPlanarNeckArcFamily m] at hzCommon
    obtain ⟨x, hx⟩ := hzCommon
    refine ⟨x, ?_⟩
    have hhalf : coordinateUnlinkExteriorPlanarNeckArcToRightHalf m x = w := by
      apply Subtype.ext
      exact hx
    have hpair :
        ((coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle m x, 1) :
          PartialSphereSpinAnnulus) = (u, 1) := by
      apply (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m).injective
      rw [coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle_realize, hhalf]
    exact congrArg (fun p : PartialSphereSpinAnnulus ↦ p.1) hpair
  · right
    have hzOuter : w.1 ∈ coordinateUnlinkExteriorPlanarRetainedOuterRightSet m :=
      ⟨hwOuter, w.2⟩
    rw [← iUnion_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet] at hzOuter
    rw [mem_iUnion] at hzOuter
    obtain ⟨a, t, ht⟩ := hzOuter
    refine ⟨(a, t), ?_⟩
    have hhalf : coordinateUnlinkExteriorPlanarRightOuterSectorToRightHalf m (a, t) = w := by
      apply Subtype.ext
      exact ht
    have hpair :
        ((coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m (a, t), 1) :
          PartialSphereSpinAnnulus) = (u, 1) := by
      apply (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m).injective
      rw [coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle_realize, hhalf]
    exact congrArg (fun p : PartialSphereSpinAnnulus ↦ p.1) hpair

/-! ## Pushout recognition and the product one-handle -/

/-- The abstract outer-boundary pushout for the normalized right node. -/
abbrev CoordinateUnlinkExteriorPlanarRightNodeBoundaryPushout (m : ℕ) [NeZero m] : Type :=
  TopologicalPushout
    (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m)
    (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m)

/-- The two labelled interval families recover the literal outer circle of the right annulus. -/
def coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarRightNodeBoundaryPushout m ≃ₜ Sphere 1 :=
  topologicalPushoutHomeomorph
    (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m)
    (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m)
    (coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle m)
    (coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m)
    (coordinateUnlinkExteriorPlanarRightNodeEndpoint_compatibility m)
    (injective_coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m)
    (injective_coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle m)
    (injective_coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m)
    (coordinateUnlinkExteriorPlanarRightNodeBoundary_cross m)
    (coordinateUnlinkExteriorPlanarRightNodeBoundary_cover m)

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m)
          (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m) x) =
      coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle m x :=
  topologicalPushoutHomeomorph_inl _ _ _ _ _ _ _ _ _ _ x

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m)
          (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m) x) =
      coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m x :=
  topologicalPushoutHomeomorph_inr _ _ _ _ _ _ _ _ _ _ x

/-- Product of the right-node boundary pushout with the literal closed three-ball. -/
abbrev CoordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushout
    (m : ℕ) [NeZero m] : Type :=
  TopologicalPushout
    ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m).prodMap
      (ContinuousMap.id (EuclideanClosedBall 3)))
    ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
      (ContinuousMap.id (EuclideanClosedBall 3)))

/-- The product right-node boundary split is exactly the compact one-handle `S¹ × B³`. -/
def coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushout m ≃ₜ OneHandlePiece := by
  let _ : T2Space (CoordinateUnlinkExteriorPlanarRightNodeBoundaryPushout m) :=
    (coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph m).symm.t2Space
  exact
    (topologicalPushoutProductHomeomorph
      (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m)
      (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m)
      (EuclideanClosedBall 3)
      (injective_coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m)
      (injective_coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m)).trans
      ((coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph m).prodCongr
        (Homeomorph.refl (EuclideanClosedBall 3)))

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph m
        (topologicalPushoutInl
          ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3))) (x, b)) =
      (coordinateUnlinkExteriorPlanarNormalizedRightSeamCircle m x, b) := by
  rw [coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph,
    Homeomorph.trans_apply, topologicalPushoutProductHomeomorph_inl]
  exact Prod.ext
    (coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph_inl m x) rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph m
        (topologicalPushoutInr
          ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          ((coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3))) (x, b)) =
      (coordinateUnlinkExteriorPlanarNormalizedRightOuterCircle m x, b) := by
  rw [coordinateUnlinkExteriorPlanarRightNodeOneHandleSplitPushoutHomeomorph,
    Homeomorph.trans_apply, topologicalPushoutProductHomeomorph_inr]
  exact Prod.ext
    (coordinateUnlinkExteriorPlanarRightNodeBoundaryPushoutHomeomorph_inr m x) rfl

end SplittingSpheres
