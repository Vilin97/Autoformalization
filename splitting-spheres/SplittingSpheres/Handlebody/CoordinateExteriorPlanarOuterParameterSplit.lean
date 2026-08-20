/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalPushoutProduct
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckPushout
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckSphere

/-!
# Splitting the retained outer parameter circle at the neck endpoints

The retained `Sphere 1` parameter of the planar flower has two natural closed carriers,
according as the real part of the polynomial coordinate is at most or at least `-1/2`.  Their
intersection is exactly the already constructed `ZMod m × S⁰` family of neck endpoints, and
the two carriers cover the circle.  This file recognizes the circle as their topological
pushout and, after taking a product with `B³`, recognizes the retained one-handle as the
corresponding product pushout.

The file also bundles the existing labelled neck three-spheres into one jointly continuous,
injective family.  It does **not** identify either closed carrier with a family of intervals,
choose an order of the complementary outer sectors, or make a cutting, separation,
connected-sum, manifold, or smoothness claim.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped Topology

namespace SplittingSpheres

/-! ## Joint endpoint and neck-sphere families -/

/-- The complete labelled family of the two endpoints of every lifted neck arc, expressed in
the retained outer-circle parameter. -/
def coordinateUnlinkExteriorPlanarNeckEndpointFamily
    (m : ℕ) [NeZero m] :
    C(ZMod m × sphere (0 : EuclideanSpace ℝ (Fin 1)) 1, Sphere 1) where
  toFun x := coordinateUnlinkExteriorPlanarNeckOuterParameter m x.1 x.2
  continuous_toFun := by
    rw [continuous_prod_of_discrete_left]
    exact fun a ↦ continuous_coordinateUnlinkExteriorPlanarNeckOuterParameter m a

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckEndpointFamily_apply
    (m : ℕ) [NeZero m]
    (x : ZMod m × sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    coordinateUnlinkExteriorPlanarNeckEndpointFamily m x =
      coordinateUnlinkExteriorPlanarNeckOuterParameter m x.1 x.2 :=
  rfl

theorem injective_coordinateUnlinkExteriorPlanarNeckEndpointFamily
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckEndpointFamily m) :=
  injective_coordinateUnlinkExteriorPlanarNeckOuterParameterFamily m

/-- The existing labelled neck `S³`s as one jointly continuous family. -/
def coordinateUnlinkExteriorPlanarNeckSphereFamily
    (m : ℕ) [NeZero m] :
    C(ZMod m × Sphere 3,
      CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) where
  toFun x := coordinateUnlinkExteriorPlanarNeckSphereMap m x.1 x.2
  continuous_toFun := by
    rw [continuous_prod_of_discrete_left]
    exact fun a ↦ (coordinateUnlinkExteriorPlanarNeckSphereMap m a).continuous

@[simp]
theorem coordinateUnlinkExteriorPlanarNeckSphereFamily_apply
    (m : ℕ) [NeZero m] (x : ZMod m × Sphere 3) :
    coordinateUnlinkExteriorPlanarNeckSphereFamily m x =
      coordinateUnlinkExteriorPlanarNeckSphereMap m x.1 x.2 :=
  rfl

theorem injective_coordinateUnlinkExteriorPlanarNeckSphereFamily
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckSphereFamily m) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  have h' : coordinateUnlinkExteriorPlanarNeckBoundaryMap m a
        (productFourBoundaryPushoutHomeomorphSphere.symm x) =
      coordinateUnlinkExteriorPlanarNeckBoundaryMap m b
        (productFourBoundaryPushoutHomeomorphSphere.symm y) := h
  obtain ⟨hab, hxy⟩ :=
    coordinateUnlinkExteriorPlanarNeckBoundaryMap_eq m a b
      (productFourBoundaryPushoutHomeomorphSphere.symm x)
      (productFourBoundaryPushoutHomeomorphSphere.symm y) h'
  exact Prod.ext hab <|
    productFourBoundaryPushoutHomeomorphSphere.symm.injective hxy

/-- The complete labelled neck-sphere family is a topological embedding. -/
theorem isEmbedding_coordinateUnlinkExteriorPlanarNeckSphereFamily
    (m : ℕ) [NeZero m] :
    IsEmbedding (coordinateUnlinkExteriorPlanarNeckSphereFamily m) := by
  let _ : T2Space (CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) :=
    (coordinateUnlinkExteriorPlanarFlowerSpinCapComplementHomeomorphSphere m).symm.t2Space
  exact (coordinateUnlinkExteriorPlanarNeckSphereFamily m).continuous.isClosedEmbedding
    (injective_coordinateUnlinkExteriorPlanarNeckSphereFamily m) |>.isEmbedding

/-! ## The two closed carriers in the outer parameter circle -/

/-- Retained outer parameters whose polynomial coordinate lies in the closed left half. -/
def coordinateUnlinkExteriorPlanarOuterParameterLeftCarrier
    (m : ℕ) [NeZero m] : Set (Sphere 1) :=
  {u | ((coordinateUnlinkExteriorPlanarFlowerOuter m u).1.1 ^ m).re ≤ -1 / 2}

/-- Retained outer parameters whose polynomial coordinate lies in the closed right half. -/
def coordinateUnlinkExteriorPlanarOuterParameterRightCarrier
    (m : ℕ) [NeZero m] : Set (Sphere 1) :=
  {u | -1 / 2 ≤ ((coordinateUnlinkExteriorPlanarFlowerOuter m u).1.1 ^ m).re}

@[simp]
theorem mem_coordinateUnlinkExteriorPlanarOuterParameterLeftCarrier
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    u ∈ coordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m ↔
      ((coordinateUnlinkExteriorPlanarFlowerOuter m u).1.1 ^ m).re ≤ -1 / 2 :=
  Iff.rfl

@[simp]
theorem mem_coordinateUnlinkExteriorPlanarOuterParameterRightCarrier
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    u ∈ coordinateUnlinkExteriorPlanarOuterParameterRightCarrier m ↔
      -1 / 2 ≤ ((coordinateUnlinkExteriorPlanarFlowerOuter m u).1.1 ^ m).re :=
  Iff.rfl

theorem continuous_coordinateUnlinkExteriorPlanarFlowerOuterPowerReal
    (m : ℕ) [NeZero m] :
    Continuous (fun u : Sphere 1 ↦
      ((coordinateUnlinkExteriorPlanarFlowerOuter m u).1.1 ^ m).re) := by
  have hval : Continuous (fun u : Sphere 1 ↦
      (coordinateUnlinkExteriorPlanarFlowerOuter m u).1.1) :=
    continuous_subtype_val.comp <|
      continuous_subtype_val.comp
        (coordinateUnlinkExteriorPlanarFlowerOuter m).continuous
  exact Complex.continuous_re.comp (hval.pow m)

theorem isClosed_coordinateUnlinkExteriorPlanarOuterParameterLeftCarrier
    (m : ℕ) [NeZero m] :
    IsClosed (coordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m) :=
  isClosed_le
    (continuous_coordinateUnlinkExteriorPlanarFlowerOuterPowerReal m)
    continuous_const

theorem isClosed_coordinateUnlinkExteriorPlanarOuterParameterRightCarrier
    (m : ℕ) [NeZero m] :
    IsClosed (coordinateUnlinkExteriorPlanarOuterParameterRightCarrier m) :=
  isClosed_le continuous_const
    (continuous_coordinateUnlinkExteriorPlanarFlowerOuterPowerReal m)

/-- The two closed polynomial-half carriers cover the retained outer parameter circle. -/
theorem coordinateUnlinkExteriorPlanarOuterParameterCarrier_cover
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m ∪
        coordinateUnlinkExteriorPlanarOuterParameterRightCarrier m = univ := by
  apply Set.eq_univ_of_forall
  intro u
  exact le_total ((coordinateUnlinkExteriorPlanarFlowerOuter m u).1.1 ^ m).re
    (-1 / 2) |>.elim Or.inl Or.inr

/-! ## Exact endpoint intersection -/

theorem coordinateUnlinkExteriorPlanarFlowerOuter_outerNorm
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    ‖(coordinateUnlinkExteriorPlanarFlowerOuter m u).1.1 ^ m + (1 / 2 : ℂ)‖ =
      sphereHandleRadius := by
  rw [coordinateUnlinkExteriorPlanarFlowerOuter_val,
    ← coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph_coe]
  exact (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m u).2

/-- The `S⁰` point corresponding to interval parameter `0`. -/
def coordinateUnlinkExteriorPlanarNeckLowerEnd :
    sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
  let d := unitIntervalToEuclideanClosedBallOne 0
  refine ⟨d.1, ?_⟩
  rw [mem_sphere_zero_iff_norm, norm_euclideanSpace_fin_one]
  change |2 * (0 : ℝ) - 1| = 1
  norm_num

/-- The `S⁰` point corresponding to interval parameter `1`. -/
def coordinateUnlinkExteriorPlanarNeckUpperEnd :
    sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
  let d := unitIntervalToEuclideanClosedBallOne 1
  refine ⟨d.1, ?_⟩
  rw [mem_sphere_zero_iff_norm, norm_euclideanSpace_fin_one]
  change |2 * (1 : ℝ) - 1| = 1
  norm_num

@[simp]
theorem productFourEndUnitInterval_neckLowerEnd :
    productFourEndUnitInterval coordinateUnlinkExteriorPlanarNeckLowerEnd = 0 := by
  apply Subtype.ext
  norm_num [coordinateUnlinkExteriorPlanarNeckLowerEnd,
    productFourEndUnitInterval, euclideanClosedBallOneToUnitInterval]

@[simp]
theorem productFourEndUnitInterval_neckUpperEnd :
    productFourEndUnitInterval coordinateUnlinkExteriorPlanarNeckUpperEnd = 1 := by
  apply Subtype.ext
  norm_num [coordinateUnlinkExteriorPlanarNeckUpperEnd,
    productFourEndUnitInterval, euclideanClosedBallOneToUnitInterval]

/-- A lifted neck point lying on the polynomial outer boundary is one of the two interval
endpoints. -/
theorem coordinateUnlinkExteriorPlanarNeckArcTranslate_parameter_eq_endpoint_of_outerNorm
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval)
    (houter : ‖(coordinateUnlinkExteriorPlanarNeckArcTranslate m a t).1.1 ^ m +
      (1 / 2 : ℂ)‖ = sphereHandleRadius) :
    t = 0 ∨ t = 1 := by
  by_cases h0 : t = 0
  · exact Or.inl h0
  by_cases h1 : t = 1
  · exact Or.inr h1
  exfalso
  have h0r : (t : ℝ) ≠ 0 := fun h ↦ h0 (Subtype.ext h)
  have h1r : (t : ℝ) ≠ 1 := fun h ↦ h1 (Subtype.ext h)
  have ht : (t : ℝ) ∈ Ioo 0 1 :=
    ⟨lt_of_le_of_ne t.2.1 h0r.symm, lt_of_le_of_ne t.2.2 h1r⟩
  have hnorm :=
    coordinateUnlinkExteriorPlanarNeckArcTranslate_outer_norm m a t
  rw [hnorm] at houter
  have habs : |2 * (t : ℝ) - 1| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hstrict := mul_lt_mul_of_pos_left habs sphereHandleRadius_pos
  linarith

/-- The two closed carriers meet at exactly the complete `ZMod m × S⁰` family of neck
endpoints. -/
theorem range_coordinateUnlinkExteriorPlanarNeckEndpointFamily
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarNeckEndpointFamily m) =
      coordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m ∩
        coordinateUnlinkExteriorPlanarOuterParameterRightCarrier m := by
  ext u
  constructor
  · rintro ⟨⟨a, e⟩, rfl⟩
    constructor
    · change ((coordinateUnlinkExteriorPlanarFlowerOuter m
          (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e)).1.1 ^ m).re ≤
        -1 / 2
      rw [coordinateUnlinkExteriorPlanarFlowerOuter_neckOuterParameter,
        coordinateUnlinkExteriorPlanarNeckArcTranslate_pow,
        coordinateUnlinkExteriorPlanarNeckBaseArc_re]
    · change -1 / 2 ≤ ((coordinateUnlinkExteriorPlanarFlowerOuter m
          (coordinateUnlinkExteriorPlanarNeckOuterParameter m a e)).1.1 ^ m).re
      rw [coordinateUnlinkExteriorPlanarFlowerOuter_neckOuterParameter,
        coordinateUnlinkExteriorPlanarNeckArcTranslate_pow,
        coordinateUnlinkExteriorPlanarNeckBaseArc_re]
  · intro hu
    have hre : ((coordinateUnlinkExteriorPlanarFlowerOuter m u).1.1 ^ m).re = -1 / 2 :=
      le_antisymm hu.1 hu.2
    have hcommon : coordinateUnlinkExteriorPlanarFlowerOuter m u ∈
        coordinateUnlinkExteriorPlanarFlowerLeftHalfSet m ∩
          coordinateUnlinkExteriorPlanarFlowerRightHalfSet m := ⟨hre.le, hre.ge⟩
    rw [← range_coordinateUnlinkExteriorPlanarNeckArcFamily m] at hcommon
    obtain ⟨⟨a, t⟩, hat⟩ := hcommon
    change coordinateUnlinkExteriorPlanarNeckArcTranslate m a t =
      coordinateUnlinkExteriorPlanarFlowerOuter m u at hat
    have houter :
        ‖(coordinateUnlinkExteriorPlanarNeckArcTranslate m a t).1.1 ^ m +
          (1 / 2 : ℂ)‖ = sphereHandleRadius := by
      rw [hat]
      exact coordinateUnlinkExteriorPlanarFlowerOuter_outerNorm m u
    rcases
        coordinateUnlinkExteriorPlanarNeckArcTranslate_parameter_eq_endpoint_of_outerNorm
          m a t houter with h0 | h1
    · refine ⟨(a, coordinateUnlinkExteriorPlanarNeckLowerEnd), ?_⟩
      change coordinateUnlinkExteriorPlanarNeckOuterParameter m a
        coordinateUnlinkExteriorPlanarNeckLowerEnd = u
      apply injective_coordinateUnlinkExteriorPlanarFlowerOuter m
      rw [coordinateUnlinkExteriorPlanarFlowerOuter_neckOuterParameter,
        productFourEndUnitInterval_neckLowerEnd, ← h0]
      exact hat
    · refine ⟨(a, coordinateUnlinkExteriorPlanarNeckUpperEnd), ?_⟩
      change coordinateUnlinkExteriorPlanarNeckOuterParameter m a
        coordinateUnlinkExteriorPlanarNeckUpperEnd = u
      apply injective_coordinateUnlinkExteriorPlanarFlowerOuter m
      rw [coordinateUnlinkExteriorPlanarFlowerOuter_neckOuterParameter,
        productFourEndUnitInterval_neckUpperEnd, ← h1]
      exact hat

/-! ## Pushout recognition of the retained outer circle -/

abbrev CoordinateUnlinkExteriorPlanarOuterParameterLeftCarrier
    (m : ℕ) [NeZero m] : Type :=
  ↑(coordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m)

abbrev CoordinateUnlinkExteriorPlanarOuterParameterRightCarrier
    (m : ℕ) [NeZero m] : Type :=
  ↑(coordinateUnlinkExteriorPlanarOuterParameterRightCarrier m)

noncomputable instance compactSpace_coordinateUnlinkExteriorPlanarOuterParameterLeftCarrier
    (m : ℕ) [NeZero m] :
    CompactSpace (CoordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m) :=
  isCompact_iff_compactSpace.mp
    (isClosed_coordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m).isCompact

noncomputable instance compactSpace_coordinateUnlinkExteriorPlanarOuterParameterRightCarrier
    (m : ℕ) [NeZero m] :
    CompactSpace (CoordinateUnlinkExteriorPlanarOuterParameterRightCarrier m) :=
  isCompact_iff_compactSpace.mp
    (isClosed_coordinateUnlinkExteriorPlanarOuterParameterRightCarrier m).isCompact

/-- Regard every labelled neck endpoint as a point of the closed left carrier. -/
def coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter
    (m : ℕ) [NeZero m] :
    C(ZMod m × sphere (0 : EuclideanSpace ℝ (Fin 1)) 1,
      CoordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m) where
  toFun x := ⟨coordinateUnlinkExteriorPlanarNeckEndpointFamily m x, by
    have hx : coordinateUnlinkExteriorPlanarNeckEndpointFamily m x ∈
        range (coordinateUnlinkExteriorPlanarNeckEndpointFamily m) := ⟨x, rfl⟩
    rw [range_coordinateUnlinkExteriorPlanarNeckEndpointFamily m] at hx
    exact hx.1⟩
  continuous_toFun :=
    (coordinateUnlinkExteriorPlanarNeckEndpointFamily m).continuous.subtype_mk _

/-- Regard every labelled neck endpoint as a point of the closed right carrier. -/
def coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter
    (m : ℕ) [NeZero m] :
    C(ZMod m × sphere (0 : EuclideanSpace ℝ (Fin 1)) 1,
      CoordinateUnlinkExteriorPlanarOuterParameterRightCarrier m) where
  toFun x := ⟨coordinateUnlinkExteriorPlanarNeckEndpointFamily m x, by
    have hx : coordinateUnlinkExteriorPlanarNeckEndpointFamily m x ∈
        range (coordinateUnlinkExteriorPlanarNeckEndpointFamily m) := ⟨x, rfl⟩
    rw [range_coordinateUnlinkExteriorPlanarNeckEndpointFamily m] at hx
    exact hx.2⟩
  continuous_toFun :=
    (coordinateUnlinkExteriorPlanarNeckEndpointFamily m).continuous.subtype_mk _

/-- Include the closed left carrier in the retained outer parameter circle. -/
def coordinateUnlinkExteriorPlanarOuterParameterLeftInclusion
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m, Sphere 1) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Include the closed right carrier in the retained outer parameter circle. -/
def coordinateUnlinkExteriorPlanarOuterParameterRightInclusion
    (m : ℕ) [NeZero m] :
    C(CoordinateUnlinkExteriorPlanarOuterParameterRightCarrier m, Sphere 1) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem coordinateUnlinkExteriorPlanarOuterParameterSplit_compatibility
    (m : ℕ) [NeZero m]
    (x : ZMod m × sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    coordinateUnlinkExteriorPlanarOuterParameterLeftInclusion m
        (coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m x) =
      coordinateUnlinkExteriorPlanarOuterParameterRightInclusion m
        (coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m x) :=
  rfl

theorem injective_coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m) := by
  intro x y h
  exact injective_coordinateUnlinkExteriorPlanarNeckEndpointFamily m
    (congrArg Subtype.val h)

theorem injective_coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m) := by
  intro x y h
  exact injective_coordinateUnlinkExteriorPlanarNeckEndpointFamily m
    (congrArg Subtype.val h)

theorem coordinateUnlinkExteriorPlanarOuterParameterSplit_cross
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m)
    (y : CoordinateUnlinkExteriorPlanarOuterParameterRightCarrier m)
    (hxy : coordinateUnlinkExteriorPlanarOuterParameterLeftInclusion m x =
      coordinateUnlinkExteriorPlanarOuterParameterRightInclusion m y) :
    ∃ a,
      coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m a = x ∧
        coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m a = y := by
  have hx : x.1 ∈ coordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m ∩
      coordinateUnlinkExteriorPlanarOuterParameterRightCarrier m :=
    ⟨x.2, by
      change x.1 = y.1 at hxy
      exact hxy.symm ▸ y.2⟩
  rw [← range_coordinateUnlinkExteriorPlanarNeckEndpointFamily m] at hx
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, Subtype.ext ha, Subtype.ext (ha.trans hxy)⟩

theorem coordinateUnlinkExteriorPlanarOuterParameterSplit_subtype_cover
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarOuterParameterLeftInclusion m) ∪
        range (coordinateUnlinkExteriorPlanarOuterParameterRightInclusion m) = univ := by
  ext u
  constructor
  · exact fun _ ↦ mem_univ u
  · intro _
    have hu : u ∈ coordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m ∪
        coordinateUnlinkExteriorPlanarOuterParameterRightCarrier m := by
      rw [coordinateUnlinkExteriorPlanarOuterParameterCarrier_cover m]
      exact mem_univ u
    rcases hu with hu | hu
    · exact Or.inl ⟨⟨u, hu⟩, rfl⟩
    · exact Or.inr ⟨⟨u, hu⟩, rfl⟩

/-- The retained outer circle is exactly the pushout of its two closed polynomial-half
carriers along the complete labelled endpoint family. -/
abbrev CoordinateUnlinkExteriorPlanarOuterParameterSplitPushout
    (m : ℕ) [NeZero m] : Type :=
  TopologicalPushout
    (coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m)
    (coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m)

/-- Concrete pushout recognition of the retained outer parameter circle. -/
def coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarOuterParameterSplitPushout m ≃ₜ Sphere 1 :=
  topologicalPushoutHomeomorph
    (coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m)
    (coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m)
    (coordinateUnlinkExteriorPlanarOuterParameterLeftInclusion m)
    (coordinateUnlinkExteriorPlanarOuterParameterRightInclusion m)
    (coordinateUnlinkExteriorPlanarOuterParameterSplit_compatibility m)
    (injective_coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m)
    (fun _ _ h ↦ Subtype.ext h)
    (fun _ _ h ↦ Subtype.ext h)
    (coordinateUnlinkExteriorPlanarOuterParameterSplit_cross m)
    (coordinateUnlinkExteriorPlanarOuterParameterSplit_subtype_cover m)

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m) :
    coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph m
        (topologicalPushoutInl
          (coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m)
          (coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m) x) = x.1 :=
  topologicalPushoutHomeomorph_inl _ _ _ _ _ _ _ _ _ _ x

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarOuterParameterRightCarrier m) :
    coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph m
        (topologicalPushoutInr
          (coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m)
          (coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m) x) = x.1 :=
  topologicalPushoutHomeomorph_inr _ _ _ _ _ _ _ _ _ _ x

/-! ## Product split of the retained one-handle -/

/-- Cross the two endpoint inclusions with the literal closed three-ball. -/
abbrev CoordinateUnlinkExteriorPlanarOuterParameterOneHandleSplitPushout
    (m : ℕ) [NeZero m] : Type :=
  TopologicalPushout
    ((coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m).prodMap
      (ContinuousMap.id (EuclideanClosedBall 3)))
    ((coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m).prodMap
      (ContinuousMap.id (EuclideanClosedBall 3)))

/-- The retained one-handle `S¹ × B³` is exactly the product pushout of the two closed
outer-parameter carriers times `B³`. -/
def coordinateUnlinkExteriorPlanarOuterParameterOneHandleSplitHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarOuterParameterOneHandleSplitPushout m ≃ₜ
      OneHandlePiece := by
  let _ : T2Space (CoordinateUnlinkExteriorPlanarOuterParameterSplitPushout m) :=
    (coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph m).symm.t2Space
  exact
    (topologicalPushoutProductHomeomorph
      (coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m)
      (coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m)
      (EuclideanClosedBall 3)
      (injective_coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m)
      (injective_coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m)).trans
      ((coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph m).prodCongr
        (Homeomorph.refl (EuclideanClosedBall 3)))

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterParameterOneHandleSplitHomeomorph_inl
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarOuterParameterOneHandleSplitHomeomorph m
        (topologicalPushoutInl
          ((coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          ((coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3))) (x, b)) =
      (x.1, b) := by
  rw [coordinateUnlinkExteriorPlanarOuterParameterOneHandleSplitHomeomorph,
    Homeomorph.trans_apply, topologicalPushoutProductHomeomorph_inl]
  exact Prod.ext
    (coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph_inl m x) rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarOuterParameterOneHandleSplitHomeomorph_inr
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarOuterParameterRightCarrier m)
    (b : EuclideanClosedBall 3) :
    coordinateUnlinkExteriorPlanarOuterParameterOneHandleSplitHomeomorph m
        (topologicalPushoutInr
          ((coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3)))
          ((coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m).prodMap
            (ContinuousMap.id (EuclideanClosedBall 3))) (x, b)) =
      (x.1, b) := by
  rw [coordinateUnlinkExteriorPlanarOuterParameterOneHandleSplitHomeomorph,
    Homeomorph.trans_apply, topologicalPushoutProductHomeomorph_inr]
  exact Prod.ext
    (coordinateUnlinkExteriorPlanarOuterParameterSplitPushoutHomeomorph_inr m x) rfl

end SplittingSpheres
