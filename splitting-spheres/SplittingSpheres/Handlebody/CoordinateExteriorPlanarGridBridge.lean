/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarRightNodeBoundary

/-!
# Coordinate bridges for the planar neck pushout grid

The retained right sectors are labelled by their lower endpoints.  Their upper endpoints meet
neck arcs whose labels differ by the canonical, deliberately unevaluated endpoint offset.  This
file first packages that endpoint relabelling as a homeomorphism.  It then identifies the
explicit labelled left and right outer sectors with the literal closed carrier subtypes used by
the retained-circle pushout.

Only point-set topology is asserted.  In particular, the endpoint offset is not identified with
`1`, and no cyclic orientation or order is chosen.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-! ## Relabelling right-sector endpoints by their incident neck arcs -/

/-- Undo the right-sector-to-neck relabelling at an endpoint.  At the lower endpoint the label
is unchanged; at the upper endpoint the canonical offset is subtracted. -/
def coordinateUnlinkExteriorPlanarRightNodeEndpointUnrelabel
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarRightNodeEndpoint m) :
    CoordinateUnlinkExteriorPlanarRightNodeEndpoint m :=
  (if productFourEndUnitInterval x.2 = 0 then x.1
    else x.1 - coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m, x.2)

/-- Relabel each retained-right-sector endpoint by the neck arc incident to it, as an
equivalence of underlying types. -/
def coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelEquiv
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarRightNodeEndpoint m ≃
      CoordinateUnlinkExteriorPlanarRightNodeEndpoint m where
  toFun x :=
    ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x).1, x.2)
  invFun := coordinateUnlinkExteriorPlanarRightNodeEndpointUnrelabel m
  left_inv x := by
    rcases productFourEndUnitInterval_eq_zero_or_one x.2 with hx | hx
    · apply Prod.ext
      · simp [coordinateUnlinkExteriorPlanarRightNodeEndpointUnrelabel,
          coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam, hx]
      · rfl
    · apply Prod.ext
      · simp [coordinateUnlinkExteriorPlanarRightNodeEndpointUnrelabel,
          coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam, hx]
      · rfl
  right_inv x := by
    rcases productFourEndUnitInterval_eq_zero_or_one x.2 with hx | hx
    · apply Prod.ext
      · simp [coordinateUnlinkExteriorPlanarRightNodeEndpointUnrelabel,
          coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam, hx]
      · rfl
    · apply Prod.ext
      · simp [coordinateUnlinkExteriorPlanarRightNodeEndpointUnrelabel,
          coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam, hx]
      · rfl

/-- Relabel each retained-right-sector endpoint by the neck arc incident to it.

Thus the lower endpoint keeps label `a`, while the upper endpoint receives label `a + c`, where
`c` is the canonical endpoint offset. -/
def coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph
    (m : ℕ) [NeZero m] :
    CoordinateUnlinkExteriorPlanarRightNodeEndpoint m ≃ₜ
      CoordinateUnlinkExteriorPlanarRightNodeEndpoint m :=
  Continuous.homeoOfEquivCompactToT2
    (f := coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelEquiv m) <|
      ((continuous_fst.comp
        (coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m).continuous).prodMk
          continuous_snd)

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph_apply
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarRightNodeEndpoint m) :
    coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m x =
      ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x).1, x.2) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph_symm_apply
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarRightNodeEndpoint m) :
    (coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m).symm x =
      (if productFourEndUnitInterval x.2 = 0 then x.1
        else x.1 - coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m, x.2) :=
  rfl

/-! ## Explicit left-sector parameters in the retained circle -/

/-- The retained outer-circle parameter corresponding to a labelled left flower sector. -/
def coordinateUnlinkExteriorPlanarLeftOuterSectorParameter
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftOuterArc) : Sphere 1 :=
  (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m).symm
    ⟨(coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap m x.1 x.2).1.1, by
      change ‖(coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap m x.1 x.2).1.1 ^ m +
        (1 / 2 : ℂ)‖ = sphereHandleRadius
      rw [coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap_pow]
      exact x.2.2⟩

/-- The explicit left parameter maps back to the chosen labelled flower sector. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerOuter_leftOuterSectorParameter
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftOuterArc) :
    coordinateUnlinkExteriorPlanarFlowerOuter m
        (coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m x) =
      coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap m x.1 x.2 := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coordinateUnlinkExteriorPlanarFlowerOuter_val]
  rw [← coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph_coe]
  unfold coordinateUnlinkExteriorPlanarLeftOuterSectorParameter
  rw [(coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m).apply_symm_apply]

theorem continuous_coordinateUnlinkExteriorPlanarLeftOuterSectorParameter
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m) := by
  unfold coordinateUnlinkExteriorPlanarLeftOuterSectorParameter
  apply (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m).symm.continuous.comp
  apply Continuous.subtype_mk
  apply continuous_subtype_val.comp
  apply continuous_subtype_val.comp
  rw [continuous_prod_of_discrete_left]
  exact fun a ↦ (coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap m a).continuous

/-- The complete labelled left-sector parameterization is injective. -/
theorem injective_coordinateUnlinkExteriorPlanarLeftOuterSectorParameter
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m) := by
  intro x y hxy
  have hflower := congrArg (coordinateUnlinkExteriorPlanarFlowerOuter m) hxy
  rw [coordinateUnlinkExteriorPlanarFlowerOuter_leftOuterSectorParameter,
    coordinateUnlinkExteriorPlanarFlowerOuter_leftOuterSectorParameter] at hflower
  have hleft :
      coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m (x.1, x.2.1) =
        coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m (y.1, y.2.1) := by
    apply Subtype.ext
    exact hflower
  have hp := (coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization m).injective hleft
  have hfst : x.1 = y.1 :=
    congrArg (fun z : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftHalf ↦ z.1) hp
  have hsnd : x.2.1 = y.2.1 :=
    congrArg (fun z : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftHalf ↦ z.2) hp
  exact Prod.ext hfst (Subtype.ext hsnd)

/-- Bundle every labelled left-sector parameter in the literal closed left carrier. -/
def coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierMap
    (m : ℕ) [NeZero m] :
    C(ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftOuterArc,
      CoordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m) where
  toFun x := ⟨coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m x, by
    change ((coordinateUnlinkExteriorPlanarFlowerOuter m
      (coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m x)).1.1 ^ m).re ≤ -1 / 2
    rw [coordinateUnlinkExteriorPlanarFlowerOuter_leftOuterSectorParameter,
      coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap_pow]
    exact (mem_coordinateUnlinkExteriorPlanarBaseLeftHalfSet_iff x.2.1.1).mp
      x.2.1.2 |>.2.2.2⟩
  continuous_toFun :=
    (continuous_coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m).subtype_mk _

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierMap_coe
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftOuterArc) :
    (coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierMap m x : Sphere 1) =
      coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m x :=
  rfl

theorem injective_coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierMap
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierMap m) := by
  intro x y hxy
  apply injective_coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m
  exact congrArg Subtype.val hxy

theorem surjective_coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierMap
    (m : ℕ) [NeZero m] :
    Surjective (coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierMap m) := by
  intro u
  let z := coordinateUnlinkExteriorPlanarFlowerOuter m u.1
  have hzouter : z ∈ coordinateUnlinkExteriorPlanarRetainedOuterSet m := by
    rw [← range_coordinateUnlinkExteriorPlanarFlowerOuter m]
    exact ⟨u.1, rfl⟩
  have hzleft : z ∈ coordinateUnlinkExteriorPlanarFlowerLeftHalfSet m := by
    exact u.2
  have hz : z ∈ coordinateUnlinkExteriorPlanarRetainedOuterLeftSet m :=
    ⟨hzouter, hzleft⟩
  rw [← iUnion_coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorSet m] at hz
  rw [mem_iUnion] at hz
  obtain ⟨a, w, hw⟩ := hz
  refine ⟨(a, w), ?_⟩
  apply Subtype.ext
  apply injective_coordinateUnlinkExteriorPlanarFlowerOuter m
  rw [coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierMap_coe,
    coordinateUnlinkExteriorPlanarFlowerOuter_leftOuterSectorParameter]
  exact hw

/-- The labelled left sectors are exactly the literal closed left outer-parameter carrier. -/
def coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierHomeomorph
    (m : ℕ) [NeZero m] :
    (ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftOuterArc) ≃ₜ
      CoordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective
      (coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierMap m)
      ⟨injective_coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierMap m,
        surjective_coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierMap m⟩)
    (coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierMap m).continuous

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierHomeomorph_apply_coe
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarBaseLeftOuterArc) :
    (coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierHomeomorph m x : Sphere 1) =
      coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m x :=
  rfl

theorem coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierHomeomorph_symm_spec
    (m : ℕ) [NeZero m]
    (u : CoordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m) :
    coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m
        ((coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierHomeomorph m).symm u) =
      u.1 := by
  exact congrArg Subtype.val <|
    (coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierHomeomorph m).apply_symm_apply u

/-- Exact range of the unbundled labelled left-sector parameterization. -/
theorem range_coordinateUnlinkExteriorPlanarLeftOuterSectorParameter
    (m : ℕ) [NeZero m] :
    range (coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m) =
      coordinateUnlinkExteriorPlanarOuterParameterLeftCarrier m := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    exact (coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierMap m x).2
  · intro hu
    obtain ⟨x, hx⟩ := surjective_coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierMap m
      ⟨u, hu⟩
    exact ⟨x, congrArg Subtype.val hx⟩

/-! ## The right-sector carrier -/

/-- Bundle every labelled right-sector parameter in the literal closed right carrier. -/
def coordinateUnlinkExteriorPlanarRightOuterSectorCarrierMap
    (m : ℕ) [NeZero m] :
    C(ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval,
      CoordinateUnlinkExteriorPlanarOuterParameterRightCarrier m) where
  toFun x := ⟨coordinateUnlinkExteriorPlanarRightOuterSectorParameter m x.1 x.2, by
    change -1 / 2 ≤ ((coordinateUnlinkExteriorPlanarFlowerOuter m
      (coordinateUnlinkExteriorPlanarRightOuterSectorParameter m x.1 x.2)).1.1 ^ m).re
    rw [coordinateUnlinkExteriorPlanarFlowerOuter_rightOuterSectorParameter,
      coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_pow]
    exact coordinateUnlinkExteriorPlanarBaseRightOuterArc_re_ge x.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_prod_of_discrete_left]
    exact fun a ↦ continuous_coordinateUnlinkExteriorPlanarRightOuterSectorParameter m a

@[simp]
theorem coordinateUnlinkExteriorPlanarRightOuterSectorCarrierMap_coe
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarRightOuterSectorCarrierMap m x : Sphere 1) =
      coordinateUnlinkExteriorPlanarRightOuterSectorParameter m x.1 x.2 :=
  rfl

theorem injective_coordinateUnlinkExteriorPlanarRightOuterSectorCarrierMap
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarRightOuterSectorCarrierMap m) := by
  intro x y hxy
  exact injective_coordinateUnlinkExteriorPlanarRightOuterSectorParameterFamily m <|
    congrArg Subtype.val hxy

theorem surjective_coordinateUnlinkExteriorPlanarRightOuterSectorCarrierMap
    (m : ℕ) [NeZero m] :
    Surjective (coordinateUnlinkExteriorPlanarRightOuterSectorCarrierMap m) := by
  intro u
  have hu : u.1 ∈ coordinateUnlinkExteriorPlanarRetainedOuterParameterRightSet m := u.2
  rw [← iUnion_coordinateUnlinkExteriorPlanarRightOuterParameterSectorSet m] at hu
  rw [mem_iUnion] at hu
  obtain ⟨a, t, ht⟩ := hu
  exact ⟨(a, t), Subtype.ext ht⟩

/-- The labelled right sectors are exactly the literal closed right outer-parameter carrier. -/
def coordinateUnlinkExteriorPlanarRightOuterSectorCarrierHomeomorph
    (m : ℕ) [NeZero m] :
    (ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) ≃ₜ
      CoordinateUnlinkExteriorPlanarOuterParameterRightCarrier m :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective
      (coordinateUnlinkExteriorPlanarRightOuterSectorCarrierMap m)
      ⟨injective_coordinateUnlinkExteriorPlanarRightOuterSectorCarrierMap m,
        surjective_coordinateUnlinkExteriorPlanarRightOuterSectorCarrierMap m⟩)
    (coordinateUnlinkExteriorPlanarRightOuterSectorCarrierMap m).continuous

@[simp]
theorem coordinateUnlinkExteriorPlanarRightOuterSectorCarrierHomeomorph_apply_coe
    (m : ℕ) [NeZero m]
    (x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarRightOuterSectorCarrierHomeomorph m x : Sphere 1) =
      coordinateUnlinkExteriorPlanarRightOuterSectorParameter m x.1 x.2 :=
  rfl

theorem coordinateUnlinkExteriorPlanarRightOuterSectorCarrierHomeomorph_symm_spec
    (m : ℕ) [NeZero m]
    (u : CoordinateUnlinkExteriorPlanarOuterParameterRightCarrier m) :
    coordinateUnlinkExteriorPlanarRightOuterSectorParameter m
        ((coordinateUnlinkExteriorPlanarRightOuterSectorCarrierHomeomorph m).symm u).1
        ((coordinateUnlinkExteriorPlanarRightOuterSectorCarrierHomeomorph m).symm u).2 =
      u.1 := by
  exact congrArg Subtype.val <|
    (coordinateUnlinkExteriorPlanarRightOuterSectorCarrierHomeomorph m).apply_symm_apply u

/-- Exact range of the unbundled labelled right-sector parameterization. -/
theorem range_coordinateUnlinkExteriorPlanarRightOuterSectorParameter
    (m : ℕ) [NeZero m] :
    range (fun x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval ↦
      coordinateUnlinkExteriorPlanarRightOuterSectorParameter m x.1 x.2) =
        coordinateUnlinkExteriorPlanarOuterParameterRightCarrier m := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    exact (coordinateUnlinkExteriorPlanarRightOuterSectorCarrierMap m x).2
  · intro hu
    obtain ⟨x, hx⟩ := surjective_coordinateUnlinkExteriorPlanarRightOuterSectorCarrierMap m
      ⟨u, hu⟩
    exact ⟨x, congrArg Subtype.val hx⟩

/-! ## Compatibility at the common endpoint family -/

/-- A labelled left outer-sector endpoint is the retained-circle parameter of the same labelled
neck endpoint. -/
theorem coordinateUnlinkExteriorPlanarLeftOuterSectorParameter_endpoint
    (m : ℕ) [NeZero m] (a : ZMod m)
    (e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m
        (a, coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc e) =
      coordinateUnlinkExteriorPlanarNeckOuterParameter m a e := by
  apply injective_coordinateUnlinkExteriorPlanarFlowerOuter m
  rw [coordinateUnlinkExteriorPlanarFlowerOuter_leftOuterSectorParameter,
    coordinateUnlinkExteriorPlanarFlowerOuter_neckOuterParameter]
  rcases productFourEndUnitInterval_eq_zero_or_one e with he | he
  · have hw : coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc e =
        coordinateUnlinkExteriorPlanarBaseLeftOuterArcLower := by
      apply Subtype.ext
      rw [coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc_apply, he]
      rfl
    rw [hw, coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap_lower, he]
  · have hw : coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc e =
        coordinateUnlinkExteriorPlanarBaseLeftOuterArcUpper := by
      apply Subtype.ext
      rw [coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc_apply, he]
      rfl
    rw [hw, coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorMap_upper, he]

/-- The explicit left-sector carrier homeomorphism agrees at every corner with the physical
neck-endpoint inclusion after relabelling the corner by its incident neck. -/
theorem coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierHomeomorph_endpoint
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarRightNodeEndpoint m) :
    coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierHomeomorph m
        ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x).1,
          coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc x.2) =
      coordinateUnlinkExteriorPlanarNeckEndpointToLeftOuterParameter m
        (coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m x) := by
  apply Subtype.ext
  rw [coordinateUnlinkExteriorPlanarLeftOuterSectorCarrierHomeomorph_apply_coe]
  change coordinateUnlinkExteriorPlanarLeftOuterSectorParameter m
      ((coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam m x).1,
        coordinateUnlinkExteriorPlanarLeftLeafEndpointToOuterArc x.2) =
    coordinateUnlinkExteriorPlanarNeckOuterParameter m
      (coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m x).1
      (coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m x).2
  rw [coordinateUnlinkExteriorPlanarLeftOuterSectorParameter_endpoint,
    coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph_apply]

/-- A retained right-sector endpoint has the physical neck label supplied by the endpoint
relabelling homeomorphism. -/
theorem coordinateUnlinkExteriorPlanarRightOuterSectorParameter_endpoint
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarRightNodeEndpoint m) :
    coordinateUnlinkExteriorPlanarRightOuterSectorParameter m
        (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m x).1
        (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m x).2 =
      coordinateUnlinkExteriorPlanarNeckOuterParameter m
        (coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m x).1
        (coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m x).2 := by
  rcases productFourEndUnitInterval_eq_zero_or_one x.2 with hx | hx
  · rw [coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter_apply, hx,
      coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph_apply,
      coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam_apply_of_zero m x hx]
    exact coordinateUnlinkExteriorPlanarRightOuterSectorParameter_zero m x.1 x.2 hx
  · rw [coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter_apply, hx,
      coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph_apply,
      coordinateUnlinkExteriorPlanarRightNodeEndpointToSeam_apply_of_one m x hx]
    exact coordinateUnlinkExteriorPlanarRightOuterSectorParameter_one m x.1 x.2 hx

/-- The explicit right-sector carrier homeomorphism agrees at every corner with the physical
neck-endpoint inclusion after relabelling the corner by its incident neck. -/
theorem coordinateUnlinkExteriorPlanarRightOuterSectorCarrierHomeomorph_endpoint
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarRightNodeEndpoint m) :
    coordinateUnlinkExteriorPlanarRightOuterSectorCarrierHomeomorph m
        (coordinateUnlinkExteriorPlanarRightNodeEndpointToOuter m x) =
      coordinateUnlinkExteriorPlanarNeckEndpointToRightOuterParameter m
        (coordinateUnlinkExteriorPlanarRightNodeEndpointRelabelHomeomorph m x) := by
  apply Subtype.ext
  rw [coordinateUnlinkExteriorPlanarRightOuterSectorCarrierHomeomorph_apply_coe]
  exact coordinateUnlinkExteriorPlanarRightOuterSectorParameter_endpoint m x

end SplittingSpheres
