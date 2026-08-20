/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarOuterRightSector

/-!
# Deck-equivariant parameters for the retained planar outer circle

The one-handle boundary trivialization makes the retained outer-circle parameter equivariant
for the same roots-of-unity action as the planar power pullback.  This file proves that exact
equivariance, including the complex phase formula for the standard `ZMod m` index.

It then transports the selected right semicircle and all its labelled deck translates back to
the retained `Sphere 1` parameter.  The parameter sectors are jointly injective, pairwise
disjoint, and exhaust exactly the closed right parameter carrier.  Their endpoint laws use the
canonical, but deliberately unevaluated, endpoint offset from
`CoordinateExteriorPlanarOuterRightSector`.

No cyclic orientation is chosen, and no assertion that the endpoint offset is `1` is made.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## Equivariance of the existing outer lift -/

/-- Translating the source circle by an `m`th root of unity is exactly the intrinsic deck map
on the planar outer lift. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarOuterLift_circleDeckTranslation
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ) (v : Sphere 1) :
    coordinateUnlinkExteriorPlanarOuterLift m
        (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m u v) =
      coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap m u
        (coordinateUnlinkExteriorPlanarOuterLift m v) := by
  apply Subtype.ext
  apply Prod.ext
  · change coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarOuterLift m
          (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m u v)) =
      coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarOuterLift m v)
    rw [coordinateUnlinkExteriorPlanarOuterLift_proj,
      coordinateUnlinkExteriorPlanarOuterLift_proj,
      unlinkUnitCirclePow_circleDeckTranslation]
  · apply Subtype.ext
    rw [coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap_powerCoordinate,
      coordinateUnlinkExteriorPlanarOuterLift_powerCoordinate,
      coordinateUnlinkExteriorPlanarOuterLift_powerCoordinate]
    have h := coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph_deckTranslation
      m u (v, coordinateUnlinkExteriorPlanarOuterBoundarySpherePoint)
    exact congrArg
      (fun z : CoordinateUnlinkExteriorBoundaryPowerPullback m ↦ (z.1.2 : ℂ)) h

/-- The same equivariance after transport to the flower coordinate. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerOuter_circleDeckTranslation
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ) (v : Sphere 1) :
    coordinateUnlinkExteriorPlanarFlowerOuter m
        (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m u v) =
      coordinateUnlinkExteriorPlanarFlowerDeckMap m u
        (coordinateUnlinkExteriorPlanarFlowerOuter m v) := by
  rw [coordinateUnlinkExteriorPlanarFlowerOuter_apply,
    coordinateUnlinkExteriorPlanarFlowerOuter_apply,
    coordinateUnlinkExteriorPlanarOuterLift_circleDeckTranslation]
  exact
    coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackPlanarFlowerHomeomorph_smul
      m u (coordinateUnlinkExteriorPlanarOuterLift m v)

/-- The source-circle deck translation indexed additively by `ZMod m`. -/
def coordinateUnlinkExteriorPlanarOuterParameterDeckTranslationZMod
    (m : ℕ) [NeZero m] (a : ZMod m) (v : Sphere 1) : Sphere 1 :=
  coordinateUnlinkExteriorOneHandleCircleDeckTranslation m
    (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)) v

/-- Exact complex phase of the additive source-circle deck translation. -/
@[simp]
theorem unlinkUnitCircleComplex_planarOuterParameterDeckTranslationZMod
    (m : ℕ) [NeZero m] (a : ZMod m) (v : Sphere 1) :
    unlinkUnitCircleComplex
        (coordinateUnlinkExteriorPlanarOuterParameterDeckTranslationZMod m a v) =
      Complex.exp (2 * Real.pi * Complex.I * a.val / m) *
        unlinkUnitCircleComplex v := by
  rw [coordinateUnlinkExteriorPlanarOuterParameterDeckTranslationZMod,
    unlinkUnitCircleComplex_circleDeckTranslation,
    standardRootsOfUnityZModMulEquiv_val]

/-- Exact `ZMod m`-indexed equivariance in flower coordinates. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerOuter_deckTranslationZMod
    (m : ℕ) [NeZero m] (a : ZMod m) (v : Sphere 1) :
    coordinateUnlinkExteriorPlanarFlowerOuter m
        (coordinateUnlinkExteriorPlanarOuterParameterDeckTranslationZMod m a v) =
      coordinateUnlinkExteriorPlanarFlowerDeckMap m
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a))
        (coordinateUnlinkExteriorPlanarFlowerOuter m v) :=
  coordinateUnlinkExteriorPlanarFlowerOuter_circleDeckTranslation m _ v

/-- Source-circle deck translations compose by addition of their `ZMod m` labels. -/
theorem coordinateUnlinkExteriorPlanarOuterParameterDeckTranslationZMod_add
    (m : ℕ) [NeZero m] (a b : ZMod m) (v : Sphere 1) :
    coordinateUnlinkExteriorPlanarOuterParameterDeckTranslationZMod m a
        (coordinateUnlinkExteriorPlanarOuterParameterDeckTranslationZMod m b v) =
      coordinateUnlinkExteriorPlanarOuterParameterDeckTranslationZMod m (a + b) v := by
  apply injective_unlinkUnitCircleComplex
  change unlinkUnitCircleComplex
      (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a))
        (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m
          (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd b)) v)) =
    unlinkUnitCircleComplex
      (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd (a + b))) v)
  rw [unlinkUnitCircleComplex_circleDeckTranslation,
    unlinkUnitCircleComplex_circleDeckTranslation,
    unlinkUnitCircleComplex_circleDeckTranslation, ← mul_assoc]
  congr 1
  simpa using (congrArg
    (fun u : rootsOfUnity m ℂ ↦ (((u.1 : ℂˣ) : ℂ)))
    ((standardRootsOfUnityZModMulEquiv m).map_mul
      (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))).symm

/-! ## The selected and labelled right parameter sectors -/

/-- The retained outer-circle parameter of the selected right lifted semicircle. -/
def coordinateUnlinkExteriorPlanarSelectedRightOuterParameter
    (m : ℕ) [NeZero m]
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) : Sphere 1 :=
  (coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m).symm
    ⟨(coordinateUnlinkExteriorPlanarFlowerRightOuterArc m t).1.1, by
      change ‖(coordinateUnlinkExteriorPlanarFlowerRightOuterArc m t).1.1 ^ m +
        (1 / 2 : ℂ)‖ = sphereHandleRadius
      rw [coordinateUnlinkExteriorPlanarFlowerRightOuterArc_pow,
        coordinateUnlinkExteriorPlanarBaseRightOuterArc_add_half_norm]⟩

/-- The selected parameter really maps to the selected lifted right semicircle. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerOuter_selectedRightOuterParameter
    (m : ℕ) [NeZero m]
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarFlowerOuter m
        (coordinateUnlinkExteriorPlanarSelectedRightOuterParameter m t) =
      coordinateUnlinkExteriorPlanarFlowerRightOuterArc m t := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coordinateUnlinkExteriorPlanarFlowerOuter_val]
  rw [← coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph_coe]
  unfold coordinateUnlinkExteriorPlanarSelectedRightOuterParameter
  rw [(coordinateUnlinkExteriorPlanarOuterLiftPolynomialBoundaryHomeomorph m).apply_symm_apply]

theorem continuous_coordinateUnlinkExteriorPlanarSelectedRightOuterParameter
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarSelectedRightOuterParameter m) := by
  unfold coordinateUnlinkExteriorPlanarSelectedRightOuterParameter
  fun_prop

/-- The retained outer-circle parameter of the right sector with sheet label `a`. -/
def coordinateUnlinkExteriorPlanarRightOuterSectorParameter
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) : Sphere 1 :=
  coordinateUnlinkExteriorPlanarOuterParameterDeckTranslationZMod m a
    (coordinateUnlinkExteriorPlanarSelectedRightOuterParameter m t)

theorem continuous_coordinateUnlinkExteriorPlanarRightOuterSectorParameter
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous (coordinateUnlinkExteriorPlanarRightOuterSectorParameter m a) :=
  (continuous_coordinateUnlinkExteriorOneHandleCircleDeckTranslation m _).comp
    (continuous_coordinateUnlinkExteriorPlanarSelectedRightOuterParameter m)

/-- The parameter sector maps exactly to the previously constructed flower sector. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerOuter_rightOuterSectorParameter
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarFlowerOuter m
        (coordinateUnlinkExteriorPlanarRightOuterSectorParameter m a t) =
      coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m a t := by
  rw [coordinateUnlinkExteriorPlanarRightOuterSectorParameter,
    coordinateUnlinkExteriorPlanarFlowerOuter_deckTranslationZMod,
    coordinateUnlinkExteriorPlanarFlowerOuter_selectedRightOuterParameter]
  rfl

theorem injective_coordinateUnlinkExteriorPlanarRightOuterSectorParameterFamily
    (m : ℕ) [NeZero m] :
    Injective (fun x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval ↦
      coordinateUnlinkExteriorPlanarRightOuterSectorParameter m x.1 x.2) := by
  intro x y h
  have h' := congrArg (coordinateUnlinkExteriorPlanarFlowerOuter m) h
  rw [coordinateUnlinkExteriorPlanarFlowerOuter_rightOuterSectorParameter,
    coordinateUnlinkExteriorPlanarFlowerOuter_rightOuterSectorParameter] at h'
  exact injective_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorFamily m h'

theorem injective_coordinateUnlinkExteriorPlanarRightOuterSectorParameter
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Injective (coordinateUnlinkExteriorPlanarRightOuterSectorParameter m a) := by
  intro t s h
  have hp : (a, t) = (a, s) :=
    injective_coordinateUnlinkExteriorPlanarRightOuterSectorParameterFamily m h
  exact congrArg Prod.snd hp

/-- The parameter range of one labelled right sector. -/
def coordinateUnlinkExteriorPlanarRightOuterParameterSectorSet
    (m : ℕ) [NeZero m] (a : ZMod m) : Set (Sphere 1) :=
  range (coordinateUnlinkExteriorPlanarRightOuterSectorParameter m a)

/-- Each labelled parameter sector is genuinely a closed interval. -/
def coordinateUnlinkExteriorPlanarRightOuterParameterSectorHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorPlanarNeckInterval ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarRightOuterParameterSectorSet m a) :=
  ((continuous_coordinateUnlinkExteriorPlanarRightOuterSectorParameter m a)
    |>.isClosedEmbedding
      (injective_coordinateUnlinkExteriorPlanarRightOuterSectorParameter m a))
    |>.isEmbedding.toHomeomorph

/-- The closed right carrier in the retained outer parameter circle. -/
def coordinateUnlinkExteriorPlanarRetainedOuterParameterRightSet
    (m : ℕ) [NeZero m] : Set (Sphere 1) :=
  {u | -1 / 2 ≤ ((coordinateUnlinkExteriorPlanarFlowerOuter m u).1.1 ^ m).re}

/-- The labelled parameter sectors exhaust exactly the right parameter carrier. -/
theorem iUnion_coordinateUnlinkExteriorPlanarRightOuterParameterSectorSet
    (m : ℕ) [NeZero m] :
    (⋃ a : ZMod m,
      coordinateUnlinkExteriorPlanarRightOuterParameterSectorSet m a) =
        coordinateUnlinkExteriorPlanarRetainedOuterParameterRightSet m := by
  ext u
  constructor
  · intro hu
    rw [mem_iUnion] at hu
    obtain ⟨a, t, rfl⟩ := hu
    change -1 / 2 ≤
      ((coordinateUnlinkExteriorPlanarFlowerOuter m
        (coordinateUnlinkExteriorPlanarRightOuterSectorParameter m a t)).1.1 ^ m).re
    rw [coordinateUnlinkExteriorPlanarFlowerOuter_rightOuterSectorParameter,
      coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_pow]
    exact coordinateUnlinkExteriorPlanarBaseRightOuterArc_re_ge t
  · intro hu
    have hz : coordinateUnlinkExteriorPlanarFlowerOuter m u ∈
        coordinateUnlinkExteriorPlanarRetainedOuterRightSet m := by
      have houter : coordinateUnlinkExteriorPlanarFlowerOuter m u ∈
          coordinateUnlinkExteriorPlanarRetainedOuterSet m := by
        rw [← range_coordinateUnlinkExteriorPlanarFlowerOuter]
        exact ⟨u, rfl⟩
      exact ⟨houter, hu⟩
    rw [← iUnion_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet] at hz
    rw [mem_iUnion] at hz
    obtain ⟨a, t, ht⟩ := hz
    rw [mem_iUnion]
    refine ⟨a, t, ?_⟩
    apply injective_coordinateUnlinkExteriorPlanarFlowerOuter m
    rw [coordinateUnlinkExteriorPlanarFlowerOuter_rightOuterSectorParameter]
    exact ht

/-- Distinct labels give disjoint parameter sectors, including both endpoints. -/
theorem pairwise_disjoint_coordinateUnlinkExteriorPlanarRightOuterParameterSectorSet
    (m : ℕ) [NeZero m] :
    Pairwise fun a b : ZMod m ↦
      Disjoint (coordinateUnlinkExteriorPlanarRightOuterParameterSectorSet m a)
        (coordinateUnlinkExteriorPlanarRightOuterParameterSectorSet m b) := by
  intro a b hab
  rw [Set.disjoint_left]
  rintro u ⟨t, rfl⟩ ⟨s, hs⟩
  apply hab
  have hp : (a, t) = (b, s) :=
    injective_coordinateUnlinkExteriorPlanarRightOuterSectorParameterFamily m hs.symm
  exact congrArg Prod.fst hp

/-! ## Endpoint laws -/

theorem coordinateUnlinkExteriorPlanarRightOuterSectorParameter_zero
    (m : ℕ) [NeZero m] (a : ZMod m)
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (he : productFourEndUnitInterval e = 0) :
    coordinateUnlinkExteriorPlanarRightOuterSectorParameter m a 0 =
      coordinateUnlinkExteriorPlanarNeckOuterParameter m a e := by
  apply injective_coordinateUnlinkExteriorPlanarFlowerOuter m
  rw [coordinateUnlinkExteriorPlanarFlowerOuter_rightOuterSectorParameter,
    coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_zero,
    coordinateUnlinkExteriorPlanarFlowerOuter_neckOuterParameter, he]

theorem coordinateUnlinkExteriorPlanarRightOuterSectorParameter_one
    (m : ℕ) [NeZero m] (a : ZMod m)
    (e : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
    (he : productFourEndUnitInterval e = 1) :
    coordinateUnlinkExteriorPlanarRightOuterSectorParameter m a 1 =
      coordinateUnlinkExteriorPlanarNeckOuterParameter m
        (a + coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m) e := by
  apply injective_coordinateUnlinkExteriorPlanarFlowerOuter m
  rw [coordinateUnlinkExteriorPlanarFlowerOuter_rightOuterSectorParameter,
    coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_one,
    coordinateUnlinkExteriorPlanarFlowerOuter_neckOuterParameter, he]

end SplittingSpheres
