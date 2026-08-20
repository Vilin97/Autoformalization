/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkMeridianDeckIndex
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarFlower
public import SplittingSpheres.Handlebody.CoordinateExteriorPuncturedDiskBoundary

/-!
# Lifted inner boundary circles in the planar power pullback

The two inner circles of the punctured normal disk behave differently in the power pullback.
Above the right circle, the base parameter is traversed by the degree-`m` circle map while the
power coordinate traverses one circle; this one circle is the entire restricted pullback.  Above
the left circle, a selected continuous root branch gives one closed lifted circle, and its
`ZMod m` deck translates are pairwise disjoint and exhaust the restricted pullback.

All statements are point-set statements about the explicit pullback.  In particular, this file
makes no induced-orientation, surface-classification, or ribbon-thickening claim.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-! ## Elementary circle and fiber facts -/

theorem injective_unlinkUnitCircleComplex : Injective unlinkUnitCircleComplex := by
  intro u v huv
  apply Subtype.ext
  rw [← complexToUnlinkNormalPlane_unlinkUnitCircleComplex u,
    ← complexToUnlinkNormalPlane_unlinkUnitCircleComplex v, huv]

/-- For nonzero degree, the explicit power map on the project's unit circle is surjective. -/
theorem surjective_unlinkUnitCirclePow (m : ℕ) [NeZero m] :
    Surjective (unlinkUnitCirclePow m) := by
  intro w
  let b : ℂˣ := Units.mk0 (unlinkUnitCircleComplex w)
    (unlinkUnitCircleComplex_ne_zero w)
  obtain ⟨a, ha⟩ := (Complex.isQuotientCoveringMap_npow m).surjective b
  have haval : (a : ℂ) ^ m = unlinkUnitCircleComplex w :=
    congrArg Units.val ha
  have hanormpow : ‖(a : ℂ)‖ ^ m = 1 := by
    rw [← norm_pow, haval, norm_unlinkUnitCircleComplex]
  have hanorm : ‖(a : ℂ)‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg (a : ℂ)) (NeZero.ne m)).mp hanormpow
  let u : Sphere 1 :=
    ⟨complexToUnlinkNormalPlane (a : ℂ), by
      rw [mem_sphere_zero_iff_norm, norm_complexToUnlinkNormalPlane, hanorm]⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  change complexToUnlinkNormalPlane
      (unlinkUnitCircleComplex u ^ m) = w.1
  rw [show unlinkUnitCircleComplex u = (a : ℂ) by
      exact unlinkNormalPlaneToComplex_complexToUnlinkNormalPlane _, haval,
    complexToUnlinkNormalPlane_unlinkUnitCircleComplex]

/-- The intrinsic roots-of-unity action on the planar pullback is free at every point. -/
theorem coordinateUnlinkExteriorPuncturedNormalDiskPowerDeck_smul_right_injective
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    Injective (fun u : rootsOfUnity m ℂ ↦ u • z) := by
  intro u v huv
  apply Subtype.ext
  apply Units.ext
  have hcoordinate := congrArg
    (fun q : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m ↦
      ((q.1.2 : {ζ : ℂ // ζ ≠ 0}) : ℂ)) huv
  change ((u.1 : ℂˣ) : ℂ) * z.1.2.1 =
    ((v.1 : ℂˣ) : ℂ) * z.1.2.1 at hcoordinate
  exact mul_right_cancel₀ z.1.2.2 hcoordinate

/-- Two planar-pullback points above the same punctured-disk point differ by a unique deck
transformation. -/
theorem existsUnique_coordinateUnlinkExteriorPuncturedNormalDiskPowerDeck_smul_eq
    (m : ℕ)
    (z w : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m)
    (hbase : z.1.1 = w.1.1) :
    ∃! u : rootsOfUnity m ℂ, u • z = w := by
  let a : ℂ := z.1.2.1
  let b : ℂ := w.1.2.1
  have ha : a ≠ 0 := z.1.2.2
  have hb : b ≠ 0 := w.1.2.2
  have hpowers : b ^ m = a ^ m := by
    change w.1.2.1 ^ m = z.1.2.1 ^ m
    calc
      w.1.2.1 ^ m =
          (coordinateUnlinkExteriorPuncturedNormalDiskCharacter w.1.1 : ℂ) :=
        (congrArg Subtype.val w.2).symm
      _ = (coordinateUnlinkExteriorPuncturedNormalDiskCharacter z.1.1 : ℂ) :=
        congrArg (fun x ↦
          (coordinateUnlinkExteriorPuncturedNormalDiskCharacter x : ℂ)) hbase.symm
      _ = z.1.2.1 ^ m := congrArg Subtype.val z.2
  let q : ℂˣ := Units.mk0 (b / a) (div_ne_zero hb ha)
  have hq : (q : ℂ) ^ m = 1 := by
    change (b / a) ^ m = 1
    rw [div_pow, hpowers, div_self (pow_ne_zero m ha)]
  let u : rootsOfUnity m ℂ := ⟨q, (mem_rootsOfUnity' m q).mpr hq⟩
  have hu : u • z = w := by
    apply Subtype.ext
    apply Prod.ext
    · exact hbase
    · apply Subtype.ext
      change (b / a) * a = b
      exact div_mul_cancel₀ b ha
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact coordinateUnlinkExteriorPuncturedNormalDiskPowerDeck_smul_right_injective m z
    (hv.trans hu.symm)

/-! ## The connected right boundary -/

/-- The selected power coordinate on the right lifted boundary circle. -/
def coordinateUnlinkExteriorPlanarRightInnerLiftPowerCoordinate
    (m : ℕ) [NeZero m] (u : Sphere 1) : {z : ℂ // z ≠ 0} :=
  ⟨((unlinkEighthPowerRootUnit m : ℂˣ) : ℂ) * unlinkUnitCircleComplex u,
    mul_ne_zero (Units.ne_zero _) (unlinkUnitCircleComplex_ne_zero u)⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarRightInnerLiftPowerCoordinate_pow
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    (coordinateUnlinkExteriorPlanarRightInnerLiftPowerCoordinate m u : ℂ) ^ m =
      (coordinateUnlinkExteriorPuncturedNormalDiskCharacter
        (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 1
          (unlinkUnitCirclePow m u)) : ℂ) := by
  change ((((unlinkEighthPowerRootUnit m : ℂˣ) : ℂ) *
      unlinkUnitCircleComplex u) ^ m) = _
  rw [coordinateUnlinkExteriorPuncturedNormalDiskCharacter_innerBoundary_one,
    unlinkUnitCircleComplex_pow, mul_pow, unlinkEighthPowerRootUnit_pow]

theorem continuous_coordinateUnlinkExteriorPlanarRightInnerLiftPowerCoordinate
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarRightInnerLiftPowerCoordinate m) := by
  apply Continuous.subtype_mk
  exact continuous_const.mul continuous_unlinkUnitCircleComplex

/-- The single lifted circle above the right inner boundary.  Its base parameter runs through
the degree-`m` power map while its fiber coordinate runs once around the selected root circle. -/
def coordinateUnlinkExteriorPlanarRightInnerLift
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m :=
  ⟨(coordinateUnlinkExteriorPuncturedDiskInnerBoundary 1
      (unlinkUnitCirclePow m u),
    coordinateUnlinkExteriorPlanarRightInnerLiftPowerCoordinate m u), by
    apply Subtype.ext
    exact (coordinateUnlinkExteriorPlanarRightInnerLiftPowerCoordinate_pow m u).symm⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarRightInnerLift_proj
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarRightInnerLift m u) =
      coordinateUnlinkExteriorPuncturedDiskInnerBoundary 1
        (unlinkUnitCirclePow m u) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarRightInnerLift_powerCoordinate
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    (coordinateUnlinkExteriorPlanarRightInnerLift m u).1.2 =
      coordinateUnlinkExteriorPlanarRightInnerLiftPowerCoordinate m u :=
  rfl

theorem continuous_coordinateUnlinkExteriorPlanarRightInnerLift
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarRightInnerLift m) := by
  apply Continuous.subtype_mk
  exact ((continuous_coordinateUnlinkExteriorPuncturedDiskInnerBoundary 1).comp
      (continuous_unlinkUnitCirclePow m)).prodMk
    (continuous_coordinateUnlinkExteriorPlanarRightInnerLiftPowerCoordinate m)

theorem injective_coordinateUnlinkExteriorPlanarRightInnerLift
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarRightInnerLift m) := by
  intro u v huv
  apply injective_unlinkUnitCircleComplex
  have hcoordinate := congrArg
    (fun z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m ↦
      ((z.1.2 : {ζ : ℂ // ζ ≠ 0}) : ℂ)) huv
  change ((unlinkEighthPowerRootUnit m : ℂˣ) : ℂ) *
      unlinkUnitCircleComplex u =
    ((unlinkEighthPowerRootUnit m : ℂˣ) : ℂ) *
      unlinkUnitCircleComplex v at hcoordinate
  exact mul_left_cancel₀ (Units.ne_zero _) hcoordinate

/-- Translating the source circle by a root of unity is exactly the corresponding deck
translation of the right lifted circle. -/
theorem coordinateUnlinkExteriorPlanarRightInnerLift_circleDeckTranslation
    (m : ℕ) [NeZero m] (a : rootsOfUnity m ℂ) (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarRightInnerLift m
        (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m a u) =
      a • coordinateUnlinkExteriorPlanarRightInnerLift m u := by
  apply Subtype.ext
  apply Prod.ext
  · change coordinateUnlinkExteriorPuncturedDiskInnerBoundary 1
        (unlinkUnitCirclePow m
          (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m a u)) =
      (coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap m a
        (coordinateUnlinkExteriorPlanarRightInnerLift m u)).1.1
    rw [coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap_base,
      unlinkUnitCirclePow_circleDeckTranslation]
    rfl
  · apply Subtype.ext
    change ((coordinateUnlinkExteriorPlanarRightInnerLiftPowerCoordinate m
        (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m a u) :
          {ζ : ℂ // ζ ≠ 0}) : ℂ) =
      ((coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap m a
        (coordinateUnlinkExteriorPlanarRightInnerLift m u)).1.2 : ℂ)
    rw [coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap_powerCoordinate]
    change ((unlinkEighthPowerRootUnit m : ℂˣ) : ℂ) *
        (((a.1 : ℂˣ) : ℂ) * unlinkUnitCircleComplex u) =
      ((a.1 : ℂˣ) : ℂ) *
        (((unlinkEighthPowerRootUnit m : ℂˣ) : ℂ) *
          unlinkUnitCircleComplex u)
    ring

/-- Indexed form of the right-boundary deck-translation law. -/
theorem coordinateUnlinkExteriorPlanarRightInnerLift_zmodTranslation
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarRightInnerLift m
        (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m
          (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)) u) =
      standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a) •
        coordinateUnlinkExteriorPlanarRightInnerLift m u :=
  coordinateUnlinkExteriorPlanarRightInnerLift_circleDeckTranslation m _ u

/-- In particular, the standard positive generator acts on the one connected right lift by the
circle translation indexed by `1 : ZMod m`. -/
theorem coordinateUnlinkExteriorPlanarRightInnerLift_zmodOne
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarRightInnerLift m
        (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m
          (standardUnlinkPowerDeckGenerator m) u) =
      standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd (1 : ZMod m)) •
        coordinateUnlinkExteriorPlanarRightInnerLift m u := by
  rw [standardUnlinkPowerDeckGenerator_eq_standardZMod_one]
  exact coordinateUnlinkExteriorPlanarRightInnerLift_zmodTranslation m 1 u

/-- The exact part of the planar pullback lying above the right inner boundary. -/
def coordinateUnlinkExteriorPlanarRightInnerBoundaryCarrier (m : ℕ) :
    Set (CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :=
  topologicalCoverPullbackRestrictionRange (nonzeroComplexPow m)
    coordinateUnlinkExteriorPuncturedNormalDiskCharacter
    (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 1)

@[simp]
theorem mem_coordinateUnlinkExteriorPlanarRightInnerBoundaryCarrier
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    z ∈ coordinateUnlinkExteriorPlanarRightInnerBoundaryCarrier m ↔
      z.1.1 ∈ Set.range
        (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 1) :=
  Iff.rfl

/-- The right lifted circle exhausts the whole pullback over the right inner boundary. -/
theorem range_coordinateUnlinkExteriorPlanarRightInnerLift
    (m : ℕ) [NeZero m] :
    Set.range (coordinateUnlinkExteriorPlanarRightInnerLift m) =
      coordinateUnlinkExteriorPlanarRightInnerBoundaryCarrier m := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨unlinkUnitCirclePow m u, rfl⟩
  · rintro ⟨w, hw⟩
    obtain ⟨u, hu⟩ := surjective_unlinkUnitCirclePow m w
    let z₀ := coordinateUnlinkExteriorPlanarRightInnerLift m u
    have hbase : z₀.1.1 = z.1.1 := by
      change coordinateUnlinkExteriorPuncturedDiskInnerBoundary 1
          (unlinkUnitCirclePow m u) = z.1.1
      rw [hu]
      change coordinateUnlinkExteriorPuncturedDiskInnerBoundary 1 w = z.1.1 at hw
      exact hw
    obtain ⟨a, ha, -⟩ :=
      existsUnique_coordinateUnlinkExteriorPuncturedNormalDiskPowerDeck_smul_eq
        m z₀ z hbase
    refine ⟨coordinateUnlinkExteriorOneHandleCircleDeckTranslation m a u, ?_⟩
    rw [coordinateUnlinkExteriorPlanarRightInnerLift_circleDeckTranslation, ha]

/-- The right lifted circle is a topological embedding. -/
theorem isEmbedding_coordinateUnlinkExteriorPlanarRightInnerLift
    (m : ℕ) [NeZero m] :
    IsEmbedding (coordinateUnlinkExteriorPlanarRightInnerLift m) :=
  (continuous_coordinateUnlinkExteriorPlanarRightInnerLift m).isClosedEmbedding
    (injective_coordinateUnlinkExteriorPlanarRightInnerLift m) |>.isEmbedding

/-- The right lift is a homeomorphism from one circle onto the full right-boundary carrier. -/
def coordinateUnlinkExteriorPlanarRightInnerBoundaryHomeomorph
    (m : ℕ) [NeZero m] :
    Sphere 1 ≃ₜ coordinateUnlinkExteriorPlanarRightInnerBoundaryCarrier m :=
  (isEmbedding_coordinateUnlinkExteriorPlanarRightInnerLift m).toHomeomorph.trans
    (Homeomorph.setCongr
      (range_coordinateUnlinkExteriorPlanarRightInnerLift m))

@[simp]
theorem coordinateUnlinkExteriorPlanarRightInnerBoundaryHomeomorph_apply_coe
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    ((coordinateUnlinkExteriorPlanarRightInnerBoundaryHomeomorph m u :
        coordinateUnlinkExteriorPlanarRightInnerBoundaryCarrier m) :
      CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) =
      coordinateUnlinkExteriorPlanarRightInnerLift m u :=
  rfl

/-- Set-level connectedness of the entire lifted right boundary. -/
theorem isConnected_coordinateUnlinkExteriorPlanarRightInnerBoundaryCarrier
    (m : ℕ) [NeZero m] :
    IsConnected (coordinateUnlinkExteriorPlanarRightInnerBoundaryCarrier m) := by
  rw [← range_coordinateUnlinkExteriorPlanarRightInnerLift m]
  simpa only [image_univ] using
    isPathConnected_sphereOne.isConnected.image
      (coordinateUnlinkExteriorPlanarRightInnerLift m)
      (continuous_coordinateUnlinkExteriorPlanarRightInnerLift m).continuousOn

/-! ## The `m` closed left boundary circles -/

theorem coordinateUnlinkExteriorPuncturedNormalDiskCharacter_innerBoundary_zero_mem_leftBall
    (u : Sphere 1) :
    (coordinateUnlinkExteriorPuncturedNormalDiskCharacter
        (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0 u) : ℂ) ∈
      unlinkLeftCharacterBall := by
  rw [coordinateUnlinkExteriorPuncturedNormalDiskCharacter_innerBoundary_zero]
  change dist ((-1 : ℂ) + (1 / 8 : ℂ) * unlinkUnitCircleComplex u) (-1) < 1 / 4
  rw [Complex.dist_eq]
  have hsub : (-1 : ℂ) + (1 / 8 : ℂ) * unlinkUnitCircleComplex u - (-1) =
      (1 / 8 : ℂ) * unlinkUnitCircleComplex u := by ring
  rw [hsub, norm_mul, norm_unlinkUnitCircleComplex]
  norm_num

/-- The selected continuous root coordinate above the left inner boundary. -/
def coordinateUnlinkExteriorPlanarLeftInnerLiftPowerCoordinate
    (m : ℕ) [NeZero m] (u : Sphere 1) : {z : ℂ // z ≠ 0} :=
  ⟨unlinkLeftCharacterPowerRoot m
      (coordinateUnlinkExteriorPuncturedNormalDiskCharacter
        (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0 u)), by
    intro hz
    have hp := unlinkLeftCharacterPowerRoot_pow m
      (coordinateUnlinkExteriorPuncturedNormalDiskCharacter
        (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0 u) : ℂ)
    rw [hz, zero_pow (NeZero.ne m)] at hp
    exact (coordinateUnlinkExteriorPuncturedNormalDiskCharacter
      (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0 u)).2 hp.symm⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftInnerLiftPowerCoordinate_pow
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    (coordinateUnlinkExteriorPlanarLeftInnerLiftPowerCoordinate m u : ℂ) ^ m =
      (coordinateUnlinkExteriorPuncturedNormalDiskCharacter
        (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0 u) : ℂ) :=
  unlinkLeftCharacterPowerRoot_pow m _

theorem continuous_coordinateUnlinkExteriorPlanarLeftInnerLiftPowerCoordinate
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarLeftInnerLiftPowerCoordinate m) := by
  apply Continuous.subtype_mk
  exact (continuousOn_unlinkLeftCharacterPowerRoot m).comp_continuous
    (continuous_subtype_val.comp
      (continuous_coordinateUnlinkExteriorPuncturedNormalDiskCharacter.comp
        (continuous_coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0)))
    coordinateUnlinkExteriorPuncturedNormalDiskCharacter_innerBoundary_zero_mem_leftBall

/-- One selected closed lift of the left inner boundary circle. -/
def coordinateUnlinkExteriorPlanarLeftInnerLift
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m :=
  ⟨(coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0 u,
    coordinateUnlinkExteriorPlanarLeftInnerLiftPowerCoordinate m u), by
    apply Subtype.ext
    exact (coordinateUnlinkExteriorPlanarLeftInnerLiftPowerCoordinate_pow m u).symm⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftInnerLift_proj
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarLeftInnerLift m u) =
      coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0 u :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftInnerLift_powerCoordinate
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    (coordinateUnlinkExteriorPlanarLeftInnerLift m u).1.2 =
      coordinateUnlinkExteriorPlanarLeftInnerLiftPowerCoordinate m u :=
  rfl

theorem continuous_coordinateUnlinkExteriorPlanarLeftInnerLift
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarLeftInnerLift m) := by
  apply Continuous.subtype_mk
  exact (continuous_coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0).prodMk
    (continuous_coordinateUnlinkExteriorPlanarLeftInnerLiftPowerCoordinate m)

theorem injective_coordinateUnlinkExteriorPlanarLeftInnerLift
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPlanarLeftInnerLift m) := by
  intro u v huv
  apply injective_coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0
  exact congrArg
    (fun z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m ↦ z.1.1) huv

theorem isEmbedding_coordinateUnlinkExteriorPlanarLeftInnerLift
    (m : ℕ) [NeZero m] :
    IsEmbedding (coordinateUnlinkExteriorPlanarLeftInnerLift m) :=
  (continuous_coordinateUnlinkExteriorPlanarLeftInnerLift m).isClosedEmbedding
    (injective_coordinateUnlinkExteriorPlanarLeftInnerLift m) |>.isEmbedding

/-- The left lifted circle indexed by `a : ZMod m`. -/
def coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1) :
    CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m :=
  standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a) •
    coordinateUnlinkExteriorPlanarLeftInnerLift m u

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate_proj
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1) :
    coordinateUnlinkExteriorPuncturedNormalDiskPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m a u) =
      coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0 u :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate_powerCoordinate
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1) :
    ((coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m a u).1.2 : ℂ) =
      (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) *
        (coordinateUnlinkExteriorPlanarLeftInnerLiftPowerCoordinate m u : ℂ) :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate_zero
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m 0 u =
      coordinateUnlinkExteriorPlanarLeftInnerLift m u := by
  simp [coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate]

theorem continuous_coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Continuous (coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m a) :=
  (continuous_coordinateUnlinkExteriorPuncturedNormalDiskPowerDeckMap m
      (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a))).comp
    (continuous_coordinateUnlinkExteriorPlanarLeftInnerLift m)

theorem injective_coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Injective (coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m a) := by
  intro u v huv
  apply injective_coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0
  exact congrArg
    (fun z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m ↦ z.1.1) huv

theorem isEmbedding_coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsEmbedding (coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m a) :=
  (continuous_coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m a).isClosedEmbedding
    (injective_coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m a) |>.isEmbedding

/-- Different `ZMod m` indices give disjoint closed lifted circles over the left boundary. -/
theorem disjoint_range_coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate
    (m : ℕ) [NeZero m] {a b : ZMod m} (hab : a ≠ b) :
    Disjoint
      (Set.range (coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m a))
      (Set.range (coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m b)) := by
  rw [Set.disjoint_left]
  rintro z ⟨u, rfl⟩ ⟨v, huv⟩
  have hbase := congrArg
    (fun q : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m ↦ q.1.1) huv
  have huv' : u = v :=
    injective_coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0 hbase.symm
  subst v
  have hroot :
      standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a) =
        standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd b) :=
    coordinateUnlinkExteriorPuncturedNormalDiskPowerDeck_smul_right_injective m
      (coordinateUnlinkExteriorPlanarLeftInnerLift m u) huv.symm
  have hab' : Multiplicative.ofAdd a = Multiplicative.ofAdd b :=
    (standardRootsOfUnityZModMulEquiv m).injective hroot
  exact hab (Multiplicative.ofAdd.injective hab')

/-- The exact part of the planar pullback lying above the left inner boundary. -/
def coordinateUnlinkExteriorPlanarLeftInnerBoundaryCarrier (m : ℕ) :
    Set (CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :=
  topologicalCoverPullbackRestrictionRange (nonzeroComplexPow m)
    coordinateUnlinkExteriorPuncturedNormalDiskCharacter
    (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0)

@[simp]
theorem mem_coordinateUnlinkExteriorPlanarLeftInnerBoundaryCarrier
    (m : ℕ) (z : CoordinateUnlinkExteriorPuncturedNormalDiskPowerPullback m) :
    z ∈ coordinateUnlinkExteriorPlanarLeftInnerBoundaryCarrier m ↔
      z.1.1 ∈ Set.range
        (coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0) :=
  Iff.rfl

/-- The `m` deck translates of the selected left circle exhaust the whole left-boundary
carrier. -/
theorem iUnion_range_coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate
    (m : ℕ) [NeZero m] :
    (⋃ a : ZMod m,
      Set.range (coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m a)) =
      coordinateUnlinkExteriorPlanarLeftInnerBoundaryCarrier m := by
  ext z
  constructor
  · intro hz
    simp only [Set.mem_iUnion, Set.mem_range] at hz
    rcases hz with ⟨a, u, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, hu⟩
    let z₀ := coordinateUnlinkExteriorPlanarLeftInnerLift m u
    have hbase : z₀.1.1 = z.1.1 := by
      change coordinateUnlinkExteriorPuncturedDiskInnerBoundary 0 u = z.1.1
      exact hu
    obtain ⟨a, ha, -⟩ :=
      existsUnique_coordinateUnlinkExteriorPuncturedNormalDiskPowerDeck_smul_eq
        m z₀ z hbase
    let b : Multiplicative (ZMod m) :=
      (standardRootsOfUnityZModMulEquiv m).symm a
    simp only [Set.mem_iUnion, Set.mem_range]
    refine ⟨b.toAdd, u, ?_⟩
    change standardRootsOfUnityZModMulEquiv m b • z₀ = z
    rw [(standardRootsOfUnityZModMulEquiv m).apply_symm_apply]
    exact ha

/-- Every individual left lifted boundary circle is connected. -/
theorem isConnected_range_coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate
    (m : ℕ) [NeZero m] (a : ZMod m) :
    IsConnected
      (Set.range (coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m a)) :=
  by
    simpa only [image_univ] using
      isPathConnected_sphereOne.isConnected.image
        (coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m a)
        (continuous_coordinateUnlinkExteriorPlanarLeftInnerLiftTranslate m a).continuousOn

end SplittingSpheres
