/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckFullCoverRange

/-!
# The normalized pieces of the strict planar neck core

This file computes the exact strict-exterior condition on the planar face of the flower model.
The two distances from the unlink tube centers are respectively
`‖z ^ m + 1‖` and `‖z ^ m‖`.  On either annulus-normalized flower half, strictness is therefore
equivalent to positive annulus time: the inner circle at time zero is excluded and every
positive-time point is included.  The whole one-handle face is strictly exterior.

The final section transports these statements to the exact strict core in the neck star.  No
connectedness, component count, or equality with a compact star piece is asserted.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open Set.Notation
open scoped unitInterval

namespace SplittingSpheres

/-! ## Exact tube distances on the planar face -/

private theorem coordinateUnlinkExteriorPlanarNeckTransport_planar_proj_closed_formula
    (m : ℕ) [NeZero m] (z : CoordinateUnlinkExteriorPlanarFlower m)
    (s : Sphere 2) :
    coordinateUnlinkExteriorEighthPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (partialSphereSpinInr
            (coordinateUnlinkExteriorPlanarFlowerOuter m) (z, s))) =
      unlinkAlignedPuncturedCapExteriorMap (1 / 8 : ℝ)
        (coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm
          (coordinateUnlinkExteriorPlanarFlowerBase m z, s)) := by
  rw [coordinateUnlinkExteriorPlanarNeckTransportHomeomorph, Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph_symm_planar,
    coordinateUnlinkExteriorPartialSphereSpinHomeomorph_proj,
    coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph_inr,
    coordinateUnlinkExteriorPuncturedCapPowerPullbackToPushout_proj]
  apply coordinateUnlinkExteriorPushoutHomeomorph_inr (by norm_num)
    oneEighth_lt_sphereHandleRadius_sub_half

/-- On the planar face, the distance from tube center `i` is exactly one of the two
polynomial distances. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_planar_tubeDistance
    (m : ℕ) [NeZero m] (z : CoordinateUnlinkExteriorPlanarFlower m)
    (s : Sphere 2) (i : Fin 2) :
    ‖standardUnlinkNormalProjection
          ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (partialSphereSpinInr
              (coordinateUnlinkExteriorPlanarFlowerOuter m) (z, s))).1.1.1) -
        standardUnlinkNormalCenter i‖ =
      if i = 0 then ‖z.1.1 ^ m + 1‖ else ‖z.1.1 ^ m‖ := by
  change ‖standardUnlinkNormalProjection
        ((coordinateUnlinkExteriorEighthPowerPullbackProj m
          (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (partialSphereSpinInr
              (coordinateUnlinkExteriorPlanarFlowerOuter m) (z, s)))).1) -
      standardUnlinkNormalCenter i‖ = _
  rw [coordinateUnlinkExteriorPlanarNeckTransport_planar_proj_closed_formula]
  change ‖standardUnlinkNormalProjection
      (unlinkAlignedCapSphereMap
        (coordinateUnlinkExteriorPuncturedCapProductHomeomorph.symm
          (coordinateUnlinkExteriorPlanarFlowerBase m z, s)).1) -
      standardUnlinkNormalCenter i‖ = _
  rw [standardUnlinkNormalProjection_unlinkAlignedCapSphereMap,
    ← sphereHandleRadius_smul_unlinkCapCoordinateCenter i,
    ← dist_eq_norm, dist_smul₀, Real.norm_eq_abs,
    abs_of_pos sphereHandleRadius_pos,
    coordinateUnlinkExteriorPuncturedCapProductHomeomorph_symm_fst_val]
  fin_cases i
  · simp only [Fin.zero_eta, ↓reduceIte]
    exact dist_planarFlowerBaseRaw_center_zero m z.1
  · simp only [Fin.mk_one, one_ne_zero, ↓reduceIte]
    exact dist_planarFlowerBaseRaw_center_one m z.1

/-- The exact distance from the left unlink tube center on the transported planar face. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_planar_leftTubeDistance
    (m : ℕ) [NeZero m] (z : CoordinateUnlinkExteriorPlanarFlower m)
    (s : Sphere 2) :
    ‖standardUnlinkNormalProjection
          ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (partialSphereSpinInr
              (coordinateUnlinkExteriorPlanarFlowerOuter m) (z, s))).1.1.1) -
        standardUnlinkNormalCenter 0‖ =
      ‖z.1.1 ^ m + 1‖ := by
  simpa using
    coordinateUnlinkExteriorPlanarNeckTransport_planar_tubeDistance m z s 0

/-- The exact distance from the right unlink tube center on the transported planar face. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_planar_rightTubeDistance
    (m : ℕ) [NeZero m] (z : CoordinateUnlinkExteriorPlanarFlower m)
    (s : Sphere 2) :
    ‖standardUnlinkNormalProjection
          ((coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
            (partialSphereSpinInr
              (coordinateUnlinkExteriorPlanarFlowerOuter m) (z, s))).1.1.1) -
        standardUnlinkNormalCenter 1‖ =
      ‖z.1.1 ^ m‖ := by
  simpa using
    coordinateUnlinkExteriorPlanarNeckTransport_planar_tubeDistance m z s 1

/-- Exact strict-core membership on the planar face. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckTransport_planar_mem_strict_iff
    (m : ℕ) [NeZero m] (z : CoordinateUnlinkExteriorPlanarFlower m)
    (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarFlowerOuter m) (z, s)) ∈
        coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m ↔
      (1 / 8 : ℝ) < ‖z.1.1 ^ m‖ ∧
        (1 / 8 : ℝ) < ‖z.1.1 ^ m + 1‖ := by
  rw [mem_coordinateUnlinkExteriorEighthPowerPullbackStrictOpens,
    mem_standardUnlinkClosedTubeExteriorOpens]
  constructor
  · intro h
    constructor
    · have hright := h 1
      rw [coordinateUnlinkExteriorPlanarNeckTransport_planar_rightTubeDistance] at hright
      exact hright
    · have hleft := h 0
      rw [coordinateUnlinkExteriorPlanarNeckTransport_planar_leftTubeDistance] at hleft
      exact hleft
  · rintro ⟨hzero, hone⟩ i
    rw [coordinateUnlinkExteriorPlanarNeckTransport_planar_tubeDistance]
    split_ifs
    · exact hone
    · exact hzero

/-! ## The normalized left annuli -/

/-- A point of a labelled normalized left annulus, included into the whole flower. -/
def coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) :
    CoordinateUnlinkExteriorPlanarFlower m :=
  coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion m
    (coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph m (a, (u, t)))

/-- The `m`th power of a normalized left-annulus point is its literal base-annulus point. -/
theorem coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint_pow
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) :
    (coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint m a u t).1.1 ^ m =
      (coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph (u, t) : ℂ) := by
  rw [coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint,
    coordinateUnlinkExteriorPlanarFlowerLeftHalfInclusion_apply,
    coordinateUnlinkExteriorPlanarNormalizedLeftHalfHomeomorph_apply,
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivialization_apply,
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationMap_coe,
    coordinateUnlinkExteriorPlanarFlowerLeftHalfTrivializationRaw_pow]

/-- Every normalized left-annulus point is strictly outside the right tube, including at its
inner endpoint. -/
theorem coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint_pow_strict
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) :
    (1 / 8 : ℝ) <
      ‖(coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint m a u t).1.1 ^ m‖ := by
  rw [coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint_pow]
  let w := coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph (u, t)
  have hw := (mem_coordinateUnlinkExteriorPlanarBaseLeftHalfSet_iff w.1).mp w.2
  calc
    (1 / 8 : ℝ) < 1 / 2 := by norm_num
    _ ≤ |w.1.re| := by
      rw [abs_of_nonpos (by linarith [hw.2.2.2])]
      linarith [hw.2.2.2]
    _ ≤ ‖w.1‖ := Complex.abs_re_le_norm w.1

/-- On a normalized left annulus, strict distance from the left tube is equivalent to positive
annulus time. -/
theorem coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint_pow_add_one_strict_iff
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) :
    (1 / 8 : ℝ) <
        ‖(coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint m a u t).1.1 ^ m + 1‖ ↔
      0 < (t : ℝ) := by
  rw [coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint_pow,
    norm_coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_add_one]
  unfold directionalRadialAnnulusRadius
  have hgap := oneEighth_lt_coordinateUnlinkExteriorPlanarLeftOuterRadius
    (unlinkUnitCircleHomeomorph u)
  constructor
  · intro h
    by_contra ht
    have ht0 : (t : ℝ) = 0 := le_antisymm (le_of_not_gt ht) t.2.1
    rw [ht0] at h
    linarith
  · intro ht
    have hprod : 0 < (t : ℝ) *
        (coordinateUnlinkExteriorPlanarLeftOuterRadius
          (unlinkUnitCircleHomeomorph u) - 1 / 8) :=
      mul_pos ht (sub_pos.mpr hgap)
    linarith

/-- Exact strict-exterior membership on a normalized labelled left annulus. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckTransport_normalizedLeft_mem_strict_iff
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint m a u t, s)) ∈
        coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m ↔
      0 < (t : ℝ) := by
  rw [coordinateUnlinkExteriorPlanarNeckTransport_planar_mem_strict_iff]
  constructor
  · exact fun h ↦
      (coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint_pow_add_one_strict_iff
        m a u t).mp h.2
  · intro ht
    exact ⟨coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint_pow_strict m a u t,
      (coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint_pow_add_one_strict_iff
        m a u t).mpr ht⟩

/-- The inner circle of every normalized left annulus is outside the strict core. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_normalizedLeft_zero_not_mem_strict
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint m a u 0, s)) ∉
        coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m := by
  rw [coordinateUnlinkExteriorPlanarNeckTransport_normalizedLeft_mem_strict_iff]
  norm_num

/-- Every positive-time point of a normalized left annulus belongs to the strict core. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_normalizedLeft_mem_strict_of_pos
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) (ht : 0 < (t : ℝ)) :
    coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint m a u t, s)) ∈
        coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m :=
  (coordinateUnlinkExteriorPlanarNeckTransport_normalizedLeft_mem_strict_iff
    m a u t s).mpr ht

/-! ## The normalized right annulus -/

/-- A point of the normalized right annulus, included into the whole flower. -/
def coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint
    (m : ℕ) [NeZero m] (u : Sphere 1) (t : Set.Icc (0 : ℝ) 1) :
    CoordinateUnlinkExteriorPlanarFlower m :=
  coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion m
    (coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m (u, t))

/-- Exact norm of the `m`th power on the normalized right annulus. -/
theorem norm_coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint_pow
    (m : ℕ) [NeZero m] (u : Sphere 1) (t : Set.Icc (0 : ℝ) 1) :
    ‖(coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint m u t).1.1 ^ m‖ =
      directionalRadialAnnulusRadius
          (coordinateUnlinkExteriorPlanarRightInnerRadius m)
          (coordinateUnlinkExteriorPlanarRightOuterRadius m)
          (unlinkUnitCircleHomeomorph u) t ^ m := by
  rw [norm_pow, coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint,
    coordinateUnlinkExteriorPlanarFlowerRightHalfInclusion_apply,
    norm_coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_apply]

/-- On the normalized right annulus, strict distance from the right tube is equivalent to
positive annulus time. -/
theorem coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint_pow_strict_iff
    (m : ℕ) [NeZero m] (u : Sphere 1) (t : Set.Icc (0 : ℝ) 1) :
    (1 / 8 : ℝ) <
        ‖(coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint m u t).1.1 ^ m‖ ↔
      0 < (t : ℝ) := by
  rw [norm_coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint_pow,
    ← coordinateUnlinkExteriorPlanarRightInnerRadius_pow m,
    pow_lt_pow_iff_left₀
      (coordinateUnlinkExteriorPlanarRightInnerRadius_pos m).le
      (directionalRadialAnnulusRadius_pos
        (coordinateUnlinkExteriorPlanarRightInnerRadius_pos m)
        (coordinateUnlinkExteriorPlanarRightInner_lt_outer m)
        (unlinkUnitCircleHomeomorph u) t).le
      (NeZero.ne m)]
  unfold directionalRadialAnnulusRadius
  have hgap := coordinateUnlinkExteriorPlanarRightInner_lt_outer m
    (unlinkUnitCircleHomeomorph u)
  constructor
  · intro h
    by_contra ht
    have ht0 : (t : ℝ) = 0 := le_antisymm (le_of_not_gt ht) t.2.1
    rw [ht0] at h
    linarith
  · intro ht
    have hprod : 0 < (t : ℝ) *
        (coordinateUnlinkExteriorPlanarRightOuterRadius m
            (unlinkUnitCircleHomeomorph u) -
          coordinateUnlinkExteriorPlanarRightInnerRadius m) :=
      mul_pos ht (sub_pos.mpr hgap)
    linarith

/-- Every normalized right-annulus point is strictly outside the left tube, including at its
inner endpoint. -/
theorem coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint_pow_add_one_strict
    (m : ℕ) [NeZero m] (u : Sphere 1) (t : Set.Icc (0 : ℝ) 1) :
    (1 / 8 : ℝ) <
      ‖(coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint m u t).1.1 ^ m + 1‖ := by
  let w := coordinateUnlinkExteriorPlanarNormalizedRightHalfHomeomorph m (u, t)
  have hw : (-1 / 2 : ℝ) ≤ (w.1.1.1 ^ m).re := w.2
  change (1 / 8 : ℝ) < ‖w.1.1.1 ^ m + 1‖
  calc
    (1 / 8 : ℝ) < 1 / 2 := by norm_num
    _ ≤ |(w.1.1.1 ^ m + 1).re| := by
      rw [Complex.add_re, Complex.one_re, abs_of_nonneg (by linarith)]
      linarith
    _ ≤ ‖w.1.1.1 ^ m + 1‖ := Complex.abs_re_le_norm _

/-- Exact strict-exterior membership on the normalized right annulus. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckTransport_normalizedRight_mem_strict_iff
    (m : ℕ) [NeZero m] (u : Sphere 1) (t : Set.Icc (0 : ℝ) 1)
    (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint m u t, s)) ∈
        coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m ↔
      0 < (t : ℝ) := by
  rw [coordinateUnlinkExteriorPlanarNeckTransport_planar_mem_strict_iff]
  constructor
  · exact fun h ↦
      (coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint_pow_strict_iff
        m u t).mp h.1
  · intro ht
    exact ⟨(coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint_pow_strict_iff
        m u t).mpr ht,
      coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint_pow_add_one_strict m u t⟩

/-- The inner circle of the normalized right annulus is outside the strict core. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_normalizedRight_zero_not_mem_strict
    (m : ℕ) [NeZero m] (u : Sphere 1) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint m u 0, s)) ∉
        coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m := by
  rw [coordinateUnlinkExteriorPlanarNeckTransport_normalizedRight_mem_strict_iff]
  norm_num

/-- Every positive-time point of the normalized right annulus belongs to the strict core. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_normalizedRight_mem_strict_of_pos
    (m : ℕ) [NeZero m] (u : Sphere 1) (t : Set.Icc (0 : ℝ) 1)
    (s : Sphere 2) (ht : 0 < (t : ℝ)) :
    coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint m u t, s)) ∈
        coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m :=
  (coordinateUnlinkExteriorPlanarNeckTransport_normalizedRight_mem_strict_iff
    m u t s).mpr ht

/-! ## The one-handle face -/

/-- The closed-pullback projection of an arbitrary transported one-handle point. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_oneHandle_proj_closed
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    coordinateUnlinkExteriorEighthPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (partialSphereSpinInl
            (coordinateUnlinkExteriorPlanarFlowerOuter m) x)) =
      unlinkAlignedOneHandleExteriorMap
        oneEighth_lt_sphereHandleRadius_sub_half
        (coordinateUnlinkExteriorOneHandleBasePowerMap m x) := by
  rw [coordinateUnlinkExteriorPlanarNeckTransportHomeomorph, Homeomorph.trans_apply,
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorph_symm_oneHandle,
    coordinateUnlinkExteriorPartialSphereSpinHomeomorph_proj,
    coordinateUnlinkExteriorPartialSphereSpinPushoutHomeomorph_inl,
    coordinateUnlinkExteriorOneHandlePowerPullbackToPushout_proj,
    coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph_proj]
  exact coordinateUnlinkExteriorPushoutHomeomorph_inl (by norm_num)
    oneEighth_lt_sphereHandleRadius_sub_half
    (coordinateUnlinkExteriorOneHandleBasePowerMap m x)

/-- Every point of the transported one-handle face belongs to the strict exterior. -/
theorem coordinateUnlinkExteriorPlanarNeckTransport_oneHandle_mem_strict
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
        (partialSphereSpinInl
          (coordinateUnlinkExteriorPlanarFlowerOuter m) x) ∈
      coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m := by
  rw [mem_coordinateUnlinkExteriorEighthPowerPullbackStrictOpens,
    mem_standardUnlinkClosedTubeExteriorOpens]
  intro i
  change (1 / 8 : ℝ) <
    ‖standardUnlinkNormalProjection
      ((coordinateUnlinkExteriorEighthPowerPullbackProj m
        (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m
          (partialSphereSpinInl
            (coordinateUnlinkExteriorPlanarFlowerOuter m) x))).1) -
      standardUnlinkNormalCenter i‖
  rw [coordinateUnlinkExteriorPlanarNeckTransport_oneHandle_proj_closed,
    unlinkAlignedOneHandleExteriorMap_coe, ← dist_eq_norm]
  exact oneEighth_lt_sphereHandleRadius_sub_half.trans_le
    (sphereHandleRadius_sub_half_le_dist_oneHandle_normalCenter i
      (coordinateUnlinkExteriorOneHandleBasePowerMap m x))

/-! ## Exact preimages in the neck star -/

/-- Pulling the transported strict core back through the flower-to-star homeomorphism is exactly
the inverse image of the strict coordinate exterior under neck transport. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar_mem_strictCore_iff
    (m : ℕ) [NeZero m]
    (x : CoordinateUnlinkExteriorPlanarFlowerPartialSphereSpin m) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m x ∈
        coordinateUnlinkExteriorPlanarNeckStarStrictCore m ↔
      coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m x ∈
        coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m := by
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hy⟩
    have hxy :
        (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm z = x :=
      (coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m).injective hy
    rw [← hxy, (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).apply_symm_apply]
    exact hz
  · intro hx
    refine ⟨x, ⟨coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m x, hx, ?_⟩, rfl⟩
    exact (coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m).symm_apply_apply x

/-- Set-level exact preimage of the strict core in the flower partial-spin model. -/
theorem preimage_coordinateUnlinkExteriorPlanarNeckStarStrictCore_flowerHomeomorph
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m ⁻¹'
        coordinateUnlinkExteriorPlanarNeckStarStrictCore m =
      coordinateUnlinkExteriorPlanarNeckTransportHomeomorph m ⁻¹'
        coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m := by
  ext x
  exact
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar_mem_strictCore_iff
      m x

/-- Exact strict-core membership for a normalized left annulus after transport to the star. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckStar_normalizedLeft_mem_strictCore_iff
    (m : ℕ) [NeZero m] (a : ZMod m) (u : Sphere 1)
    (t : Set.Icc (0 : ℝ) 1) (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarNormalizedLeftFlowerPoint m a u t, s)) ∈
        coordinateUnlinkExteriorPlanarNeckStarStrictCore m ↔
      0 < (t : ℝ) := by
  rw [
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar_mem_strictCore_iff,
    coordinateUnlinkExteriorPlanarNeckTransport_normalizedLeft_mem_strict_iff]

/-- Exact strict-core membership for the normalized right annulus after transport to the star. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarNeckStar_normalizedRight_mem_strictCore_iff
    (m : ℕ) [NeZero m] (u : Sphere 1) (t : Set.Icc (0 : ℝ) 1)
    (s : Sphere 2) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
        (partialSphereSpinInr
          (coordinateUnlinkExteriorPlanarFlowerOuter m)
          (coordinateUnlinkExteriorPlanarNormalizedRightFlowerPoint m u t, s)) ∈
        coordinateUnlinkExteriorPlanarNeckStarStrictCore m ↔
      0 < (t : ℝ) := by
  rw [
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar_mem_strictCore_iff,
    coordinateUnlinkExteriorPlanarNeckTransport_normalizedRight_mem_strict_iff]

/-- The whole one-handle face maps into the transported strict core of the neck star. -/
theorem coordinateUnlinkExteriorPlanarNeckStar_oneHandle_mem_strictCore
    (m : ℕ) [NeZero m] (x : OneHandlePiece) :
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar m
        (partialSphereSpinInl
          (coordinateUnlinkExteriorPlanarFlowerOuter m) x) ∈
      coordinateUnlinkExteriorPlanarNeckStarStrictCore m := by
  rw [
    coordinateUnlinkExteriorPlanarFlowerPartialSphereSpinHomeomorphNeckStar_mem_strictCore_iff]
  exact coordinateUnlinkExteriorPlanarNeckTransport_oneHandle_mem_strict m x

end SplittingSpheres
