/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarOuterSector

/-!
# Labelled right sectors of the retained planar outer circle

The right semicircle of the polynomial outer boundary is parametrized explicitly from the
lower neck endpoint to the upper neck endpoint.  We lift that path through the punctured
complex power covering, starting at the selected lower neck lift, and take all of its `ZMod m`
deck translates.  These translated paths are pairwise disjoint and exhaust exactly the right
part of the retained outer circle.

The selected lift can end on a different sheet at the upper endpoint.  Rather than imposing an
orientation convention, this file defines the unique endpoint offset
`coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m`.  Thus the sector labelled `a`
connects lower endpoint `a` to upper endpoint
`a + coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m`.  Addition by this offset is
proved bijective; no claim that the offset equals `1` is made.

All results are point-set topology.  There is no cyclic-order, orientation, surface
classification, or smoothness assertion.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped unitInterval

namespace SplittingSpheres

/-! ## The downstairs right polynomial semicircle -/

/-- The vertical coordinate of the right polynomial outer semicircle. -/
def coordinateUnlinkExteriorPlanarBaseRightOuterArcVertical
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) : ℝ :=
  sphereHandleRadius * (2 * (t : ℝ) - 1)

/-- The nonnegative horizontal coordinate of the right polynomial outer semicircle. -/
def coordinateUnlinkExteriorPlanarBaseRightOuterArcHorizontal
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) : ℝ :=
  Real.sqrt (sphereHandleRadius ^ 2 -
    coordinateUnlinkExteriorPlanarBaseRightOuterArcVertical t ^ 2)

/-- The right semicircle of the polynomial outer boundary, from lower to upper neck endpoint. -/
def coordinateUnlinkExteriorPlanarBaseRightOuterArc
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) : ℂ :=
  (-1 / 2 : ℂ) +
    (coordinateUnlinkExteriorPlanarBaseRightOuterArcHorizontal t : ℂ) +
      (coordinateUnlinkExteriorPlanarBaseRightOuterArcVertical t : ℂ) * Complex.I

theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_vertical_sq_le
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarBaseRightOuterArcVertical t ^ 2 ≤
      sphereHandleRadius ^ 2 := by
  have hk : (2 * (t : ℝ) - 1) ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).2
      (abs_two_mul_sub_one_le_one_on_neckInterval t)
  unfold coordinateUnlinkExteriorPlanarBaseRightOuterArcVertical
  nlinarith [sq_nonneg sphereHandleRadius]

theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_horizontal_sq
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarBaseRightOuterArcHorizontal t ^ 2 =
      sphereHandleRadius ^ 2 -
        coordinateUnlinkExteriorPlanarBaseRightOuterArcVertical t ^ 2 := by
  rw [coordinateUnlinkExteriorPlanarBaseRightOuterArcHorizontal, Real.sq_sqrt]
  exact sub_nonneg.mpr
    (coordinateUnlinkExteriorPlanarBaseRightOuterArc_vertical_sq_le t)

theorem continuous_coordinateUnlinkExteriorPlanarBaseRightOuterArc :
    Continuous coordinateUnlinkExteriorPlanarBaseRightOuterArc := by
  unfold coordinateUnlinkExteriorPlanarBaseRightOuterArc
    coordinateUnlinkExteriorPlanarBaseRightOuterArcHorizontal
    coordinateUnlinkExteriorPlanarBaseRightOuterArcVertical
  fun_prop

theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_horizontal_nonneg
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    0 ≤ coordinateUnlinkExteriorPlanarBaseRightOuterArcHorizontal t :=
  Real.sqrt_nonneg _

@[simp]
theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_re
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarBaseRightOuterArc t).re =
      -1 / 2 + coordinateUnlinkExteriorPlanarBaseRightOuterArcHorizontal t := by
  norm_num [coordinateUnlinkExteriorPlanarBaseRightOuterArc, Complex.mul_re]

@[simp]
theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_im
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarBaseRightOuterArc t).im =
      coordinateUnlinkExteriorPlanarBaseRightOuterArcVertical t := by
  norm_num [coordinateUnlinkExteriorPlanarBaseRightOuterArc, Complex.mul_im]

theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_re_ge
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    -1 / 2 ≤ (coordinateUnlinkExteriorPlanarBaseRightOuterArc t).re := by
  rw [coordinateUnlinkExteriorPlanarBaseRightOuterArc_re]
  exact le_add_of_nonneg_right
    (coordinateUnlinkExteriorPlanarBaseRightOuterArc_horizontal_nonneg t)

theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_add_half_norm
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    ‖coordinateUnlinkExteriorPlanarBaseRightOuterArc t + (1 / 2 : ℂ)‖ =
      sphereHandleRadius := by
  rw [← sq_eq_sq₀ (norm_nonneg _) sphereHandleRadius_pos.le,
    Complex.sq_norm, Complex.normSq_apply]
  norm_num [coordinateUnlinkExteriorPlanarBaseRightOuterArc, Complex.mul_re,
    Complex.mul_im]
  nlinarith [coordinateUnlinkExteriorPlanarBaseRightOuterArc_horizontal_sq t,
    sphereHandleRadius_sq]

@[simp]
theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_vertical_zero :
    coordinateUnlinkExteriorPlanarBaseRightOuterArcVertical 0 =
      -sphereHandleRadius := by
  simp [coordinateUnlinkExteriorPlanarBaseRightOuterArcVertical]

@[simp]
theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_vertical_one :
    coordinateUnlinkExteriorPlanarBaseRightOuterArcVertical 1 =
      sphereHandleRadius := by
  simp [coordinateUnlinkExteriorPlanarBaseRightOuterArcVertical]
  ring

@[simp]
theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_horizontal_zero :
    coordinateUnlinkExteriorPlanarBaseRightOuterArcHorizontal 0 = 0 := by
  rw [coordinateUnlinkExteriorPlanarBaseRightOuterArcHorizontal,
    coordinateUnlinkExteriorPlanarBaseRightOuterArc_vertical_zero]
  simp

@[simp]
theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_horizontal_one :
    coordinateUnlinkExteriorPlanarBaseRightOuterArcHorizontal 1 = 0 := by
  rw [coordinateUnlinkExteriorPlanarBaseRightOuterArcHorizontal,
    coordinateUnlinkExteriorPlanarBaseRightOuterArc_vertical_one]
  simp

@[simp]
theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_zero :
    coordinateUnlinkExteriorPlanarBaseRightOuterArc 0 =
      coordinateUnlinkExteriorPlanarNeckBaseArc 0 := by
  rw [coordinateUnlinkExteriorPlanarNeckBaseArc_zero]
  simp [coordinateUnlinkExteriorPlanarBaseRightOuterArc]
  ring

@[simp]
theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_one :
    coordinateUnlinkExteriorPlanarBaseRightOuterArc 1 =
      coordinateUnlinkExteriorPlanarNeckBaseArc 1 := by
  rw [coordinateUnlinkExteriorPlanarNeckBaseArc_one]
  simp [coordinateUnlinkExteriorPlanarBaseRightOuterArc]

theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_norm_ge
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (1 / 8 : ℝ) ≤ ‖coordinateUnlinkExteriorPlanarBaseRightOuterArc t‖ := by
  have htri := norm_add_le
    (coordinateUnlinkExteriorPlanarBaseRightOuterArc t) (1 / 2 : ℂ)
  rw [coordinateUnlinkExteriorPlanarBaseRightOuterArc_add_half_norm] at htri
  norm_num at htri
  linarith [sphereHandleRadius_sub_half_gt_oneEighth]

theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_add_one_norm_ge
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (1 / 8 : ℝ) ≤ ‖coordinateUnlinkExteriorPlanarBaseRightOuterArc t + 1‖ := by
  have htri := norm_add_le
    (coordinateUnlinkExteriorPlanarBaseRightOuterArc t + 1) (-1 / 2 : ℂ)
  have hadd : coordinateUnlinkExteriorPlanarBaseRightOuterArc t + 1 + (-1 / 2 : ℂ) =
      coordinateUnlinkExteriorPlanarBaseRightOuterArc t + (1 / 2 : ℂ) := by ring
  rw [hadd, coordinateUnlinkExteriorPlanarBaseRightOuterArc_add_half_norm] at htri
  norm_num at htri
  linarith [sphereHandleRadius_sub_half_gt_oneEighth]

theorem coordinateUnlinkExteriorPlanarBaseRightOuterArc_ne_zero
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    coordinateUnlinkExteriorPlanarBaseRightOuterArc t ≠ 0 := by
  intro h
  have hnorm := coordinateUnlinkExteriorPlanarBaseRightOuterArc_norm_ge t
  rw [h, norm_zero] at hnorm
  norm_num at hnorm

theorem injective_coordinateUnlinkExteriorPlanarBaseRightOuterArc :
    Injective coordinateUnlinkExteriorPlanarBaseRightOuterArc := by
  intro t s h
  apply Subtype.ext
  have him := congrArg Complex.im h
  rw [coordinateUnlinkExteriorPlanarBaseRightOuterArc_im,
    coordinateUnlinkExteriorPlanarBaseRightOuterArc_im] at him
  unfold coordinateUnlinkExteriorPlanarBaseRightOuterArcVertical at him
  nlinarith [sphereHandleRadius_pos]

/-- The literal right half of the downstairs polynomial outer circle. -/
def coordinateUnlinkExteriorPlanarBaseRightOuterArcSet : Set ℂ :=
  {w | ‖w + (1 / 2 : ℂ)‖ = sphereHandleRadius ∧ -1 / 2 ≤ w.re}

/-- The explicit square-root graph parametrizes the whole right polynomial semicircle. -/
theorem range_coordinateUnlinkExteriorPlanarBaseRightOuterArc :
    range coordinateUnlinkExteriorPlanarBaseRightOuterArc =
      coordinateUnlinkExteriorPlanarBaseRightOuterArcSet := by
  ext w
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨coordinateUnlinkExteriorPlanarBaseRightOuterArc_add_half_norm t,
      coordinateUnlinkExteriorPlanarBaseRightOuterArc_re_ge t⟩
  · rintro ⟨hcircle, hre⟩
    have himAbs : |w.im| ≤ sphereHandleRadius := by
      calc
        |w.im| = |(w + (1 / 2 : ℂ)).im| := by norm_num
        _ ≤ ‖w + (1 / 2 : ℂ)‖ := Complex.abs_im_le_norm _
        _ = sphereHandleRadius := hcircle
    have himLower : -sphereHandleRadius ≤ w.im := (abs_le.mp himAbs).1
    have himUpper : w.im ≤ sphereHandleRadius := (abs_le.mp himAbs).2
    let tr : ℝ := (w.im / sphereHandleRadius + 1) / 2
    have ht0 : 0 ≤ tr := by
      dsimp only [tr]
      have hdiv : -1 ≤ w.im / sphereHandleRadius := by
        rw [le_div_iff₀ sphereHandleRadius_pos]
        nlinarith
      linarith
    have ht1 : tr ≤ 1 := by
      dsimp only [tr]
      have hdiv : w.im / sphereHandleRadius ≤ 1 := by
        rw [div_le_iff₀ sphereHandleRadius_pos]
        nlinarith
      linarith
    let t : CoordinateUnlinkExteriorPlanarNeckInterval := ⟨tr, ht0, ht1⟩
    have hy : coordinateUnlinkExteriorPlanarBaseRightOuterArcVertical t = w.im := by
      unfold coordinateUnlinkExteriorPlanarBaseRightOuterArcVertical
      dsimp only [t, tr]
      field_simp [sphereHandleRadius_ne_zero]
      ring
    have hsq : (w.re + 1 / 2) ^ 2 + w.im ^ 2 = sphereHandleRadius ^ 2 := by
      have h := congrArg (fun x : ℝ ↦ x ^ 2) hcircle
      rw [Complex.sq_norm, Complex.normSq_apply] at h
      norm_num at h
      nlinarith [sphereHandleRadius_sq]
    have hx : coordinateUnlinkExteriorPlanarBaseRightOuterArcHorizontal t =
        w.re + 1 / 2 := by
      have hx2 := coordinateUnlinkExteriorPlanarBaseRightOuterArc_horizontal_sq t
      rw [hy] at hx2
      nlinarith [coordinateUnlinkExteriorPlanarBaseRightOuterArc_horizontal_nonneg t]
    refine ⟨t, ?_⟩
    apply Complex.ext
    · rw [coordinateUnlinkExteriorPlanarBaseRightOuterArc_re, hx]
      ring
    · rw [coordinateUnlinkExteriorPlanarBaseRightOuterArc_im, hy]

/-! ## The selected covering lift -/

/-- The right polynomial semicircle as a path in the punctured complex plane. -/
def coordinateUnlinkExteriorPlanarBaseRightOuterPath :
    C(I, {z : ℂ // z ≠ 0}) where
  toFun t := ⟨coordinateUnlinkExteriorPlanarBaseRightOuterArc t,
    coordinateUnlinkExteriorPlanarBaseRightOuterArc_ne_zero t⟩
  continuous_toFun :=
    continuous_coordinateUnlinkExteriorPlanarBaseRightOuterArc.subtype_mk _

/-- The selected lower neck root, used as the initial point of the right lift. -/
def coordinateUnlinkExteriorPlanarBaseRightOuterLiftStart
    (m : ℕ) [NeZero m] : {z : ℂ // z ≠ 0} :=
  (coordinateUnlinkExteriorPlanarNeckArc m 0).1

theorem coordinateUnlinkExteriorPlanarBaseRightOuterPath_zero
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarBaseRightOuterPath 0 =
      nonzeroComplexPow m
        (coordinateUnlinkExteriorPlanarBaseRightOuterLiftStart m) := by
  apply Subtype.ext
  rw [nonzeroComplexPow_coe,
    coordinateUnlinkExteriorPlanarBaseRightOuterLiftStart,
    coordinateUnlinkExteriorPlanarNeckArc_pow]
  exact coordinateUnlinkExteriorPlanarBaseRightOuterArc_zero

/-- The canonical path lift of the right polynomial semicircle starting at lower label `0`. -/
def coordinateUnlinkExteriorPlanarBaseRightOuterLift
    (m : ℕ) [NeZero m] : C(I, {z : ℂ // z ≠ 0}) :=
  (isCoveringMap_nonzeroComplexPow m).liftPath
    coordinateUnlinkExteriorPlanarBaseRightOuterPath
    (coordinateUnlinkExteriorPlanarBaseRightOuterLiftStart m)
    (coordinateUnlinkExteriorPlanarBaseRightOuterPath_zero m)

@[simp]
theorem coordinateUnlinkExteriorPlanarBaseRightOuterLift_pow
    (m : ℕ) [NeZero m]
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarBaseRightOuterLift m t : ℂ) ^ m =
      coordinateUnlinkExteriorPlanarBaseRightOuterArc t := by
  have h := congr_fun
    ((isCoveringMap_nonzeroComplexPow m).liftPath_lifts
      coordinateUnlinkExteriorPlanarBaseRightOuterPath
      (coordinateUnlinkExteriorPlanarBaseRightOuterLiftStart m)
      (coordinateUnlinkExteriorPlanarBaseRightOuterPath_zero m)) t
  exact congrArg Subtype.val h

@[simp]
theorem coordinateUnlinkExteriorPlanarBaseRightOuterLift_zero
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarBaseRightOuterLift m 0 =
      coordinateUnlinkExteriorPlanarBaseRightOuterLiftStart m :=
  (isCoveringMap_nonzeroComplexPow m).liftPath_zero _ _ _

/-- The selected right outer arc, bundled in the planar flower. -/
def coordinateUnlinkExteriorPlanarFlowerRightOuterArc
    (m : ℕ) [NeZero m]
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    CoordinateUnlinkExteriorPlanarFlower m :=
  ⟨coordinateUnlinkExteriorPlanarBaseRightOuterLift m t, by
    rw [mem_coordinateUnlinkExteriorPlanarFlowerSet_iff,
      coordinateUnlinkExteriorPlanarBaseRightOuterLift_pow]
    exact ⟨coordinateUnlinkExteriorPlanarBaseRightOuterArc_add_half_norm t |>.le,
      coordinateUnlinkExteriorPlanarBaseRightOuterArc_norm_ge t,
      coordinateUnlinkExteriorPlanarBaseRightOuterArc_add_one_norm_ge t⟩⟩

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerRightOuterArc_pow
    (m : ℕ) [NeZero m]
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarFlowerRightOuterArc m t).1.1 ^ m =
      coordinateUnlinkExteriorPlanarBaseRightOuterArc t :=
  coordinateUnlinkExteriorPlanarBaseRightOuterLift_pow m t

theorem continuous_coordinateUnlinkExteriorPlanarFlowerRightOuterArc
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorPlanarFlowerRightOuterArc m) := by
  apply Continuous.subtype_mk
  exact (coordinateUnlinkExteriorPlanarBaseRightOuterLift m).continuous

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerRightOuterArc_zero
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFlowerRightOuterArc m 0 =
      coordinateUnlinkExteriorPlanarNeckArc m 0 := by
  apply Subtype.ext
  exact coordinateUnlinkExteriorPlanarBaseRightOuterLift_zero m

/-! ## Fiber transitivity and the endpoint offset -/

/-- Two flower points with the same polynomial power differ by a unique `ZMod m` deck map. -/
theorem existsUnique_coordinateUnlinkExteriorPlanarFlowerDeckZMod_eq
    (m : ℕ) [NeZero m]
    (z w : CoordinateUnlinkExteriorPlanarFlower m)
    (hpow : z.1.1 ^ m = w.1.1 ^ m) :
    ∃! a : ZMod m,
      coordinateUnlinkExteriorPlanarFlowerDeckMap m
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)) z = w := by
  let q : ℂˣ := Units.mk0 (w.1.1 / z.1.1) (div_ne_zero w.1.2 z.1.2)
  have hqpow : (q : ℂ) ^ m = 1 := by
    change (w.1.1 / z.1.1) ^ m = 1
    rw [div_pow, ← hpow, div_self (pow_ne_zero m z.1.2)]
  let u : rootsOfUnity m ℂ :=
    ⟨q, (mem_rootsOfUnity' m q).mpr hqpow⟩
  let a : Multiplicative (ZMod m) :=
    (standardRootsOfUnityZModMulEquiv m).symm u
  have ha :
      coordinateUnlinkExteriorPlanarFlowerDeckMap m
          (standardRootsOfUnityZModMulEquiv m a) z = w := by
    apply Subtype.ext
    apply Subtype.ext
    change (((standardRootsOfUnityZModMulEquiv m a).1 : ℂˣ) : ℂ) * z.1.1 = w.1.1
    rw [(standardRootsOfUnityZModMulEquiv m).apply_symm_apply]
    exact div_mul_cancel₀ w.1.1 z.1.2
  refine ⟨a.toAdd, ha, ?_⟩
  intro b hb
  apply Multiplicative.ofAdd.injective
  apply (standardRootsOfUnityZModMulEquiv m).injective
  change standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd b) =
    standardRootsOfUnityZModMulEquiv m a
  apply Subtype.ext
  apply Units.ext
  apply mul_right_cancel₀ z.1.2
  have hbval := congrArg
    (fun p : CoordinateUnlinkExteriorPlanarFlower m ↦ p.1.1) hb
  have haval := congrArg
    (fun p : CoordinateUnlinkExteriorPlanarFlower m ↦ p.1.1) ha
  exact hbval.trans haval.symm

/-- The unique upper sheet reached by the selected right lift starting at lower label `0`. -/
def coordinateUnlinkExteriorPlanarRightOuterEndpointOffset
    (m : ℕ) [NeZero m] : ZMod m :=
  Classical.choose <| existsUnique_coordinateUnlinkExteriorPlanarFlowerDeckZMod_eq m
    (coordinateUnlinkExteriorPlanarNeckArc m 1)
    (coordinateUnlinkExteriorPlanarFlowerRightOuterArc m 1) <| by
      rw [coordinateUnlinkExteriorPlanarNeckArc_pow,
        coordinateUnlinkExteriorPlanarFlowerRightOuterArc_pow,
        coordinateUnlinkExteriorPlanarBaseRightOuterArc_one]

theorem coordinateUnlinkExteriorPlanarRightOuterEndpointOffset_spec
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarFlowerDeckMap m
        (standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd
            (coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m)))
        (coordinateUnlinkExteriorPlanarNeckArc m 1) =
      coordinateUnlinkExteriorPlanarFlowerRightOuterArc m 1 :=
  (Classical.choose_spec <|
    existsUnique_coordinateUnlinkExteriorPlanarFlowerDeckZMod_eq m
      (coordinateUnlinkExteriorPlanarNeckArc m 1)
      (coordinateUnlinkExteriorPlanarFlowerRightOuterArc m 1) <| by
        rw [coordinateUnlinkExteriorPlanarNeckArc_pow,
          coordinateUnlinkExteriorPlanarFlowerRightOuterArc_pow,
          coordinateUnlinkExteriorPlanarBaseRightOuterArc_one]).1

/-- Whatever the selected offset is, adding it permutes the sheet labels. -/
theorem bijective_add_coordinateUnlinkExteriorPlanarRightOuterEndpointOffset
    (m : ℕ) [NeZero m] :
    Bijective (fun a : ZMod m ↦
      a + coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m) := by
  constructor
  · intro a b h
    exact add_right_cancel h
  · intro b
    refine ⟨b - coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m, ?_⟩
    exact sub_add_cancel _ _

/-! ## Labelled right sectors -/

/-- The deck translate with label `a` of the selected right outer arc. -/
def coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    C(CoordinateUnlinkExteriorPlanarNeckInterval,
      CoordinateUnlinkExteriorPlanarFlower m) where
  toFun t := coordinateUnlinkExteriorPlanarFlowerDeckMap m
    (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a))
    (coordinateUnlinkExteriorPlanarFlowerRightOuterArc m t)
  continuous_toFun :=
    (continuous_coordinateUnlinkExteriorPlanarFlowerDeckMap m _).comp
      (continuous_coordinateUnlinkExteriorPlanarFlowerRightOuterArc m)

/-- The range of one labelled right outer sector. -/
def coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Set (CoordinateUnlinkExteriorPlanarFlower m) :=
  range (coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m a)

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_pow
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m a t).1.1 ^ m =
      coordinateUnlinkExteriorPlanarBaseRightOuterArc t := by
  change (coordinateUnlinkExteriorPlanarFlowerDeckMap m
    (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a))
    (coordinateUnlinkExteriorPlanarFlowerRightOuterArc m t)).1.1 ^ m = _
  rw [coordinateUnlinkExteriorPlanarFlowerDeckMap_val, mul_pow,
    (mem_rootsOfUnity' m
      (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).1).mp
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).2,
    one_mul, coordinateUnlinkExteriorPlanarFlowerRightOuterArc_pow]

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_zero
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m a 0 =
      coordinateUnlinkExteriorPlanarNeckArcTranslate m a 0 := by
  change coordinateUnlinkExteriorPlanarFlowerDeckMap m
    (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a))
    (coordinateUnlinkExteriorPlanarFlowerRightOuterArc m 0) = _
  rw [coordinateUnlinkExteriorPlanarFlowerRightOuterArc_zero]
  rfl

/-- The upper endpoint has the same label translated by the canonical, unspecified offset. -/
@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_one
    (m : ℕ) [NeZero m] (a : ZMod m) :
    coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m a 1 =
      coordinateUnlinkExteriorPlanarNeckArcTranslate m
        (a + coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m) 1 := by
  change coordinateUnlinkExteriorPlanarFlowerDeckMap m
      (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a))
      (coordinateUnlinkExteriorPlanarFlowerRightOuterArc m 1) = _
  rw [← coordinateUnlinkExteriorPlanarRightOuterEndpointOffset_spec m]
  exact coordinateUnlinkExteriorPlanarNeckArcTranslate_add m a
    (coordinateUnlinkExteriorPlanarRightOuterEndpointOffset m) 1

theorem injective_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorFamily
    (m : ℕ) [NeZero m] :
    Injective (fun x : ZMod m × CoordinateUnlinkExteriorPlanarNeckInterval ↦
      coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m x.1 x.2) := by
  rintro ⟨a, t⟩ ⟨b, s⟩ h
  have hp := congrArg
    (fun z : CoordinateUnlinkExteriorPlanarFlower m ↦ z.1.1 ^ m) h
  have hts : t = s := injective_coordinateUnlinkExteriorPlanarBaseRightOuterArc <| by
    simpa only [coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_pow] using hp
  subst s
  have hval := congrArg
    (fun z : CoordinateUnlinkExteriorPlanarFlower m ↦ z.1.1) h
  have hroot :
      (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) =
        (((standardRootsOfUnityZModMulEquiv m
          (Multiplicative.ofAdd b)).1 : ℂˣ) : ℂ) := by
    apply mul_right_cancel₀
      (coordinateUnlinkExteriorPlanarFlowerRightOuterArc m t).1.2
    exact hval
  have hroots : standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a) =
      standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd b) := by
    apply Subtype.ext
    apply Units.ext
    exact hroot
  have hab : a = b := Multiplicative.ofAdd.injective <|
    (standardRootsOfUnityZModMulEquiv m).injective hroots
  exact Prod.ext hab rfl

theorem injective_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap
    (m : ℕ) [NeZero m] (a : ZMod m) :
    Injective (coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m a) := by
  intro t s h
  have hp : (a, t) = (a, s) :=
    injective_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorFamily m h
  exact congrArg Prod.snd hp

/-- Each labelled right sector is genuinely a closed interval. -/
def coordinateUnlinkExteriorPlanarFlowerRightOuterSectorHomeomorph
    (m : ℕ) [NeZero m] (a : ZMod m) :
    CoordinateUnlinkExteriorPlanarNeckInterval ≃ₜ
      ↑(coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet m a) :=
  ((coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m a).continuous
    |>.isClosedEmbedding
      (injective_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m a))
    |>.isEmbedding.toHomeomorph

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerRightOuterSectorHomeomorph_apply_coe
    (m : ℕ) [NeZero m] (a : ZMod m)
    (t : CoordinateUnlinkExteriorPlanarNeckInterval) :
    (coordinateUnlinkExteriorPlanarFlowerRightOuterSectorHomeomorph m a t :
        CoordinateUnlinkExteriorPlanarFlower m) =
      coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m a t :=
  rfl

/-- Distinct labels give disjoint closed right sectors, including their endpoints. -/
theorem pairwise_disjoint_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet
    (m : ℕ) [NeZero m] :
    Pairwise fun a b : ZMod m ↦
      Disjoint (coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet m a)
        (coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet m b) := by
  intro a b hab
  rw [Set.disjoint_left]
  rintro z ⟨t, rfl⟩ ⟨s, hs⟩
  apply hab
  have hp : (a, t) = (b, s) :=
    injective_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorFamily m hs.symm
  exact congrArg Prod.fst hp

/-! ## Exact coverage -/

/-- The part of the retained outer locus lying over the closed right polynomial half. -/
def coordinateUnlinkExteriorPlanarRetainedOuterRightSet
    (m : ℕ) : Set (CoordinateUnlinkExteriorPlanarFlower m) :=
  coordinateUnlinkExteriorPlanarRetainedOuterSet m ∩
    coordinateUnlinkExteriorPlanarFlowerRightHalfSet m

/-- The labelled right sectors exhaust exactly the right part of the retained outer circle. -/
theorem iUnion_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet
    (m : ℕ) [NeZero m] :
    (⋃ a : ZMod m,
      coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet m a) =
        coordinateUnlinkExteriorPlanarRetainedOuterRightSet m := by
  ext z
  constructor
  · intro hz
    rw [mem_iUnion] at hz
    obtain ⟨a, t, rfl⟩ := hz
    constructor
    · change ‖(coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap
          m a t).1.1 ^ m + (1 / 2 : ℂ)‖ = sphereHandleRadius
      rw [coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_pow,
        coordinateUnlinkExteriorPlanarBaseRightOuterArc_add_half_norm]
    · change -1 / 2 ≤
        ((coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap m a t).1.1 ^ m).re
      rw [coordinateUnlinkExteriorPlanarFlowerRightOuterSectorMap_pow]
      exact coordinateUnlinkExteriorPlanarBaseRightOuterArc_re_ge t
  · rintro ⟨hzouter, hzright⟩
    have hw : z.1.1 ^ m ∈ coordinateUnlinkExteriorPlanarBaseRightOuterArcSet :=
      ⟨hzouter, hzright⟩
    rw [← range_coordinateUnlinkExteriorPlanarBaseRightOuterArc] at hw
    obtain ⟨t, ht⟩ := hw
    obtain ⟨a, ha, -⟩ :=
      existsUnique_coordinateUnlinkExteriorPlanarFlowerDeckZMod_eq m
        (coordinateUnlinkExteriorPlanarFlowerRightOuterArc m t) z <| by
          rw [coordinateUnlinkExteriorPlanarFlowerRightOuterArc_pow, ht]
    rw [mem_iUnion]
    exact ⟨a, t, ha⟩

/-- The left and right labelled sectors together cover the complete retained outer circle. -/
theorem coordinateUnlinkExteriorPlanarFlowerOuterSector_cover
    (m : ℕ) [NeZero m] :
    (⋃ a : ZMod m,
        coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorSet m a) ∪
      (⋃ a : ZMod m,
        coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet m a) =
      coordinateUnlinkExteriorPlanarRetainedOuterSet m := by
  rw [iUnion_coordinateUnlinkExteriorPlanarFlowerLeftOuterSectorSet,
    iUnion_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet]
  ext z
  constructor
  · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
  · intro hz
    rcases le_total (z.1.1 ^ m).re (-1 / 2) with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩

/-! ## Low-degree elaboration checks -/

example :
    (⋃ a : ZMod 1,
      coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet 1 a) =
      coordinateUnlinkExteriorPlanarRetainedOuterRightSet 1 :=
  iUnion_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet 1

example :
    Disjoint (coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet 2 0)
      (coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet 2 1) :=
  pairwise_disjoint_coordinateUnlinkExteriorPlanarFlowerRightOuterSectorSet 2 (by norm_num)

end SplittingSpheres
