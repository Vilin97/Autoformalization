/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.CoordinateUnlinkExteriorCommonModelSphere
public import SplittingSpheres.Geometry.UnlinkEquatorPowerCollar
import SplittingSpheres.Foundations.LocalDiffeomorphismRecognition
import SplittingSpheres.Foundations.SmoothRadialCompression
import SplittingSpheres.Foundations.SplitDerivativeImmersion
import SplittingSpheres.Geometry.EuclideanFourBallSmoothCollar
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# A smooth rounded Euclidean four-ball in the coordinate sphere

This file constructs a direct smooth closed hemisphere in the four-sphere, modeled on the common
coordinate-unlink exterior model. A smooth radial profile maps the Euclidean four-ball onto the
closed negative coordinate cap. Near its boundary the profile agrees exactly with the existing
sphere equator collar, with inward ball time sent to negative signed collar time.

The cap atlas is built directly from its open interior and this boundary collar. The resulting
ball-to-cap map is a genuine diffeomorphism, and the model boundary is exactly the equator. No
atlas is transported through an unrelated homeomorphism, and no capping pushout or handlebody
recognition is asserted here.
-/

open Function Metric Set Topology TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

def roundedHemisphereRationalHeight (r : ℝ) : ℝ :=
  (1 - r ^ 2) / (1 + r ^ 2)

def roundedHemisphereLinearHeight (r : ℝ) : ℝ :=
  1 - r

def roundedHemisphereWeight : ℝ → ℝ :=
  Real.smoothTransition ∘ fun r : ℝ ↦ 4 * r - 1

def roundedHemisphereHeight : ℝ → ℝ :=
  roundedHemisphereRationalHeight +
    roundedHemisphereWeight *
      (roundedHemisphereLinearHeight - roundedHemisphereRationalHeight)

theorem roundedHemisphereRationalHeight_contDiff :
    ContDiff ℝ ∞ roundedHemisphereRationalHeight := by
  unfold roundedHemisphereRationalHeight
  exact (contDiff_const.sub (contDiff_id.pow 2)).div
    (contDiff_const.add (contDiff_id.pow 2)) (fun r ↦ by
      exact ne_of_gt (by nlinarith [sq_nonneg r]))

theorem roundedHemisphereLinearHeight_contDiff :
    ContDiff ℝ ∞ roundedHemisphereLinearHeight := by
  unfold roundedHemisphereLinearHeight
  exact contDiff_const.sub contDiff_id

theorem roundedHemisphereWeight_contDiff :
    ContDiff ℝ ∞ roundedHemisphereWeight := by
  unfold roundedHemisphereWeight
  exact Real.smoothTransition.contDiff.comp <|
    (contDiff_const.mul contDiff_id).sub contDiff_const

theorem roundedHemisphereHeight_contDiff :
    ContDiff ℝ ∞ roundedHemisphereHeight := by
  unfold roundedHemisphereHeight
  exact roundedHemisphereRationalHeight_contDiff.add
    (roundedHemisphereWeight_contDiff.mul
      (roundedHemisphereLinearHeight_contDiff.sub
        roundedHemisphereRationalHeight_contDiff))

theorem roundedHemisphereHeight_eq_rational_of_le
    {r : ℝ} (hr : r ≤ 1 / 4) :
    roundedHemisphereHeight r = roundedHemisphereRationalHeight r := by
  have hw : roundedHemisphereWeight r = 0 := by
    rw [roundedHemisphereWeight, Function.comp_apply,
      Real.smoothTransition.zero_of_nonpos]
    linarith
  simp [roundedHemisphereHeight, hw]

theorem roundedHemisphereHeight_eq_linear_of_le
    {r : ℝ} (hr : 1 / 2 ≤ r) :
    roundedHemisphereHeight r = roundedHemisphereLinearHeight r := by
  have hw : roundedHemisphereWeight r = 1 := by
    rw [roundedHemisphereWeight, Function.comp_apply,
      Real.smoothTransition.one_of_one_le]
    linarith
  simp [roundedHemisphereHeight, hw]

@[simp] theorem roundedHemisphereHeight_zero :
    roundedHemisphereHeight 0 = 1 := by
  rw [roundedHemisphereHeight_eq_rational_of_le (by norm_num)]
  norm_num [roundedHemisphereRationalHeight]

@[simp] theorem roundedHemisphereHeight_one :
    roundedHemisphereHeight 1 = 0 := by
  rw [roundedHemisphereHeight_eq_linear_of_le (by norm_num)]
  norm_num [roundedHemisphereLinearHeight]

theorem roundedHemisphereRationalHeight_hasDerivAt (r : ℝ) :
    HasDerivAt roundedHemisphereRationalHeight
      (-4 * r / (1 + r ^ 2) ^ 2) r := by
  unfold roundedHemisphereRationalHeight
  have hden : 1 + r ^ 2 ≠ 0 := by positivity
  have hp := (hasDerivAt_id r).pow 2
  have hnum := hp.const_sub 1
  have hden' := hp.const_add 1
  have h := hnum.div hden' hden
  convert! h using 1
  simp only [Pi.pow_apply, id_eq]
  field_simp [hden]
  ring

theorem roundedHemisphereLinearHeight_hasDerivAt (r : ℝ) :
    HasDerivAt roundedHemisphereLinearHeight (-1) r := by
  unfold roundedHemisphereLinearHeight
  convert! (hasDerivAt_id r).const_sub 1 using 1

theorem roundedHemisphereWeight_hasDerivAt (r : ℝ) :
    HasDerivAt roundedHemisphereWeight
      (4 * deriv Real.smoothTransition (4 * r - 1)) r := by
  unfold roundedHemisphereWeight
  have hs : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (4 * r - 1)) (4 * r - 1) :=
    ((Real.smoothTransition.contDiffAt (n := (⊤ : ℕ∞))).differentiableAt
      (by simp)).hasDerivAt
  have hi : HasDerivAt (fun x : ℝ ↦ 4 * x - 1) 4 r := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id r).const_mul 4).sub_const 1
  convert! hs.comp r hi using 1
  exact mul_comm _ _

theorem roundedHemisphereHeight_hasDerivAt (r : ℝ) :
    HasDerivAt roundedHemisphereHeight
      ((-4 * r / (1 + r ^ 2) ^ 2) +
        ((4 * deriv Real.smoothTransition (4 * r - 1)) *
          ((roundedHemisphereLinearHeight -
            roundedHemisphereRationalHeight) r) +
        roundedHemisphereWeight r *
          (-1 - (-4 * r / (1 + r ^ 2) ^ 2)))) r := by
  unfold roundedHemisphereHeight
  have hw := roundedHemisphereWeight_hasDerivAt r
  have hq := roundedHemisphereRationalHeight_hasDerivAt r
  have hl := roundedHemisphereLinearHeight_hasDerivAt r
  exact hq.add (hw.mul (hl.sub hq))

theorem roundedHemisphereLinearHeight_sub_rational_nonpos
    {r : ℝ} (hr0 : 0 ≤ r) (_hr1 : r ≤ 1) :
    roundedHemisphereLinearHeight r - roundedHemisphereRationalHeight r ≤ 0 := by
  have hden : 0 < 1 + r ^ 2 := by positivity
  change (1 - r) - (1 - r ^ 2) / (1 + r ^ 2) ≤ 0
  rw [sub_nonpos, le_div_iff₀ hden]
  nlinarith [sq_nonneg r, sq_nonneg (1 - r)]

theorem roundedHemisphereHeight_deriv_neg
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    deriv roundedHemisphereHeight r < 0 := by
  rw [(roundedHemisphereHeight_hasDerivAt r).deriv]
  have hw0 : 0 ≤ roundedHemisphereWeight r :=
    Real.smoothTransition.nonneg _
  have hw1 : roundedHemisphereWeight r ≤ 1 :=
    Real.smoothTransition.le_one _
  have hq' : -4 * r / (1 + r ^ 2) ^ 2 < 0 := by
    apply div_neg_of_neg_of_pos
    · nlinarith
    · positivity
  have hwd : 0 ≤ 4 * deriv Real.smoothTransition (4 * r - 1) := by
    exact mul_nonneg (by norm_num) Real.smoothTransition.monotone.deriv_nonneg
  have hdiff : roundedHemisphereLinearHeight r -
      roundedHemisphereRationalHeight r ≤ 0 :=
    roundedHemisphereLinearHeight_sub_rational_nonpos hr0.le hr1.le
  have hmix :
      (-4 * r / (1 + r ^ 2) ^ 2) +
        roundedHemisphereWeight r *
          (-1 - (-4 * r / (1 + r ^ 2) ^ 2)) < 0 := by
    by_cases hw : roundedHemisphereWeight r = 1
    · simp [hw]
    · have hwlt : roundedHemisphereWeight r < 1 := lt_of_le_of_ne hw1 hw
      have hp : (1 - roundedHemisphereWeight r) *
          (-4 * r / (1 + r ^ 2) ^ 2) < 0 :=
        mul_neg_of_pos_of_neg (sub_pos.mpr hwlt) hq'
      have hn : -roundedHemisphereWeight r ≤ 0 := neg_nonpos.mpr hw0
      nlinarith
  have hlast :
      (4 * deriv Real.smoothTransition (4 * r - 1)) *
        (roundedHemisphereLinearHeight r -
          roundedHemisphereRationalHeight r) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hwd hdiff
  simp only [Pi.sub_apply] at ⊢
  linarith

theorem roundedHemisphereHeight_strictAntiOn :
    StrictAntiOn roundedHemisphereHeight (Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
  · exact roundedHemisphereHeight_contDiff.continuous.continuousOn
  · intro r hr
    rw [interior_Icc] at hr
    exact roundedHemisphereHeight_deriv_neg hr.1 hr.2

theorem roundedHemisphereHeight_mem_Icc
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    roundedHemisphereHeight r ∈ Icc (0 : ℝ) 1 := by
  constructor
  · have h := roundedHemisphereHeight_strictAntiOn.antitoneOn hr
      (show (1 : ℝ) ∈ Icc 0 1 by simp) hr.2
    simpa using h
  · have h := roundedHemisphereHeight_strictAntiOn.antitoneOn
      (show (0 : ℝ) ∈ Icc 0 1 by simp) hr hr.1
    simpa using h

theorem roundedHemisphereHeight_lt_one
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    roundedHemisphereHeight r < 1 := by
  have hr : r ∈ Icc (0 : ℝ) 1 := ⟨hr0.le, hr1⟩
  have h := roundedHemisphereHeight_strictAntiOn
    (show (0 : ℝ) ∈ Icc 0 1 by simp) hr hr0
  simpa using h

def roundedHemisphereTangentialRadius (r : ℝ) : ℝ :=
  Real.sqrt (1 - roundedHemisphereHeight r ^ 2)

theorem roundedHemisphereTangentialRadius_nonneg (r : ℝ) :
    0 ≤ roundedHemisphereTangentialRadius r :=
  Real.sqrt_nonneg _

theorem roundedHemisphereTangentialRadius_sq
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    roundedHemisphereTangentialRadius r ^ 2 =
      1 - roundedHemisphereHeight r ^ 2 := by
  rw [roundedHemisphereTangentialRadius, Real.sq_sqrt]
  have hh := roundedHemisphereHeight_mem_Icc ⟨hr0.le, hr1⟩
  have hlt := roundedHemisphereHeight_lt_one hr0 hr1
  rcases hh with ⟨hh0, hh1⟩
  nlinarith [sq_nonneg (roundedHemisphereHeight r)]

theorem roundedHemisphereTangentialRadius_eq_rational
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 4) :
    roundedHemisphereTangentialRadius r = 2 * r / (1 + r ^ 2) := by
  have hden : 0 < 1 + r ^ 2 := by positivity
  have hheight := roundedHemisphereHeight_eq_rational_of_le hr1
  rw [roundedHemisphereTangentialRadius, hheight,
    roundedHemisphereRationalHeight]
  have hid :
      1 - ((1 - r ^ 2) / (1 + r ^ 2)) ^ 2 =
        (2 * r / (1 + r ^ 2)) ^ 2 := by
    field_simp
    ring
  rw [hid, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  exact div_nonneg (mul_nonneg (by norm_num) hr0) hden.le

@[simp] theorem roundedHemisphereTangentialRadius_zero :
    roundedHemisphereTangentialRadius 0 = 0 := by
  simpa using roundedHemisphereTangentialRadius_eq_rational
    (r := (0 : ℝ)) (by norm_num) (by norm_num)

@[simp] theorem roundedHemisphereTangentialRadius_one :
    roundedHemisphereTangentialRadius 1 = 1 := by
  simp [roundedHemisphereTangentialRadius]

def roundedHemisphereTangentialCoefficient (r : ℝ) : ℝ :=
  if r = 0 then 2 else roundedHemisphereTangentialRadius r / r

theorem roundedHemisphereTangentialCoefficient_eq_rational
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 4) :
    roundedHemisphereTangentialCoefficient r = 2 / (1 + r ^ 2) := by
  by_cases hr : r = 0
  · subst r
    simp [roundedHemisphereTangentialCoefficient]
  · rw [roundedHemisphereTangentialCoefficient, ite_eq_right hr,
      roundedHemisphereTangentialRadius_eq_rational hr0 hr1]
    field_simp

theorem roundedHemisphereTangentialRadius_pos
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    0 < roundedHemisphereTangentialRadius r := by
  rw [roundedHemisphereTangentialRadius, Real.sqrt_pos]
  have hh := roundedHemisphereHeight_mem_Icc ⟨hr0.le, hr1⟩
  have hlt := roundedHemisphereHeight_lt_one hr0 hr1
  rcases hh with ⟨hh0, hh1⟩
  nlinarith [sq_nonneg (roundedHemisphereHeight r)]

theorem roundedHemisphereTangentialCoefficient_pos
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    0 < roundedHemisphereTangentialCoefficient r := by
  rw [roundedHemisphereTangentialCoefficient, ite_eq_right hr0.ne']
  exact div_pos (roundedHemisphereTangentialRadius_pos hr0 hr1) hr0

theorem roundedHemisphereTangentialCoefficient_mul
    {r : ℝ} (hr0 : 0 < r) :
    roundedHemisphereTangentialCoefficient r * r =
      roundedHemisphereTangentialRadius r := by
  rw [roundedHemisphereTangentialCoefficient, ite_eq_right hr0.ne']
  exact div_mul_cancel₀ _ hr0.ne'

theorem roundedHemisphereTangentialRadius_contDiffAt
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ContDiffAt ℝ ∞ roundedHemisphereTangentialRadius r := by
  unfold roundedHemisphereTangentialRadius
  apply (contDiffAt_const.sub (roundedHemisphereHeight_contDiff.contDiffAt.pow 2)).sqrt
  have hh := roundedHemisphereHeight_mem_Icc ⟨hr0.le, hr1⟩
  have hlt := roundedHemisphereHeight_lt_one hr0 hr1
  rcases hh with ⟨hh0, hh1⟩
  nlinarith [sq_nonneg (roundedHemisphereHeight r)]

theorem roundedHemisphereTangentialRadius_hasDerivAt
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    HasDerivAt roundedHemisphereTangentialRadius
      (-roundedHemisphereHeight r * deriv roundedHemisphereHeight r /
        roundedHemisphereTangentialRadius r) r := by
  have hh : HasDerivAt roundedHemisphereHeight
      (deriv roundedHemisphereHeight r) r :=
    (roundedHemisphereHeight_contDiff.contDiffAt.differentiableAt
      (by simp)).hasDerivAt
  have hinner : HasDerivAt
      (fun x : ℝ ↦ 1 - roundedHemisphereHeight x ^ 2)
      (-2 * roundedHemisphereHeight r * deriv roundedHemisphereHeight r) r := by
    convert! (hasDerivAt_const r 1).sub (hh.pow 2) using 1
    ring
  have hne : 1 - roundedHemisphereHeight r ^ 2 ≠ 0 := by
    have hh0 := (roundedHemisphereHeight_mem_Icc ⟨hr0.le, hr1.le⟩).1
    have hh1 := roundedHemisphereHeight_lt_one hr0 hr1.le
    nlinarith [sq_nonneg (roundedHemisphereHeight r)]
  have hs := hinner.sqrt hne
  convert! hs using 1
  rw [roundedHemisphereTangentialRadius]
  have hsqrt : Real.sqrt (1 - roundedHemisphereHeight r ^ 2) ≠ 0 :=
    (roundedHemisphereTangentialRadius_pos hr0 hr1.le).ne'
  field_simp [hsqrt]

theorem roundedHemisphereTangentialRadius_deriv_pos
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < deriv roundedHemisphereTangentialRadius r := by
  rw [(roundedHemisphereTangentialRadius_hasDerivAt hr0 hr1).deriv]
  apply div_pos
  · have hhpos : 0 < roundedHemisphereHeight r := by
      have h := roundedHemisphereHeight_strictAntiOn
        ⟨hr0.le, hr1.le⟩ (show (1 : ℝ) ∈ Icc 0 1 by simp) hr1
      simpa using h
    have hhneg : -roundedHemisphereHeight r < 0 := by linarith
    exact mul_pos_of_neg_of_neg hhneg
      (roundedHemisphereHeight_deriv_neg hr0 hr1)
  · exact roundedHemisphereTangentialRadius_pos hr0 hr1.le

theorem roundedHemisphereTangentialCoefficient_contDiffAt
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ContDiffAt ℝ ∞ roundedHemisphereTangentialCoefficient r := by
  have hquot := (roundedHemisphereTangentialRadius_contDiffAt hr0 hr1).div
    contDiffAt_id hr0.ne'
  apply hquot.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hr0.ne'] with x hx
  simp [roundedHemisphereTangentialCoefficient, hx]

def roundedHemisphereAmbientMap
    (u : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 5) :=
  let c := roundedHemisphereTangentialCoefficient ‖u‖
  WithLp.toLp 2 ![c * u 0, c * u 1, c * u 2,
    -roundedHemisphereHeight ‖u‖, c * u 3]

@[simp] theorem roundedHemisphereAmbientMap_apply_zero
    (u : EuclideanSpace ℝ (Fin 4)) :
    roundedHemisphereAmbientMap u 0 =
      roundedHemisphereTangentialCoefficient ‖u‖ * u 0 := rfl

@[simp] theorem roundedHemisphereAmbientMap_apply_one
    (u : EuclideanSpace ℝ (Fin 4)) :
    roundedHemisphereAmbientMap u 1 =
      roundedHemisphereTangentialCoefficient ‖u‖ * u 1 := rfl

@[simp] theorem roundedHemisphereAmbientMap_apply_two
    (u : EuclideanSpace ℝ (Fin 4)) :
    roundedHemisphereAmbientMap u 2 =
      roundedHemisphereTangentialCoefficient ‖u‖ * u 2 := rfl

@[simp] theorem roundedHemisphereAmbientMap_apply_three
    (u : EuclideanSpace ℝ (Fin 4)) :
    roundedHemisphereAmbientMap u 3 = -roundedHemisphereHeight ‖u‖ := rfl

@[simp] theorem roundedHemisphereAmbientMap_apply_four
    (u : EuclideanSpace ℝ (Fin 4)) :
    roundedHemisphereAmbientMap u 4 =
      roundedHemisphereTangentialCoefficient ‖u‖ * u 3 := rfl

def roundedHemisphereRationalAmbientMap
    (u : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 5) :=
  let c := 2 / (1 + ‖u‖ ^ 2)
  WithLp.toLp 2 ![c * u 0, c * u 1, c * u 2,
    -(1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2), c * u 3]

theorem roundedHemisphereRationalAmbientMap_contDiff :
    ContDiff ℝ ∞ roundedHemisphereRationalAmbientMap := by
  unfold roundedHemisphereRationalAmbientMap
  have hs : ContDiff ℝ ∞ fun u : EuclideanSpace ℝ (Fin 4) ↦ ‖u‖ ^ 2 :=
    contDiff_norm_sq ℝ
  have hden : ContDiff ℝ ∞ fun u : EuclideanSpace ℝ (Fin 4) ↦
      (1 + ‖u‖ ^ 2)⁻¹ := by
    apply (contDiff_const.add hs).inv
    intro u
    positivity
  have hc : ContDiff ℝ ∞ fun u : EuclideanSpace ℝ (Fin 4) ↦
      2 / (1 + ‖u‖ ^ 2) := by
    exact contDiff_const.mul hden
  have ht : ContDiff ℝ ∞ fun u : EuclideanSpace ℝ (Fin 4) ↦
      -(1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2) := by
    exact (contDiff_const.sub hs).neg.mul hden
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · simp only [Fin.isValue, neg_sub, Fin.zero_eta, Matrix.cons_val_zero]
    fun_prop
  · simp only [Fin.isValue, neg_sub, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    fun_prop
  · simp only [Fin.isValue, neg_sub, Fin.reduceFinMk, Matrix.cons_val]
    fun_prop
  · simpa [roundedHemisphereRationalAmbientMap] using ht
  · simp only [Fin.isValue, neg_sub, Fin.reduceFinMk, Matrix.cons_val]
    fun_prop

theorem roundedHemisphereAmbientMap_eq_rational_of_norm_le
    {u : EuclideanSpace ℝ (Fin 4)} (hu : ‖u‖ ≤ 1 / 4) :
    roundedHemisphereAmbientMap u = roundedHemisphereRationalAmbientMap u := by
  have hc := roundedHemisphereTangentialCoefficient_eq_rational
    (r := ‖u‖) (norm_nonneg _) hu
  have hh := roundedHemisphereHeight_eq_rational_of_le hu
  ext i
  fin_cases i <;> simp [roundedHemisphereAmbientMap,
    roundedHemisphereRationalAmbientMap, hc, hh,
    roundedHemisphereRationalHeight]
  all_goals ring

theorem roundedHemisphereAmbientMap_contDiffAt_zero :
    ContDiffAt ℝ ∞ roundedHemisphereAmbientMap
      (0 : EuclideanSpace ℝ (Fin 4)) := by
  apply roundedHemisphereRationalAmbientMap_contDiff.contDiffAt.congr_of_eventuallyEq
  have hev : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin 4)), ‖y‖ ≤ 1 / 4 := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨1 / 4, by norm_num, ?_⟩
    intro y hy
    simpa [dist_zero_right] using hy.le
  filter_upwards [hev] with y hy
  exact roundedHemisphereAmbientMap_eq_rational_of_norm_le hy

theorem roundedHemisphereAmbientMap_contDiffAt_of_ne_zero
    {u : EuclideanSpace ℝ (Fin 4)} (hu0 : u ≠ 0) (hu1 : ‖u‖ ≤ 1) :
    ContDiffAt ℝ ∞ roundedHemisphereAmbientMap u := by
  have hr0 : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hnorm : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 4) ↦ ‖y‖) u :=
    contDiffAt_norm ℝ hu0
  have hc : ContDiffAt ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin 4) ↦
        roundedHemisphereTangentialCoefficient ‖y‖) u :=
    (roundedHemisphereTangentialCoefficient_contDiffAt hr0 hu1).comp u hnorm
  have hh : ContDiffAt ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin 4) ↦ roundedHemisphereHeight ‖y‖) u :=
    roundedHemisphereHeight_contDiff.contDiffAt.comp u hnorm
  unfold roundedHemisphereAmbientMap
  rw [contDiffAt_piLp]
  intro i
  fin_cases i <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
    fun_prop

theorem roundedHemisphereAmbientMap_contDiffOn_closedBall :
    ContDiffOn ℝ ∞ roundedHemisphereAmbientMap
      (closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  intro u hu
  by_cases hu0 : u = 0
  · subst u
    exact roundedHemisphereAmbientMap_contDiffAt_zero.contDiffWithinAt
  · apply (roundedHemisphereAmbientMap_contDiffAt_of_ne_zero hu0 ?_).contDiffWithinAt
    simpa [mem_closedBall_zero_iff] using hu

theorem roundedHemisphereTangentialCoefficient_sq_mul_sq
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    roundedHemisphereTangentialCoefficient r ^ 2 * r ^ 2 =
      1 - roundedHemisphereHeight r ^ 2 := by
  rw [roundedHemisphereTangentialCoefficient, ite_eq_right hr0.ne', div_pow]
  field_simp [hr0.ne']
  exact roundedHemisphereTangentialRadius_sq hr0 hr1

theorem norm_roundedHemisphereAmbientMap
    {u : EuclideanSpace ℝ (Fin 4)} (hu : ‖u‖ ≤ 1) :
    ‖roundedHemisphereAmbientMap u‖ = 1 := by
  by_cases hu0 : u = 0
  · subst u
    have hsq : ‖roundedHemisphereAmbientMap
        (0 : EuclideanSpace ℝ (Fin 4))‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      norm_num [roundedHemisphereAmbientMap, Fin.sum_univ_succ]
    nlinarith [norm_nonneg (roundedHemisphereAmbientMap
      (0 : EuclideanSpace ℝ (Fin 4)))]
  · have hr0 : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hc := roundedHemisphereTangentialCoefficient_sq_mul_sq hr0 hu
    have hcoords :
        u 0 ^ 2 + (u 1 ^ 2 + (u 2 ^ 2 + u 3 ^ 2)) = ‖u‖ ^ 2 := by
      simpa [Fin.sum_univ_succ] using (EuclideanSpace.real_norm_sq_eq u).symm
    have hnormsq : ‖roundedHemisphereAmbientMap u‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      change
        (roundedHemisphereTangentialCoefficient ‖u‖ * u 0) ^ 2 +
          ((roundedHemisphereTangentialCoefficient ‖u‖ * u 1) ^ 2 +
            ((roundedHemisphereTangentialCoefficient ‖u‖ * u 2) ^ 2 +
              ((-roundedHemisphereHeight ‖u‖) ^ 2 +
                (roundedHemisphereTangentialCoefficient ‖u‖ * u 3) ^ 2))) = 1
      nlinarith
    nlinarith [norm_nonneg (roundedHemisphereAmbientMap u)]

def roundedHemisphereSphereMap (u : EuclideanFourBall) : Sphere 4 :=
  ⟨roundedHemisphereAmbientMap u.1, by
    simpa [mem_sphere_zero_iff_norm] using
      norm_roundedHemisphereAmbientMap (u := u.1)
        (mem_closedBall_zero_iff.mp u.2)⟩

theorem contMDiff_roundedHemisphereAmbientMapOnFourBall :
    ContMDiff euclideanFourBallModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5))) ∞
      (fun u : EuclideanFourBall ↦ roundedHemisphereAmbientMap u.1) := by
  intro u
  have hg : ContDiffWithinAt ℝ ∞ roundedHemisphereAmbientMap
      (closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1) u.1 :=
    roundedHemisphereAmbientMap_contDiffOn_closedBall u.1 u.2
  have hf : ContMDiffWithinAt euclideanFourBallModel
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (Subtype.val : EuclideanFourBall → EuclideanSpace ℝ (Fin 4)) univ u :=
    (contMDiff_closedUnitBall_inclusion
      (E := EuclideanSpace ℝ (Fin 4))).contMDiffAt.contMDiffWithinAt
  have hc := hg.comp_contMDiffWithinAt hf (by
    intro x _hx
    exact x.2)
  exact hc.contMDiffAt (by simp)

theorem contMDiff_roundedHemisphereSphereMap :
    ContMDiff euclideanFourBallModel (𝓡 4) ∞ roundedHemisphereSphereMap := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) := ⟨by simp⟩
  have h := contMDiff_roundedHemisphereAmbientMapOnFourBall.codRestrict_sphere
    (n := 4) (fun u ↦ (roundedHemisphereSphereMap u).2)
  exact h.congr fun _ ↦ rfl

/-! The remaining public declarations expose only the direct closed-cap geometry. -/

/-- Reverse the inward radial parameter to the negative equator-collar parameter. -/
@[expose] public def roundedHemisphereEquatorTime
    (t : EuclideanFourBallCollarInterval) : EquatorCollarInterval :=
  ⟨-(t.1.1 : ℝ), by
    have ht0 : 0 ≤ (t.1.1 : ℝ) := t.1.2.1
    have htlt : (t.1.1 : ℝ) < 1 / 2 := t.2
    constructor
    · linarith
    · linarith⟩

/-- The reversed equator-collar parameter has value equal to the negated radial parameter. -/
@[simp] public theorem roundedHemisphereEquatorTime_value
    (t : EuclideanFourBallCollarInterval) :
    (roundedHemisphereEquatorTime t : ℝ) = -(t.1.1 : ℝ) :=
  rfl

theorem roundedHemisphereTangentialRadius_collar
    (t : EuclideanFourBallCollarInterval) :
    roundedHemisphereTangentialRadius (1 - (t.1.1 : ℝ)) =
      equatorCollarScale (-(t.1.1 : ℝ)) := by
  have htlt : (t.1.1 : ℝ) < 1 / 2 := t.2
  have hr : 1 / 2 ≤ 1 - (t.1.1 : ℝ) := by linarith
  rw [roundedHemisphereTangentialRadius, equatorCollarScale,
    roundedHemisphereHeight_eq_linear_of_le hr,
    roundedHemisphereLinearHeight]
  congr 1
  ring

theorem roundedHemisphereAmbientMap_euclideanFourBallSmoothCollar
    (p : EuclideanFourBallCollarDomain) :
    roundedHemisphereAmbientMap
        (euclideanFourBallSmoothCollar p : EuclideanSpace ℝ (Fin 4)) =
      equatorCollarAmbientMap p.1.1 (roundedHemisphereEquatorTime p.2).1 := by
  have htlt : (p.2.1.1 : ℝ) < 1 / 2 := p.2.2
  have hr0 : 0 < 1 - (p.2.1.1 : ℝ) := by linarith
  have hc := roundedHemisphereTangentialCoefficient_mul hr0
  have hs := roundedHemisphereTangentialRadius_collar p.2
  have hh := roundedHemisphereHeight_eq_linear_of_le
    (r := 1 - (p.2.1.1 : ℝ)) (by linarith)
  have hnorm := norm_euclideanFourBallSmoothCollar p
  ext i
  fin_cases i
  · change roundedHemisphereTangentialCoefficient
        ‖(euclideanFourBallSmoothCollar p : EuclideanSpace ℝ (Fin 4))‖ *
          (euclideanFourBallSmoothCollar p : EuclideanSpace ℝ (Fin 4)) 0 =
        equatorCollarScale (-(p.2.1.1 : ℝ)) * p.1.1 0
    rw [hnorm, euclideanFourBallSmoothCollar_coe]
    change roundedHemisphereTangentialCoefficient (1 - (p.2.1.1 : ℝ)) *
      ((1 - (p.2.1.1 : ℝ)) * p.1.1 0) = _
    rw [← mul_assoc, hc, hs]
  · change roundedHemisphereTangentialCoefficient
        ‖(euclideanFourBallSmoothCollar p : EuclideanSpace ℝ (Fin 4))‖ *
          (euclideanFourBallSmoothCollar p : EuclideanSpace ℝ (Fin 4)) 1 =
        equatorCollarScale (-(p.2.1.1 : ℝ)) * p.1.1 1
    rw [hnorm, euclideanFourBallSmoothCollar_coe]
    change roundedHemisphereTangentialCoefficient (1 - (p.2.1.1 : ℝ)) *
      ((1 - (p.2.1.1 : ℝ)) * p.1.1 1) = _
    rw [← mul_assoc, hc, hs]
  · change roundedHemisphereTangentialCoefficient
        ‖(euclideanFourBallSmoothCollar p : EuclideanSpace ℝ (Fin 4))‖ *
          (euclideanFourBallSmoothCollar p : EuclideanSpace ℝ (Fin 4)) 2 =
        equatorCollarScale (-(p.2.1.1 : ℝ)) * p.1.1 2
    rw [hnorm, euclideanFourBallSmoothCollar_coe]
    change roundedHemisphereTangentialCoefficient (1 - (p.2.1.1 : ℝ)) *
      ((1 - (p.2.1.1 : ℝ)) * p.1.1 2) = _
    rw [← mul_assoc, hc, hs]
  · change -roundedHemisphereHeight
        ‖(euclideanFourBallSmoothCollar p : EuclideanSpace ℝ (Fin 4))‖ =
        -(p.2.1.1 : ℝ)
    rw [hnorm, hh]
    unfold roundedHemisphereLinearHeight
    ring
  · change roundedHemisphereTangentialCoefficient
        ‖(euclideanFourBallSmoothCollar p : EuclideanSpace ℝ (Fin 4))‖ *
          (euclideanFourBallSmoothCollar p : EuclideanSpace ℝ (Fin 4)) 3 =
        equatorCollarScale (-(p.2.1.1 : ℝ)) * p.1.1 3
    rw [hnorm, euclideanFourBallSmoothCollar_coe]
    change roundedHemisphereTangentialCoefficient (1 - (p.2.1.1 : ℝ)) *
      ((1 - (p.2.1.1 : ℝ)) * p.1.1 3) = _
    rw [← mul_assoc, hc, hs]

theorem roundedHemisphereSphereMap_euclideanFourBallSmoothCollar
    (p : EuclideanFourBallCollarDomain) :
    roundedHemisphereSphereMap (euclideanFourBallSmoothCollar p) =
      equatorCollarSphereMap (p.1, roundedHemisphereEquatorTime p.2) := by
  apply Subtype.ext
  exact roundedHemisphereAmbientMap_euclideanFourBallSmoothCollar p

theorem equatorAmbientProjection_roundedHemisphereAmbientMap
    (u : EuclideanSpace ℝ (Fin 4)) :
    equatorAmbientProjection (roundedHemisphereAmbientMap u) =
      roundedHemisphereTangentialCoefficient ‖u‖ • u := by
  ext i
  fin_cases i <;>
    simp [equatorAmbientProjection, roundedHemisphereAmbientMap]

theorem roundedHemisphereAmbientMap_injectiveOn_closedBall :
    Set.InjOn roundedHemisphereAmbientMap
      (closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  intro u hu v hv huv
  have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.mp hu
  have hv1 : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.mp hv
  have hheight : roundedHemisphereHeight ‖u‖ =
      roundedHemisphereHeight ‖v‖ := by
    have hcoord := congrArg (fun z : EuclideanSpace ℝ (Fin 5) ↦ z 3) huv
    simpa using neg_injective hcoord
  have hnorm : ‖u‖ = ‖v‖ :=
    roundedHemisphereHeight_strictAntiOn.injOn
      ⟨norm_nonneg _, hu1⟩ ⟨norm_nonneg _, hv1⟩ hheight
  by_cases hzero : ‖u‖ = 0
  · have hu0 : u = 0 := norm_eq_zero.mp hzero
    have hv0 : v = 0 := norm_eq_zero.mp (hnorm ▸ hzero)
    exact hu0.trans hv0.symm
  · have hu0 : u ≠ 0 := fun hu0 ↦ hzero (by rw [hu0, norm_zero])
    have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hcne : roundedHemisphereTangentialCoefficient ‖u‖ ≠ 0 :=
      (roundedHemisphereTangentialCoefficient_pos hpos hu1).ne'
    have hproj := congrArg equatorAmbientProjection huv
    rw [equatorAmbientProjection_roundedHemisphereAmbientMap,
      equatorAmbientProjection_roundedHemisphereAmbientMap, ← hnorm] at hproj
    have hz : roundedHemisphereTangentialCoefficient ‖u‖ • (u - v) = 0 := by
      rw [smul_sub, hproj, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hcne)

theorem injective_roundedHemisphereSphereMap :
    Injective roundedHemisphereSphereMap := by
  intro u v huv
  apply Subtype.ext
  apply roundedHemisphereAmbientMap_injectiveOn_closedBall u.2 v.2
  exact congrArg Subtype.val huv

theorem isClosedEmbedding_roundedHemisphereSphereMap :
    IsClosedEmbedding roundedHemisphereSphereMap :=
  contMDiff_roundedHemisphereSphereMap.continuous.isClosedEmbedding
    injective_roundedHemisphereSphereMap

def roundedHemisphereHeightMap : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
  fun r ↦ ⟨roundedHemisphereHeight r.1,
    roundedHemisphereHeight_mem_Icc r.2⟩

theorem continuous_roundedHemisphereHeightMap :
    Continuous roundedHemisphereHeightMap := by
  exact continuous_induced_rng.mpr <|
    roundedHemisphereHeight_contDiff.continuous.comp continuous_subtype_val

theorem injective_roundedHemisphereHeightMap :
    Injective roundedHemisphereHeightMap := by
  intro r s hrs
  apply Subtype.ext
  apply roundedHemisphereHeight_strictAntiOn.injOn r.2 s.2
  exact congrArg Subtype.val hrs

theorem surjective_roundedHemisphereHeightMap :
    Surjective roundedHemisphereHeightMap := by
  have himage : roundedHemisphereHeight '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
    simpa using
      roundedHemisphereHeight_contDiff.continuous.continuousOn.image_Icc_of_antitoneOn
        (show (0 : ℝ) ≤ 1 by norm_num)
        roundedHemisphereHeight_strictAntiOn.antitoneOn
  intro y
  have hy : (y.1 : ℝ) ∈ roundedHemisphereHeight '' Icc (0 : ℝ) 1 := by
    rw [himage]
    exact y.2
  rcases hy with ⟨r, hr, hry⟩
  exact ⟨⟨r, hr⟩, Subtype.ext hry⟩

noncomputable def roundedHemisphereHeightHomeomorph :
    Icc (0 : ℝ) 1 ≃ₜ Icc (0 : ℝ) 1 :=
  (continuous_roundedHemisphereHeightMap.isClosedEmbedding
    injective_roundedHemisphereHeightMap).isEmbedding.toHomeomorphOfSurjective
      surjective_roundedHemisphereHeightMap

@[simp] theorem roundedHemisphereHeightHomeomorph_apply
    (r : Icc (0 : ℝ) 1) :
    (roundedHemisphereHeightHomeomorph r : ℝ) =
      roundedHemisphereHeight r.1 :=
  rfl

/-- The closed coordinate hemisphere on the nonpositive side of the equator. -/
@[expose] public def coordinateClosedCapZero : Set (Sphere 4) :=
  (coordinateOpenCap 1)ᶜ

theorem roundedHemisphereSphereMap_mem_coordinateClosedCapZero
    (u : EuclideanFourBall) :
    roundedHemisphereSphereMap u ∈ coordinateClosedCapZero := by
  rw [coordinateClosedCapZero, mem_compl_iff, mem_coordinateOpenCap_one]
  change ¬0 < -roundedHemisphereHeight ‖u.1‖
  have hu1 : ‖u.1‖ ≤ 1 := mem_closedBall_zero_iff.mp u.2
  have hh0 := (roundedHemisphereHeight_mem_Icc
    ⟨norm_nonneg u.1, hu1⟩).1
  linarith

private theorem euclideanFive_ext_of_equatorAmbientProjection_eq
    {x y : EuclideanSpace ℝ (Fin 5)}
    (hproj : equatorAmbientProjection x = equatorAmbientProjection y)
    (hthree : x 3 = y 3) : x = y := by
  ext i
  fin_cases i
  · exact congrArg (fun z : EuclideanSpace ℝ (Fin 4) ↦ z 0) hproj
  · exact congrArg (fun z : EuclideanSpace ℝ (Fin 4) ↦ z 1) hproj
  · exact congrArg (fun z : EuclideanSpace ℝ (Fin 4) ↦ z 2) hproj
  · exact hthree
  · exact congrArg (fun z : EuclideanSpace ℝ (Fin 4) ↦ z 3) hproj

theorem coordinateClosedCapZero_subset_range_roundedHemisphereSphereMap :
    coordinateClosedCapZero ⊆ range roundedHemisphereSphereMap := by
  intro y hy
  have hy3 : y.1 3 ≤ 0 := by
    rw [coordinateClosedCapZero, mem_compl_iff,
      mem_coordinateOpenCap_one] at hy
    exact le_of_not_gt hy
  have hynorm : ‖y.1‖ = 1 := mem_sphere_zero_iff_norm.mp y.2
  have hdecomp :
      ‖equatorAmbientProjection y.1‖ ^ 2 + y.1 3 ^ 2 = 1 := by
    simpa [hynorm] using norm_equatorAmbientProjection_sq_add_coord_three y.1
  have hy3lower : -1 ≤ y.1 3 := by
    nlinarith [sq_nonneg (equatorAmbientProjection y.1 |> norm)]
  let t : Icc (0 : ℝ) 1 := ⟨-y.1 3, by constructor <;> linarith⟩
  let rI : Icc (0 : ℝ) 1 := roundedHemisphereHeightHomeomorph.symm t
  let r : ℝ := rI.1
  have hrmem : r ∈ Icc (0 : ℝ) 1 := rI.2
  have hheight : roundedHemisphereHeight r = -y.1 3 := by
    have h := roundedHemisphereHeightHomeomorph.apply_symm_apply t
    exact congrArg Subtype.val h
  by_cases hrzero : r = 0
  · have hy3eq : y.1 3 = -1 := by
      rw [hrzero, roundedHemisphereHeight_zero] at hheight
      linarith
    have hprojzero : equatorAmbientProjection y.1 = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (equatorAmbientProjection y.1)]
    let u : EuclideanFourBall := ⟨0, by simp⟩
    refine ⟨u, Subtype.ext ?_⟩
    apply euclideanFive_ext_of_equatorAmbientProjection_eq
    · change equatorAmbientProjection (roundedHemisphereAmbientMap u.1) = _
      rw [equatorAmbientProjection_roundedHemisphereAmbientMap,
        hprojzero]
      simp [u]
    · simp [roundedHemisphereSphereMap, roundedHemisphereAmbientMap, u, hy3eq]
  · have hrpos : 0 < r := lt_of_le_of_ne hrmem.1 (Ne.symm hrzero)
    have hspos : 0 < roundedHemisphereTangentialRadius r :=
      roundedHemisphereTangentialRadius_pos hrpos hrmem.2
    have hprojNorm : ‖equatorAmbientProjection y.1‖ =
        roundedHemisphereTangentialRadius r := by
      have hsSq := roundedHemisphereTangentialRadius_sq hrpos hrmem.2
      nlinarith [norm_nonneg (equatorAmbientProjection y.1)]
    let u0 : EuclideanSpace ℝ (Fin 4) :=
      (r / roundedHemisphereTangentialRadius r) •
        equatorAmbientProjection y.1
    have hu0norm : ‖u0‖ = r := by
      dsimp [u0]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hrpos hspos),
        hprojNorm]
      field_simp [hspos.ne']
    let u : EuclideanFourBall := ⟨u0, by
      rw [mem_closedBall_zero_iff, hu0norm]
      exact hrmem.2⟩
    refine ⟨u, Subtype.ext ?_⟩
    apply euclideanFive_ext_of_equatorAmbientProjection_eq
    · change equatorAmbientProjection (roundedHemisphereAmbientMap u.1) = _
      rw [equatorAmbientProjection_roundedHemisphereAmbientMap]
      change roundedHemisphereTangentialCoefficient ‖u0‖ • u0 = _
      rw [hu0norm]
      dsimp [u0]
      rw [smul_smul]
      rw [roundedHemisphereTangentialCoefficient,
        ite_eq_right hrpos.ne']
      field_simp [hrpos.ne', hspos.ne']
      simp
    · change -roundedHemisphereHeight ‖u0‖ = y.1 3
      rw [hu0norm, hheight]
      ring

theorem range_roundedHemisphereSphereMap :
    range roundedHemisphereSphereMap = coordinateClosedCapZero := by
  apply Subset.antisymm
  · rintro _ ⟨u, rfl⟩
    exact roundedHemisphereSphereMap_mem_coordinateClosedCapZero u
  · exact coordinateClosedCapZero_subset_range_roundedHemisphereSphereMap

noncomputable def roundedHemisphereClosedCapHomeomorph :
    EuclideanFourBall ≃ₜ coordinateClosedCapZero :=
  isClosedEmbedding_roundedHemisphereSphereMap.isEmbedding.toHomeomorph.trans <|
    Homeomorph.setCongr range_roundedHemisphereSphereMap

@[simp] theorem roundedHemisphereClosedCapHomeomorph_apply_coe
    (u : EuclideanFourBall) :
    ((roundedHemisphereClosedCapHomeomorph u : coordinateClosedCapZero) : Sphere 4) =
      roundedHemisphereSphereMap u :=
  rfl

theorem roundedHemisphereHeight_pos_iff
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 < roundedHemisphereHeight r ↔ r < 1 := by
  constructor
  · intro hh
    exact lt_of_le_of_ne hr1 fun hr ↦ by
      subst r
      simp at hh
  · intro hr
    have h := roundedHemisphereHeight_strictAntiOn
      ⟨hr0, hr1⟩ (show (1 : ℝ) ∈ Icc 0 1 by simp) hr
    simpa using h

theorem roundedHemisphereSphereMap_mem_coordinateOpenCap_zero_iff
    (u : EuclideanFourBall) :
    roundedHemisphereSphereMap u ∈ coordinateOpenCap 0 ↔ ‖u.1‖ < 1 := by
  rw [mem_coordinateOpenCap_zero]
  change -roundedHemisphereHeight ‖u.1‖ < 0 ↔ ‖u.1‖ < 1
  rw [neg_lt_zero, roundedHemisphereHeight_pos_iff (norm_nonneg _)]
  exact mem_closedBall_zero_iff.mp u.2

theorem roundedHemisphereTangentialRadius_strictMonoOn :
    StrictMonoOn roundedHemisphereTangentialRadius (Icc (0 : ℝ) 1) := by
  intro r hr s hs hrs
  by_cases hrzero : r = 0
  · subst r
    rw [roundedHemisphereTangentialRadius_zero]
    exact roundedHemisphereTangentialRadius_pos hrs hs.2
  · have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hrzero)
    have hspos : 0 < s := hrpos.trans hrs
    have hheight := roundedHemisphereHeight_strictAntiOn hr hs hrs
    have hhr := roundedHemisphereHeight_mem_Icc hr
    have hhs := roundedHemisphereHeight_mem_Icc hs
    have hheightSq : roundedHemisphereHeight s ^ 2 <
        roundedHemisphereHeight r ^ 2 :=
      (sq_lt_sq₀ hhs.1 hhr.1).mpr hheight
    have hrSq := roundedHemisphereTangentialRadius_sq hrpos hr.2
    have hsSq := roundedHemisphereTangentialRadius_sq hspos hs.2
    have hradSq : roundedHemisphereTangentialRadius r ^ 2 <
        roundedHemisphereTangentialRadius s ^ 2 := by
      nlinarith
    exact (sq_lt_sq₀ (roundedHemisphereTangentialRadius_nonneg r)
      (roundedHemisphereTangentialRadius_nonneg s)).mp hradSq

def roundedHemisphereTangentialRadiusMap :
    Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun r ↦
  ⟨roundedHemisphereTangentialRadius r.1, by
    constructor
    · exact roundedHemisphereTangentialRadius_nonneg _
    · by_cases hrzero : r.1 = 0
      · simp [hrzero]
      · have hrpos : 0 < r.1 := lt_of_le_of_ne r.2.1 (Ne.symm hrzero)
        have hsq := roundedHemisphereTangentialRadius_sq hrpos r.2.2
        have hh := roundedHemisphereHeight_mem_Icc r.2
        nlinarith [roundedHemisphereTangentialRadius_nonneg r.1,
          sq_nonneg (roundedHemisphereHeight r.1)]⟩

theorem continuous_roundedHemisphereTangentialRadiusMap :
    Continuous roundedHemisphereTangentialRadiusMap := by
  apply continuous_induced_rng.mpr
  change Continuous fun r : Icc (0 : ℝ) 1 ↦
    roundedHemisphereTangentialRadius r.1
  apply continuous_iff_continuousAt.mpr
  intro r
  by_cases hrzero : r.1 = 0
  · have hre : r = (⟨0, by simp⟩ : Icc (0 : ℝ) 1) := Subtype.ext hrzero
    rw [hre]
    apply ContinuousAt.congr_of_eventuallyEq
      (show ContinuousAt (fun x : Icc (0 : ℝ) 1 ↦
        2 * x.1 / (1 + x.1 ^ 2)) ⟨0, by simp⟩ by
          exact (continuousAt_const.mul continuousAt_subtype_val).div
            (continuousAt_const.add (continuousAt_subtype_val.pow 2)) (by norm_num))
    have hev : ∀ᶠ x : Icc (0 : ℝ) 1 in 𝓝 ⟨0, by simp⟩, x.1 ≤ 1 / 4 := by
      apply Metric.eventually_nhds_iff.mpr
      refine ⟨1 / 4, by norm_num, ?_⟩
      intro x hx
      change dist (x.1 : ℝ) 0 < 1 / 4 at hx
      have hxabs : |x.1| < 1 / 4 := by
        simpa [Real.dist_eq] using hx
      exact (le_abs_self x.1).trans hxabs.le
    filter_upwards [hev] with x hx
    exact roundedHemisphereTangentialRadius_eq_rational x.2.1 hx
  · exact (roundedHemisphereTangentialRadius_contDiffAt
      (lt_of_le_of_ne r.2.1 (Ne.symm hrzero)) r.2.2).continuousAt.comp
        continuousAt_subtype_val

theorem injective_roundedHemisphereTangentialRadiusMap :
    Injective roundedHemisphereTangentialRadiusMap := by
  intro r s hrs
  apply Subtype.ext
  apply roundedHemisphereTangentialRadius_strictMonoOn.injOn r.2 s.2
  exact congrArg Subtype.val hrs

theorem surjective_roundedHemisphereTangentialRadiusMap :
    Surjective roundedHemisphereTangentialRadiusMap := by
  have himage : roundedHemisphereTangentialRadius '' Icc (0 : ℝ) 1 =
      Icc (0 : ℝ) 1 := by
    have hcont : ContinuousOn roundedHemisphereTangentialRadius (Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact continuous_subtype_val.comp continuous_roundedHemisphereTangentialRadiusMap
    simpa using
      hcont.image_Icc_of_monotoneOn
        (show (0 : ℝ) ≤ 1 by norm_num)
        roundedHemisphereTangentialRadius_strictMonoOn.monotoneOn
  intro y
  have hy : y.1 ∈ roundedHemisphereTangentialRadius '' Icc (0 : ℝ) 1 := by
    rw [himage]
    exact y.2
  rcases hy with ⟨r, hr, hry⟩
  exact ⟨⟨r, hr⟩, Subtype.ext hry⟩

noncomputable def roundedHemisphereTangentialRadiusHomeomorph :
    Icc (0 : ℝ) 1 ≃ₜ Icc (0 : ℝ) 1 :=
  (continuous_roundedHemisphereTangentialRadiusMap.isClosedEmbedding
    injective_roundedHemisphereTangentialRadiusMap).isEmbedding.toHomeomorphOfSurjective
      surjective_roundedHemisphereTangentialRadiusMap

@[simp] theorem roundedHemisphereTangentialRadiusHomeomorph_apply
    (r : Icc (0 : ℝ) 1) :
    (roundedHemisphereTangentialRadiusHomeomorph r : ℝ) =
      roundedHemisphereTangentialRadius r.1 :=
  rfl

theorem isLocalDiffeomorphAt_roundedHemisphereTangentialRadius
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      roundedHemisphereTangentialRadius r := by
  let d : ℝ := deriv roundedHemisphereTangentialRadius r
  have hdpos : 0 < d := roundedHemisphereTangentialRadius_deriv_pos hr0 hr1
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 d hdpos.ne')
  have hf : ContDiffAt ℝ ∞ roundedHemisphereTangentialRadius r :=
    roundedHemisphereTangentialRadius_contDiffAt hr0 hr1.le
  have hder : HasFDerivAt roundedHemisphereTangentialRadius
      (e : ℝ →L[ℝ] ℝ) r := by
    have h := (roundedHemisphereTangentialRadius_hasDerivAt hr0 hr1).hasFDerivAt
    convert! h using 1
    ext
    simp [e, d, (roundedHemisphereTangentialRadius_hasDerivAt hr0 hr1).deriv]
  let P : OpenPartialHomeomorph ℝ ℝ :=
    hf.toOpenPartialHomeomorph roundedHemisphereTangentialRadius hder (by simp)
  let U : Set ℝ := Ioo 0 1
  have hUopen : IsOpen U := isOpen_Ioo
  let Q : OpenPartialHomeomorph ℝ ℝ := P.restr U
  have hrP : r ∈ P.source :=
    hf.mem_toOpenPartialHomeomorph_source hder (by simp)
  have hrQ : r ∈ Q.source := by
    simpa only [Q, P.restr_source' U hUopen, mem_inter_iff, U] using
      ⟨hrP, hr0, hr1⟩
  let Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ := {
    toPartialEquiv := Q.toPartialEquiv
    open_source := Q.open_source
    open_target := Q.open_target
    contMDiffOn_toFun := by
      change ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        roundedHemisphereTangentialRadius Q.source
      intro x hx
      have hxU : x ∈ U := by
        rw [show Q.source = P.source ∩ U by exact P.restr_source' U hUopen] at hx
        exact hx.2
      exact (roundedHemisphereTangentialRadius_contDiffAt hxU.1 hxU.2.le).contMDiffAt
        |>.contMDiffWithinAt
    contMDiffOn_invFun := by
      intro y hy
      apply ContDiffWithinAt.contMDiffWithinAt
      apply ContDiffAt.contDiffWithinAt
      have hxsource : Q.symm y ∈ Q.source := Q.symm.map_source hy
      have hxU : Q.symm y ∈ U := by
        rw [show Q.source = P.source ∩ U by exact P.restr_source' U hUopen] at hxsource
        exact hxsource.2
      let dx : ℝ := deriv roundedHemisphereTangentialRadius (Q.symm y)
      have hdxpos : 0 < dx :=
        roundedHemisphereTangentialRadius_deriv_pos hxU.1 hxU.2
      let ex : ℝ ≃L[ℝ] ℝ :=
        ContinuousLinearEquiv.smulLeft (Units.mk0 dx hdxpos.ne')
      apply Q.contDiffAt_symm hy (f₀' := ex)
      · have h := (roundedHemisphereTangentialRadius_hasDerivAt hxU.1 hxU.2).hasFDerivAt
        convert! h using 1
        ext
        simp [ex, dx,
          (roundedHemisphereTangentialRadius_hasDerivAt hxU.1 hxU.2).deriv]
      · exact roundedHemisphereTangentialRadius_contDiffAt hxU.1 hxU.2.le
    }
  exact Φ.isLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ hrQ

def roundedHemispherePuncturedOpens : Opens (EuclideanSpace ℝ (Fin 4)) :=
  ⟨{0}ᶜ, isOpen_compl_singleton⟩

abbrev RoundedHemispherePunctured := roundedHemispherePuncturedOpens

def roundedHemispherePositiveRadiusOpens : Opens ℝ :=
  ⟨Ioi 0, isOpen_Ioi⟩

abbrev RoundedHemispherePositiveRadius := roundedHemispherePositiveRadiusOpens

noncomputable def roundedHemispherePolarDiffeomorph :
    roundedHemispherePuncturedOpens ≃ₘ^∞⟮
      𝓡 4, (𝓡 3).prod (modelWithCornersSelf ℝ ℝ)⟯
      Sphere 3 × roundedHemispherePositiveRadiusOpens where
  toEquiv := (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 4))).toEquiv
  contMDiff_toFun := by
    have hval : ContMDiff (𝓡 4) (𝓡 4) ∞
        (Subtype.val : roundedHemispherePuncturedOpens →
          EuclideanSpace ℝ (Fin 4)) :=
      contMDiff_subtype_val
    have hnorm : ContMDiff (𝓡 4) (modelWithCornersSelf ℝ ℝ) ∞
        (fun x : roundedHemispherePuncturedOpens ↦ ‖x.1‖) := by
      intro x
      exact (contDiffAt_norm ℝ x.2).contMDiffAt.comp x hval.contMDiffAt
    have hraw : ContMDiff (𝓡 4) (𝓡 4) ∞
        (fun x : roundedHemispherePuncturedOpens ↦ ‖x.1‖⁻¹ • x.1) :=
      (hnorm.inv₀ (fun x ↦ norm_ne_zero_iff.mpr x.2)).smul hval
    let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
      ⟨by simp⟩
    have hdirection : ContMDiff (𝓡 4) (𝓡 3) ∞
        (fun x : roundedHemispherePuncturedOpens ↦
          (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 4)) x).1) := by
      have hcod := hraw.codRestrict_sphere (n := 3) (fun x ↦ by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr x.2))]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr x.2))
      exact hcod.congr fun x ↦ by
        apply Subtype.ext
        exact homeomorphUnitSphereProd_apply_fst_coe _ x
    have hradius : ContMDiff (𝓡 4) (modelWithCornersSelf ℝ ℝ) ∞
        (fun x : roundedHemispherePuncturedOpens ↦
          (⟨‖x.1‖, norm_pos_iff.mpr x.2⟩ :
            roundedHemispherePositiveRadiusOpens)) := by
      apply (ContMDiff.subtypeVal_comp_iff roundedHemispherePositiveRadiusOpens _).mp
      exact hnorm.congr fun _ ↦ rfl
    exact (hdirection.prodMk hradius).congr fun x ↦ by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact homeomorphUnitSphereProd_apply_snd_coe _ x
  contMDiff_invFun := by
    let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
      ⟨by simp⟩
    apply (ContMDiff.subtypeVal_comp_iff roundedHemispherePuncturedOpens _).mp
    have hradius : ContMDiff ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ))
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun p : Sphere 3 × roundedHemispherePositiveRadiusOpens ↦ p.2.1) :=
      contMDiff_subtype_val.comp contMDiff_snd
    have hdirection : ContMDiff ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ))
        (𝓡 4) ∞
        (fun p : Sphere 3 × roundedHemispherePositiveRadiusOpens ↦ p.1.1) :=
      contMDiff_coe_sphere.comp contMDiff_fst
    exact (hradius.smul hdirection).congr fun _ ↦ rfl

private theorem isLocalDiffeomorphAt_sphereThreeProdMap
    {A B : Type*} [TopologicalSpace A] [ChartedSpace ℝ A]
    [TopologicalSpace B] [ChartedSpace ℝ B]
    {f : A → B} {a : A}
    (hf : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ∞ f a)
    (x : Sphere 3) :
    IsLocalDiffeomorphAt
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ))
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ)) ∞
      (fun p : Sphere 3 × A ↦ (p.1, f p.2)) (x, a) := by
  let φ : PartialDiffeomorph (𝓡 3) (𝓡 3) (Sphere 3) (Sphere 3) ∞ := {
    toPartialEquiv := {
      toFun := id
      invFun := id
      source := univ
      target := univ
      map_source' := by simp
      map_target' := by simp
      left_inv' := by simp
      right_inv' := by simp }
    open_source := isOpen_univ
    open_target := isOpen_univ
    contMDiffOn_toFun := contMDiff_id.contMDiffOn
    contMDiffOn_invFun := contMDiff_id.contMDiffOn }
  let ψ := Classical.choose hf
  let q := φ.toOpenPartialHomeomorph.prod ψ.toOpenPartialHomeomorph
  let Φ : PartialDiffeomorph
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ))
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ))
      (Sphere 3 × A) (Sphere 3 × B) ∞ := {
    toPartialEquiv := q.toPartialEquiv
    open_source := q.open_source
    open_target := q.open_target
    contMDiffOn_toFun := φ.contMDiffOn_toFun.prodMap ψ.contMDiffOn_toFun
    contMDiffOn_invFun := φ.contMDiffOn_invFun.prodMap ψ.contMDiffOn_invFun }
  refine ⟨Φ, ?_, ?_⟩
  · change x ∈ φ.source ∧ a ∈ ψ.source
    exact ⟨trivial, (Classical.choose_spec hf).1⟩
  · intro p hp
    change p.1 ∈ φ.source ∧ p.2 ∈ ψ.source at hp
    apply Prod.ext
    · rfl
    · exact (Classical.choose_spec hf).2 hp.2

private theorem rounded_isLocalDiffeomorphAt_congr_of_eventuallyEq
    {E F H K M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace K]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K)
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N]
    {f g : M → N} {x : M}
    (hg : IsLocalDiffeomorphAt I J ∞ g x)
    (heq : f =ᶠ[nhds x] g) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp heq
  let Ψ := Classical.choose hg
  let q := Ψ.toOpenPartialHomeomorph.restrOpen W hWopen
  let Φ : PartialDiffeomorph I J M N ∞ := {
    toPartialEquiv := q.toPartialEquiv
    open_source := q.open_source
    open_target := q.open_target
    contMDiffOn_toFun := by
      apply Ψ.contMDiffOn_toFun.mono
      intro y hy
      exact hy.1
    contMDiffOn_invFun := by
      apply Ψ.contMDiffOn_invFun.mono
      intro y hy
      exact hy.1 }
  refine ⟨Φ, ?_, ?_⟩
  · exact ⟨(Classical.choose_spec hg).1, hxW⟩
  · intro y hy
    exact (hWsub hy.2).trans ((Classical.choose_spec hg).2 hy.1)

private theorem rounded_isLocalDiffeomorphAt_of_parametrization
    {E F H K M N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace K]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K)
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N]
    [TopologicalSpace P] [ChartedSpace H P]
    (F : M → N) (c : P → M) (p : P)
    (hc : IsLocalDiffeomorphAt I I ∞ c p)
    (hFc : IsLocalDiffeomorphAt I J ∞ (F ∘ c) p) :
    IsLocalDiffeomorphAt I J ∞ F (c p) := by
  have hcomp : IsLocalDiffeomorphAt I J ∞
      ((F ∘ c) ∘ hc.localInverse) (c p) :=
    hc.localInverse_isLocalDiffeomorphAt.comp J N (by
      have hinv : hc.localInverse (c p) = p :=
        hc.localInverse_left_inv hc.localInverse_mem_target
      simpa [hinv] using hFc)
  apply rounded_isLocalDiffeomorphAt_congr_of_eventuallyEq I J hcomp
  filter_upwards [hc.localInverse_eventuallyEq_right] with y hy
  simp only [Function.comp_apply] at hy ⊢
  simp [hy]

def roundedHemisphereRadialMap
    (u : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  roundedHemisphereTangentialCoefficient ‖u‖ • u

def roundedHemispherePolarReconstruct
    (p : Sphere 3 × ℝ) : EuclideanSpace ℝ (Fin 4) :=
  p.2 • p.1.1

private theorem isLocalDiffeomorphAt_roundedHemispherePolarReconstruct
    {p : Sphere 3 × ℝ} (hp : 0 < p.2) :
    IsLocalDiffeomorphAt
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ)) (𝓡 4) ∞
      roundedHemispherePolarReconstruct p := by
  let a : Sphere 3 × roundedHemispherePositiveRadiusOpens :=
    (p.1, ⟨p.2, hp⟩)
  let j : Sphere 3 × roundedHemispherePositiveRadiusOpens → Sphere 3 × ℝ :=
    fun q ↦ (q.1, q.2.1)
  have hj : IsLocalDiffeomorph
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ))
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ)) ∞ j := by
    intro q
    exact isLocalDiffeomorphAt_sphereThreeProdMap
      (isLocalDiffeomorph_opensSubtypeVal
        (modelWithCornersSelf ℝ ℝ) roundedHemispherePositiveRadiusOpens q.2) q.1
  have hpolarInv : IsLocalDiffeomorph
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ)) (𝓡 4) ∞
      (fun q : Sphere 3 × roundedHemispherePositiveRadiusOpens ↦
        ((roundedHemispherePolarDiffeomorph.symm q :
          roundedHemispherePuncturedOpens) : EuclideanSpace ℝ (Fin 4))) := by
    intro q
    have h := roundedHemispherePolarDiffeomorph.symm.isLocalDiffeomorph q
    have hval := isLocalDiffeomorph_opensSubtypeVal (𝓡 4)
      roundedHemispherePuncturedOpens
      (roundedHemispherePolarDiffeomorph.symm q)
    exact h.comp (𝓡 4) (EuclideanSpace ℝ (Fin 4)) hval
  have hcomp : IsLocalDiffeomorph
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ)) (𝓡 4) ∞
      (roundedHemispherePolarReconstruct ∘ j) := by
    intro q
    apply rounded_isLocalDiffeomorphAt_congr_of_eventuallyEq
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ)) (𝓡 4) (hpolarInv q)
    filter_upwards [] with z
    rw [Function.comp_apply, roundedHemispherePolarReconstruct]
    exact homeomorphUnitSphereProd_symm_apply_coe _ z
  have h := isLocalDiffeomorphAt_of_localDiffeomorph_parametrization
    ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ)) (𝓡 4)
    roundedHemispherePolarReconstruct j hj hcomp a
  simpa [j, a] using h

theorem isLocalDiffeomorphAt_roundedHemisphereRadialMap_of_ne_zero
    {u : EuclideanSpace ℝ (Fin 4)} (hu : u ≠ 0) (hu1 : ‖u‖ < 1) :
    IsLocalDiffeomorphAt (𝓡 4) (𝓡 4) ∞
      roundedHemisphereRadialMap u := by
  let x : roundedHemispherePuncturedOpens := ⟨u, hu⟩
  let p : Sphere 3 × roundedHemispherePositiveRadiusOpens :=
    roundedHemispherePolarDiffeomorph x
  let j : Sphere 3 × roundedHemispherePositiveRadiusOpens → Sphere 3 × ℝ :=
    fun q ↦ (q.1, q.2.1)
  let k : Sphere 3 × roundedHemispherePositiveRadiusOpens → Sphere 3 × ℝ :=
    fun q ↦ (q.1, roundedHemisphereTangentialRadius q.2.1)
  have hpRadius : p.2.1 = ‖u‖ := by
    exact homeomorphUnitSphereProd_apply_snd_coe _ x
  have hp0 : 0 < p.2.1 := p.2.2
  have hp1 : p.2.1 < 1 := hpRadius.trans_lt hu1
  have hj : IsLocalDiffeomorphAt
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ))
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ)) ∞ j p :=
    isLocalDiffeomorphAt_sphereThreeProdMap
      (isLocalDiffeomorph_opensSubtypeVal
        (modelWithCornersSelf ℝ ℝ) roundedHemispherePositiveRadiusOpens p.2) p.1
  have hradius : IsLocalDiffeomorphAt
      (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ∞
      roundedHemisphereTangentialRadius p.2.1 :=
    isLocalDiffeomorphAt_roundedHemisphereTangentialRadius hp0 hp1
  have hprod : IsLocalDiffeomorphAt
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ))
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ)) ∞
      (fun q : Sphere 3 × ℝ ↦
        (q.1, roundedHemisphereTangentialRadius q.2)) (j p) := by
    simpa [j] using isLocalDiffeomorphAt_sphereThreeProdMap hradius p.1
  have hkComp := hj.comp
    ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ)) (Sphere 3 × ℝ) hprod
  have hk : IsLocalDiffeomorphAt
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ))
      ((𝓡 3).prod (modelWithCornersSelf ℝ ℝ)) ∞ k p := by
    simpa [j, k, Function.comp_def] using hkComp
  have hkPos : 0 < (k p).2 := by
    exact roundedHemisphereTangentialRadius_pos hp0 hp1.le
  have hreconstruct :=
    isLocalDiffeomorphAt_roundedHemispherePolarReconstruct hkPos
  have hpolarComp : IsLocalDiffeomorphAt
      (𝓡 4) (𝓡 4) ∞
      ((roundedHemispherePolarReconstruct ∘ k) ∘
        roundedHemispherePolarDiffeomorph) x :=
    roundedHemispherePolarDiffeomorph.isLocalDiffeomorph x |>.comp
      (𝓡 4) (EuclideanSpace ℝ (Fin 4)) <|
      hk.comp (𝓡 4) (EuclideanSpace ℝ (Fin 4)) hreconstruct
  have hradialComp : IsLocalDiffeomorphAt (𝓡 4) (𝓡 4) ∞
      (roundedHemisphereRadialMap ∘
        (Subtype.val : roundedHemispherePuncturedOpens →
          EuclideanSpace ℝ (Fin 4))) x := by
    apply rounded_isLocalDiffeomorphAt_congr_of_eventuallyEq
      (𝓡 4) (𝓡 4) hpolarComp
    have hball : (Subtype.val : roundedHemispherePuncturedOpens →
        EuclideanSpace ℝ (Fin 4)) ⁻¹' ball 0 1 ∈ nhds x := by
      have hopen : IsOpen ((Subtype.val : roundedHemispherePuncturedOpens →
          EuclideanSpace ℝ (Fin 4)) ⁻¹' ball 0 1) :=
        isOpen_ball.preimage continuous_subtype_val
      have hxmem : x ∈ (Subtype.val : roundedHemispherePuncturedOpens →
          EuclideanSpace ℝ (Fin 4)) ⁻¹' ball 0 1 := by
        simpa [mem_ball, dist_zero_right, x] using hu1
      exact hopen.mem_nhds hxmem
    filter_upwards [hball] with z hz
    change roundedHemisphereRadialMap z.1 =
      roundedHemispherePolarReconstruct
        (k (roundedHemispherePolarDiffeomorph z))
    rw [roundedHemisphereRadialMap, roundedHemispherePolarReconstruct]
    have hz0 : 0 < ‖z.1‖ := norm_pos_iff.mpr z.2
    have hzlt : ‖z.1‖ < 1 := by
      simpa [mem_ball, dist_zero_right] using hz
    have hzle : ‖z.1‖ ≤ 1 := hzlt.le
    have hcoef : roundedHemisphereTangentialRadius ‖z.1‖ * ‖z.1‖⁻¹ =
        roundedHemisphereTangentialCoefficient ‖z.1‖ := by
      rw [mul_inv_eq_iff_eq_mul₀ (norm_ne_zero_iff.mpr z.2)]
      exact (roundedHemisphereTangentialCoefficient_mul hz0).symm
    rw [show (k (roundedHemispherePolarDiffeomorph z)).2 =
        roundedHemisphereTangentialRadius ‖z.1‖ by
      change roundedHemisphereTangentialRadius
        ((roundedHemispherePolarDiffeomorph z).2 : ℝ) = _
      exact congrArg roundedHemisphereTangentialRadius
        (homeomorphUnitSphereProd_apply_snd_coe _ z)]
    rw [show ((k (roundedHemispherePolarDiffeomorph z)).1 :
        EuclideanSpace ℝ (Fin 4)) = ‖z.1‖⁻¹ • z.1 by
      exact homeomorphUnitSphereProd_apply_fst_coe _ z]
    rw [smul_smul, hcoef]
  have hsub := isLocalDiffeomorph_opensSubtypeVal (𝓡 4)
    roundedHemispherePuncturedOpens x
  have hcancel := rounded_isLocalDiffeomorphAt_of_parametrization
    (𝓡 4) (𝓡 4) roundedHemisphereRadialMap
    (Subtype.val : roundedHemispherePuncturedOpens →
      EuclideanSpace ℝ (Fin 4)) x hsub hradialComp
  simpa [x] using hcancel

def roundedHemisphereRationalRadialMap
    (u : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  (2 / (1 + ‖u‖ ^ 2)) • u

theorem roundedHemisphereRationalRadialMap_contDiff :
    ContDiff ℝ ∞ roundedHemisphereRationalRadialMap := by
  have hs : ContDiff ℝ ∞
      (fun u : EuclideanSpace ℝ (Fin 4) ↦ ‖u‖ ^ 2) :=
    contDiff_norm_sq ℝ
  have hden : ContDiff ℝ ∞
      (fun u : EuclideanSpace ℝ (Fin 4) ↦ (1 + ‖u‖ ^ 2)⁻¹) := by
    apply (contDiff_const.add hs).inv
    intro u
    positivity
  exact (contDiff_const.mul hden).smul contDiff_id

theorem roundedHemisphereRationalRadialMap_hasFDerivAt_zero :
    HasFDerivAt roundedHemisphereRationalRadialMap
      ((2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 4))) 0 := by
  have hs : HasFDerivAt
      (fun u : EuclideanSpace ℝ (Fin 4) ↦ ‖u‖ ^ 2)
      (0 : StrongDual ℝ (EuclideanSpace ℝ (Fin 4))) 0 := by
    convert! (hasStrictFDerivAt_norm_sq
      (0 : EuclideanSpace ℝ (Fin 4))).hasFDerivAt
    simp only [map_zero, smul_zero]
  have hden : HasFDerivAt
      (fun u : EuclideanSpace ℝ (Fin 4) ↦ (1 + ‖u‖ ^ 2)⁻¹)
      (0 : StrongDual ℝ (EuclideanSpace ℝ (Fin 4))) 0 := by
    convert! (hasFDerivAt_inv _).comp _
      (hs.add (hasFDerivAt_const (1 : ℝ) 0)) <;>
      simp [add_comm]
  have hcoef : HasFDerivAt
      (fun u : EuclideanSpace ℝ (Fin 4) ↦ 2 / (1 + ‖u‖ ^ 2))
      (0 : StrongDual ℝ (EuclideanSpace ℝ (Fin 4))) 0 := by
    convert! (hasFDerivAt_const
      (x := (0 : EuclideanSpace ℝ (Fin 4))) (2 : ℝ)).mul hden ;
      simp
  convert! hcoef.smul (hasFDerivAt_id
    (x := (0 : EuclideanSpace ℝ (Fin 4)))) using 1
  ext v
  simp

theorem roundedHemisphereRadialMap_eq_rational_of_norm_le
    {u : EuclideanSpace ℝ (Fin 4)} (hu : ‖u‖ ≤ 1 / 4) :
    roundedHemisphereRadialMap u = roundedHemisphereRationalRadialMap u := by
  rw [roundedHemisphereRadialMap, roundedHemisphereRationalRadialMap,
    roundedHemisphereTangentialCoefficient_eq_rational (norm_nonneg _) hu]

theorem isLocalDiffeomorphAt_roundedHemisphereRadialMap_zero :
    IsLocalDiffeomorphAt (𝓡 4) (𝓡 4) ∞
      roundedHemisphereRadialMap 0 := by
  let e : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) (by norm_num))
  have hrat : IsLocalDiffeomorphAt (𝓡 4) (𝓡 4) ∞
      roundedHemisphereRationalRadialMap 0 := by
    apply isLocalDiffeomorphAt_of_contDiff_hasFDerivAt_equiv
      roundedHemisphereRationalRadialMap_contDiff
      (e := e) (by
        convert! roundedHemisphereRationalRadialMap_hasFDerivAt_zero using 1)
    simp
  apply rounded_isLocalDiffeomorphAt_congr_of_eventuallyEq (𝓡 4) (𝓡 4) hrat
  filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin 4))
    (show (0 : ℝ) < 1 / 4 by norm_num)] with u hu
  apply roundedHemisphereRadialMap_eq_rational_of_norm_le
  have hult : ‖u‖ < 1 / 4 := by
    simpa [mem_ball, dist_zero_right] using hu
  exact hult.le

theorem isLocalDiffeomorphAt_roundedHemisphereRadialMap
    {u : EuclideanSpace ℝ (Fin 4)} (hu : ‖u‖ < 1) :
    IsLocalDiffeomorphAt (𝓡 4) (𝓡 4) ∞
      roundedHemisphereRadialMap u := by
  by_cases hzero : u = 0
  · simpa [hzero] using isLocalDiffeomorphAt_roundedHemisphereRadialMap_zero
  · exact isLocalDiffeomorphAt_roundedHemisphereRadialMap_of_ne_zero hzero hu

def roundedHemisphereOpenUnitBallOpens :
    Opens (EuclideanSpace ℝ (Fin 4)) :=
  ⟨ball 0 1, isOpen_ball⟩

def roundedHemisphereOpenCapZeroOpens : Opens (Sphere 4) :=
  ⟨coordinateOpenCap 0, by
    change IsOpen ((fun x : Sphere 4 ↦ x.1 3) ⁻¹' Iio 0)
    apply isOpen_Iio.preimage
    fun_prop⟩

def roundedHemisphereStandardCapForward
    (u : roundedHemisphereOpenUnitBallOpens) :
    roundedHemisphereOpenCapZeroOpens :=
  ⟨capSphereMap 0 (⟨u.1, u.2⟩ : ball (0 : EuclideanSpace ℝ (Fin 4)) 1), by
    change capSphereMap 0
      (⟨u.1, u.2⟩ : ball (0 : EuclideanSpace ℝ (Fin 4)) 1) ∈
        coordinateOpenCap 0
    rw [← range_capSphereMap 0]
    exact mem_range_self _⟩

def roundedHemisphereStandardCapInverse
    (y : roundedHemisphereOpenCapZeroOpens) :
    roundedHemisphereOpenUnitBallOpens := by
  refine ⟨equatorAmbientProjection y.1.1, ?_⟩
  change equatorAmbientProjection y.1.1 ∈
    ball (0 : EuclideanSpace ℝ (Fin 4)) 1
  rw [mem_ball_zero_iff]
  have hyneg : y.1.1 3 < 0 := mem_coordinateOpenCap_zero.mp y.2
  have hynorm : ‖y.1.1‖ = 1 := by
    exact mem_sphere_zero_iff_norm.mp y.1.2
  have hsq := norm_equatorAmbientProjection_sq_add_coord_three y.1.1
  nlinarith [norm_nonneg (equatorAmbientProjection y.1.1), sq_pos_of_neg hyneg]

theorem roundedHemisphereStandardCapInverse_left
    (u : roundedHemisphereOpenUnitBallOpens) :
    roundedHemisphereStandardCapInverse
      (roundedHemisphereStandardCapForward u) = u := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [roundedHemisphereStandardCapInverse,
      roundedHemisphereStandardCapForward, capSphereMap, capAmbientMap,
      equatorAmbientProjection]

theorem roundedHemisphereStandardCapInverse_right
    (y : roundedHemisphereOpenCapZeroOpens) :
    roundedHemisphereStandardCapForward
      (roundedHemisphereStandardCapInverse y) = y := by
  have hyrange : y.1 ∈ range (capSphereMap 0) := by
    rw [range_capSphereMap 0]
    exact y.2
  rcases hyrange with ⟨u, hu⟩
  let uOpen : roundedHemisphereOpenUnitBallOpens := ⟨u.1, u.2⟩
  have hyEq : y = roundedHemisphereStandardCapForward uOpen := by
    apply Subtype.ext
    exact hu.symm
  rw [hyEq, roundedHemisphereStandardCapInverse_left]

def roundedHemisphereStandardCapHomeomorph :
    roundedHemisphereOpenUnitBallOpens ≃ₜ roundedHemisphereOpenCapZeroOpens where
  toFun := roundedHemisphereStandardCapForward
  invFun := roundedHemisphereStandardCapInverse
  left_inv := roundedHemisphereStandardCapInverse_left
  right_inv := roundedHemisphereStandardCapInverse_right
  continuous_toFun :=
    (continuous_capSphereMap 0).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (fun y : roundedHemisphereOpenCapZeroOpens ↦
      equatorAmbientProjection y.1.1)
    unfold equatorAmbientProjection
    fun_prop

theorem contMDiff_roundedHemisphereStandardCapForward :
    ContMDiff (𝓡 4) (𝓡 4) ∞
      roundedHemisphereStandardCapForward := by
  have hval : ContMDiff (𝓡 4) (𝓡 4) ∞
      (Subtype.val : roundedHemisphereOpenUnitBallOpens →
        EuclideanSpace ℝ (Fin 4)) :=
    contMDiff_subtype_val
  have hsq : ContMDiff (𝓡 4) (modelWithCornersSelf ℝ ℝ) ∞
      (fun u : roundedHemisphereOpenUnitBallOpens ↦ ‖u.1‖ ^ 2) :=
    (contDiff_norm_sq ℝ).contMDiff.comp hval
  have hrad : ContMDiff (𝓡 4) (modelWithCornersSelf ℝ ℝ) ∞
      (fun u : roundedHemisphereOpenUnitBallOpens ↦ 1 - ‖u.1‖ ^ 2) :=
    contMDiff_const.sub hsq
  have hsqrt : ContMDiff (𝓡 4) (modelWithCornersSelf ℝ ℝ) ∞
      (fun u : roundedHemisphereOpenUnitBallOpens ↦ Real.sqrt (1 - ‖u.1‖ ^ 2)) := by
    intro u
    have hu : ‖u.1‖ < 1 := mem_ball_zero_iff.mp u.2
    have hne : 1 - ‖u.1‖ ^ 2 ≠ 0 := by
      nlinarith [norm_nonneg u.1]
    exact (Real.contDiffAt_sqrt hne).contMDiffAt.comp u hrad.contMDiffAt
  have hcoord (j : Fin 4) : ContMDiff (𝓡 4)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun u : roundedHemisphereOpenUnitBallOpens ↦ u.1 j) := by
    have heval : ContDiff ℝ ∞
        (fun u : EuclideanSpace ℝ (Fin 4) ↦ u j) := by fun_prop
    exact heval.contMDiff.comp hval
  let raw : roundedHemisphereOpenUnitBallOpens → Fin 5 → ℝ := fun u ↦
    ![u.1 0, u.1 1, u.1 2, -Real.sqrt (1 - ‖u.1‖ ^ 2), u.1 3]
  have hraw : ContMDiff (𝓡 4) (modelWithCornersSelf ℝ (Fin 5 → ℝ)) ∞
      raw := by
    rw [contMDiff_pi_space]
    intro i
    fin_cases i
    · simpa [raw] using hcoord 0
    · simpa [raw] using hcoord 1
    · simpa [raw] using hcoord 2
    · simpa [raw] using hsqrt.neg
    · simpa [raw] using hcoord 3
  have htoLp : ContMDiff (modelWithCornersSelf ℝ (Fin 5 → ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5))) ∞
      (WithLp.toLp 2) :=
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin 5 ↦ ℝ)).symm.toContinuousLinearMap.contMDiff
  have hambient : ContMDiff (𝓡 4) (modelWithCornersSelf ℝ
      (EuclideanSpace ℝ (Fin 5))) ∞
      (fun u : roundedHemisphereOpenUnitBallOpens ↦
        capAmbientMap 0 u.1) :=
    (htoLp.comp hraw).congr fun u ↦ by
      ext i
      fin_cases i <;> simp [raw, capAmbientMap]
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) :=
    ⟨by simp⟩
  have hsphere : ContMDiff (𝓡 4) (𝓡 4) ∞
      (fun u : roundedHemisphereOpenUnitBallOpens ↦
        capSphereMap 0
          (⟨u.1, u.2⟩ : ball (0 : EuclideanSpace ℝ (Fin 4)) 1)) := by
    have hcod := hambient.codRestrict_sphere (n := 4) (fun u ↦ by
      simpa [mem_sphere_zero_iff_norm] using
        norm_capAmbientMap_of_mem_ball 0 u.2)
    exact hcod.congr fun _ ↦ rfl
  apply (ContMDiff.subtypeVal_comp_iff roundedHemisphereOpenCapZeroOpens _).mp
  exact hsphere.congr fun _ ↦ rfl

theorem contMDiff_roundedHemisphereStandardCapInverse :
    ContMDiff (𝓡 4) (𝓡 4) ∞
      roundedHemisphereStandardCapInverse := by
  apply (ContMDiff.subtypeVal_comp_iff roundedHemisphereOpenUnitBallOpens _).mp
  have hproj : ContDiff ℝ ∞ equatorAmbientProjection := by
    unfold equatorAmbientProjection
    rw [contDiff_piLp]
    intro i
    fin_cases i <;>
      simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
      fun_prop
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) :=
    ⟨by simp⟩
  exact (hproj.contMDiff.comp
    (contMDiff_coe_sphere.comp contMDiff_subtype_val)).congr fun _ ↦ rfl

def roundedHemisphereStandardCapDiffeomorph :
    roundedHemisphereOpenUnitBallOpens ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯
      roundedHemisphereOpenCapZeroOpens where
  toEquiv := roundedHemisphereStandardCapHomeomorph.toEquiv
  contMDiff_toFun := contMDiff_roundedHemisphereStandardCapForward
  contMDiff_invFun := contMDiff_roundedHemisphereStandardCapInverse

theorem norm_roundedHemisphereRadialMap
    {u : EuclideanSpace ℝ (Fin 4)} (hu : ‖u‖ ≤ 1) :
    ‖roundedHemisphereRadialMap u‖ =
      roundedHemisphereTangentialRadius ‖u‖ := by
  by_cases hzero : u = 0
  · subst u
    simp [roundedHemisphereRadialMap]
  · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hzero
    rw [roundedHemisphereRadialMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (roundedHemisphereTangentialCoefficient_pos hpos hu),
      roundedHemisphereTangentialCoefficient_mul hpos]

theorem roundedHemisphereTangentialRadius_lt_one
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    roundedHemisphereTangentialRadius r < 1 := by
  have h := roundedHemisphereTangentialRadius_strictMonoOn
    ⟨hr0, hr1.le⟩ (show (1 : ℝ) ∈ Icc 0 1 by simp) hr1
  simpa using h

def roundedHemisphereRadialOpenMap
    (u : roundedHemisphereOpenUnitBallOpens) :
    roundedHemisphereOpenUnitBallOpens :=
  ⟨roundedHemisphereRadialMap u.1, by
    change roundedHemisphereRadialMap u.1 ∈
      ball (0 : EuclideanSpace ℝ (Fin 4)) 1
    rw [mem_ball_zero_iff,
      norm_roundedHemisphereRadialMap (mem_ball_zero_iff.mp u.2).le]
    exact roundedHemisphereTangentialRadius_lt_one
      (norm_nonneg _) (mem_ball_zero_iff.mp u.2)⟩

@[simp] theorem roundedHemisphereRadialOpenMap_coe
    (u : roundedHemisphereOpenUnitBallOpens) :
    (roundedHemisphereRadialOpenMap u : EuclideanSpace ℝ (Fin 4)) =
      roundedHemisphereRadialMap u.1 :=
  rfl

theorem isLocalDiffeomorph_roundedHemisphereRadialOpenMap :
    IsLocalDiffeomorph (𝓡 4) (𝓡 4) ∞
      roundedHemisphereRadialOpenMap := by
  intro u
  let hU := isLocalDiffeomorph_opensSubtypeVal (𝓡 4)
    roundedHemisphereOpenUnitBallOpens u
  have hrad : IsLocalDiffeomorphAt (𝓡 4) (𝓡 4) ∞
      roundedHemisphereRadialMap u.1 :=
    isLocalDiffeomorphAt_roundedHemisphereRadialMap
      (mem_ball_zero_iff.mp u.2)
  have hcomp : IsLocalDiffeomorphAt (𝓡 4) (𝓡 4) ∞
      (roundedHemisphereRadialMap ∘
        (Subtype.val : roundedHemisphereOpenUnitBallOpens →
          EuclideanSpace ℝ (Fin 4))) u :=
    hU.comp (𝓡 4) (EuclideanSpace ℝ (Fin 4)) hrad
  let v := roundedHemisphereRadialOpenMap u
  let hV := isLocalDiffeomorph_opensSubtypeVal (𝓡 4)
    roundedHemisphereOpenUnitBallOpens v
  let phiOne := Classical.choose hcomp
  let phi : PartialDiffeomorph (𝓡 4) (𝓡 4)
      roundedHemisphereOpenUnitBallOpens
      roundedHemisphereOpenUnitBallOpens ∞ :=
    phiOne.trans hV.localInverse
  refine ⟨phi, ?_, ?_⟩
  · change u ∈ phiOne.source ∩ phiOne ⁻¹' hV.localInverse.source
    refine ⟨hcomp.choose_spec.1, ?_⟩
    change phiOne u ∈ hV.localInverse.source
    rw [← hcomp.choose_spec.2 hcomp.choose_spec.1]
    exact hV.localInverse_mem_source
  · intro z hz
    change roundedHemisphereRadialOpenMap z = hV.localInverse (phiOne z)
    have hradEq : phiOne z = roundedHemisphereRadialMap z.1 :=
      (hcomp.choose_spec.2 hz.1).symm
    have hz2 : phiOne z ∈ hV.localInverse.source := hz.2
    rw [hradEq]
    apply Subtype.ext
    exact (hV.localInverse_right_inv
      (y := roundedHemisphereRadialMap z.1) (by rwa [← hradEq])).symm

def roundedHemisphereInteriorMap
    (u : roundedHemisphereOpenUnitBallOpens) :
    roundedHemisphereOpenCapZeroOpens :=
  ⟨roundedHemisphereSphereMap
      ⟨u.1, mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp u.2).le⟩,
    roundedHemisphereSphereMap_mem_coordinateOpenCap_zero_iff
      ⟨u.1, mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp u.2).le⟩
      |>.mpr (mem_ball_zero_iff.mp u.2)⟩

@[simp] theorem roundedHemisphereInteriorMap_coe
    (u : roundedHemisphereOpenUnitBallOpens) :
    (roundedHemisphereInteriorMap u : Sphere 4) =
      roundedHemisphereSphereMap
        ⟨u.1, mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp u.2).le⟩ :=
  rfl

theorem roundedHemisphereStandardCapInverse_interiorMap
    (u : roundedHemisphereOpenUnitBallOpens) :
    roundedHemisphereStandardCapDiffeomorph.symm
        (roundedHemisphereInteriorMap u) =
      roundedHemisphereRadialOpenMap u := by
  apply Subtype.ext
  change equatorAmbientProjection (roundedHemisphereAmbientMap u.1) = _
  exact equatorAmbientProjection_roundedHemisphereAmbientMap u.1

theorem isLocalDiffeomorph_roundedHemisphereInteriorMap :
    IsLocalDiffeomorph (𝓡 4) (𝓡 4) ∞
      roundedHemisphereInteriorMap := by
  intro u
  have hcomp : IsLocalDiffeomorphAt (𝓡 4) (𝓡 4) ∞
      (roundedHemisphereStandardCapDiffeomorph ∘
        roundedHemisphereRadialOpenMap) u :=
    isLocalDiffeomorph_roundedHemisphereRadialOpenMap u |>.comp
      (𝓡 4) roundedHemisphereOpenCapZeroOpens
      (roundedHemisphereStandardCapDiffeomorph.isLocalDiffeomorph
        (roundedHemisphereRadialOpenMap u))
  apply rounded_isLocalDiffeomorphAt_congr_of_eventuallyEq
    (𝓡 4) (𝓡 4) hcomp
  filter_upwards [] with z
  apply roundedHemisphereStandardCapDiffeomorph.symm.injective
  calc
    roundedHemisphereStandardCapDiffeomorph.symm
        (roundedHemisphereInteriorMap z) =
        roundedHemisphereRadialOpenMap z :=
      roundedHemisphereStandardCapInverse_interiorMap z
    _ = roundedHemisphereStandardCapDiffeomorph.symm
        ((roundedHemisphereStandardCapDiffeomorph ∘
          roundedHemisphereRadialOpenMap) z) := by
      rw [Function.comp_apply,
        roundedHemisphereStandardCapDiffeomorph.symm_apply_apply]

theorem bijective_roundedHemisphereInteriorMap :
    Bijective roundedHemisphereInteriorMap := by
  constructor
  · intro u v huv
    let uBall : EuclideanFourBall :=
      ⟨u.1, mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp u.2).le⟩
    let vBall : EuclideanFourBall :=
      ⟨v.1, mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp v.2).le⟩
    have hsphere : roundedHemisphereSphereMap uBall =
        roundedHemisphereSphereMap vBall :=
      congrArg Subtype.val huv
    have hball : uBall = vBall :=
      injective_roundedHemisphereSphereMap hsphere
    exact Subtype.ext (congrArg (fun z : EuclideanFourBall ↦ z.1) hball)
  · intro y
    have hyClosed : y.1 ∈ coordinateClosedCapZero := by
      rw [coordinateClosedCapZero, mem_compl_iff,
        mem_coordinateOpenCap_one]
      have hyneg : y.1.1 3 < 0 :=
        mem_coordinateOpenCap_zero.mp y.2
      linarith
    rcases coordinateClosedCapZero_subset_range_roundedHemisphereSphereMap
      hyClosed with ⟨u, hu⟩
    have huOpen : ‖u.1‖ < 1 :=
      roundedHemisphereSphereMap_mem_coordinateOpenCap_zero_iff u |>.mp <| by
        rw [hu]
        exact y.2
    let uOpen : roundedHemisphereOpenUnitBallOpens :=
      ⟨u.1, mem_ball_zero_iff.mpr huOpen⟩
    refine ⟨uOpen, ?_⟩
    apply Subtype.ext
    exact hu

noncomputable def roundedHemisphereInteriorHomeomorph :
    roundedHemisphereOpenUnitBallOpens ≃ₜ
      roundedHemisphereOpenCapZeroOpens :=
  isLocalDiffeomorph_roundedHemisphereInteriorMap.isLocalHomeomorph
    |>.toHomeomorphOfBijective bijective_roundedHemisphereInteriorMap

@[simp] theorem roundedHemisphereInteriorHomeomorph_apply
    (u : roundedHemisphereOpenUnitBallOpens) :
    roundedHemisphereInteriorHomeomorph u =
      roundedHemisphereInteriorMap u :=
  rfl

noncomputable def roundedHemisphereInteriorDiffeomorph :
    roundedHemisphereOpenUnitBallOpens ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯
      roundedHemisphereOpenCapZeroOpens :=
  diffeomorphOfHomeomorphIsLocalDiffeomorph
    (𝓡 4) (𝓡 4) roundedHemisphereInteriorHomeomorph
    isLocalDiffeomorph_roundedHemisphereInteriorMap

@[simp] theorem roundedHemisphereInteriorDiffeomorph_apply
    (u : roundedHemisphereOpenUnitBallOpens) :
    roundedHemisphereInteriorDiffeomorph u =
      roundedHemisphereInteriorMap u :=
  rfl

private def roundedHemisphereFourBallInteriorOpens :
    Opens EuclideanFourBall :=
  ⟨Subtype.val ⁻¹' ball (0 : EuclideanSpace ℝ (Fin 4)) 1,
    isOpen_ball.preimage continuous_subtype_val⟩

private def roundedHemisphereOpenBallInteriorEquiv :
    roundedHemisphereOpenUnitBallOpens ≃
      roundedHemisphereFourBallInteriorOpens where
  toFun u := ⟨⟨u.1, ball_subset_closedBall u.2⟩, u.2⟩
  invFun u := ⟨u.1.1, u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem contMDiff_roundedHemisphereOpenBallInteriorEquiv :
    ContMDiff (𝓡 4) euclideanFourBallModel ∞
      roundedHemisphereOpenBallInteriorEquiv := by
  rw [← ContMDiff.subtypeVal_comp_iff
    roundedHemisphereFourBallInteriorOpens]
  apply contMDiff_euclideanClosedBall_of_contMDiff_val
  exact contMDiff_subtype_val.congr fun _ ↦ rfl

private theorem contMDiff_roundedHemisphereOpenBallInteriorEquiv_symm :
    ContMDiff euclideanFourBallModel (𝓡 4) ∞
      roundedHemisphereOpenBallInteriorEquiv.symm := by
  rw [← ContMDiff.subtypeVal_comp_iff
    roundedHemisphereOpenUnitBallOpens]
  exact contMDiff_closedUnitBall_inclusion
    (EuclideanSpace ℝ (Fin 4)) |>.comp contMDiff_subtype_val

private def roundedHemisphereOpenBallInteriorDiffeomorph :
    roundedHemisphereOpenUnitBallOpens ≃ₘ^∞⟮𝓡 4,
      euclideanFourBallModel⟯ roundedHemisphereFourBallInteriorOpens where
  toEquiv := roundedHemisphereOpenBallInteriorEquiv
  contMDiff_toFun :=
    contMDiff_roundedHemisphereOpenBallInteriorEquiv
  contMDiff_invFun :=
    contMDiff_roundedHemisphereOpenBallInteriorEquiv_symm

private def roundedHemisphereOpenBallToFourBall
    (u : roundedHemisphereOpenUnitBallOpens) : EuclideanFourBall :=
  ⟨u.1, ball_subset_closedBall u.2⟩

private theorem rounded_isLocalDiffeomorphAt_of_parametrization_models
    {A B C HA HB HC P M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [TopologicalSpace HA] [TopologicalSpace HB] [TopologicalSpace HC]
    (K : ModelWithCorners ℝ A HA) (I : ModelWithCorners ℝ B HB)
    (J : ModelWithCorners ℝ C HC)
    [TopologicalSpace P] [ChartedSpace HA P]
    [TopologicalSpace M] [ChartedSpace HB M]
    [TopologicalSpace N] [ChartedSpace HC N]
    (F : M → N) (c : P → M) (p : P)
    (hc : IsLocalDiffeomorphAt K I ∞ c p)
    (hFc : IsLocalDiffeomorphAt K J ∞ (F ∘ c) p) :
    IsLocalDiffeomorphAt I J ∞ F (c p) := by
  have hcomp : IsLocalDiffeomorphAt I J ∞
      ((F ∘ c) ∘ hc.localInverse) (c p) :=
    hc.localInverse_isLocalDiffeomorphAt.comp J N (by
      have hinv : hc.localInverse (c p) = p :=
        hc.localInverse_left_inv hc.localInverse_mem_target
      simpa [hinv] using hFc)
  apply rounded_isLocalDiffeomorphAt_congr_of_eventuallyEq I J hcomp
  filter_upwards [hc.localInverse_eventuallyEq_right] with y hy
  simp only [Function.comp_apply] at hy ⊢
  simp [hy]

private theorem isLocalDiffeomorph_roundedHemisphereOpenBallToFourBall :
    IsLocalDiffeomorph (𝓡 4) euclideanFourBallModel ∞
      roundedHemisphereOpenBallToFourBall := by
  intro u
  have hOne := roundedHemisphereOpenBallInteriorDiffeomorph.isLocalDiffeomorph u
  have hTwo := isLocalDiffeomorph_opensSubtypeVal euclideanFourBallModel
    roundedHemisphereFourBallInteriorOpens
    (roundedHemisphereOpenBallInteriorDiffeomorph u)
  have hcomp := hOne.comp euclideanFourBallModel EuclideanFourBall hTwo
  apply rounded_isLocalDiffeomorphAt_congr_of_eventuallyEq
    (𝓡 4) euclideanFourBallModel hcomp
  filter_upwards [] with z
  rfl

theorem isLocalDiffeomorphAt_roundedHemisphereSphereMap_of_mem_interior
    (u : EuclideanFourBall) (hu : ‖u.1‖ < 1) :
    IsLocalDiffeomorphAt euclideanFourBallModel (𝓡 4) ∞
      roundedHemisphereSphereMap u := by
  let v : roundedHemisphereOpenUnitBallOpens :=
    ⟨u.1, mem_ball_zero_iff.mpr hu⟩
  have hv : roundedHemisphereOpenBallToFourBall v = u := by
    apply Subtype.ext
    rfl
  have htarget : IsLocalDiffeomorph (𝓡 4) (𝓡 4) ∞
      ((Subtype.val : roundedHemisphereOpenCapZeroOpens → Sphere 4) ∘
        roundedHemisphereInteriorDiffeomorph) := by
    intro z
    exact roundedHemisphereInteriorDiffeomorph.isLocalDiffeomorph z |>.comp
      (𝓡 4) (Sphere 4)
      (isLocalDiffeomorph_opensSubtypeVal (𝓡 4)
        roundedHemisphereOpenCapZeroOpens
        (roundedHemisphereInteriorDiffeomorph z))
  have hcomp : IsLocalDiffeomorphAt (𝓡 4) (𝓡 4) ∞
      (roundedHemisphereSphereMap ∘
        roundedHemisphereOpenBallToFourBall) v := by
    apply rounded_isLocalDiffeomorphAt_congr_of_eventuallyEq
      (𝓡 4) (𝓡 4) (htarget v)
    filter_upwards [] with z
    rfl
  have hcancel := rounded_isLocalDiffeomorphAt_of_parametrization_models
    (𝓡 4) euclideanFourBallModel (𝓡 4)
    roundedHemisphereSphereMap
    roundedHemisphereOpenBallToFourBall v
    (isLocalDiffeomorph_roundedHemisphereOpenBallToFourBall v) hcomp
  simpa [hv] using hcancel

/-- Removing the equator from the closed cap leaves exactly coordinate open cap zero. -/
public theorem roundedHemisphereClosedCapZero_offBoundary :
    collaredCutSideOffBoundary coordinateClosedCapZero
      coordinateEquator = coordinateOpenCap 0 := by
  ext x
  change (x ∈ coordinateClosedCapZero ∧ x ∉ coordinateEquator) ↔
    x ∈ coordinateOpenCap 0
  rw [coordinateClosedCapZero, mem_compl_iff,
    mem_coordinateOpenCap_one, mem_coordinateOpenCap_zero]
  change (¬0 < x.1 3 ∧ x.1 3 ≠ 0) ↔ x.1 3 < 0
  constructor
  · rintro ⟨hpos, hzero⟩
    exact lt_of_le_of_ne (le_of_not_gt hpos) hzero
  · intro hneg
    exact ⟨not_lt_of_ge hneg.le, hneg.ne⟩

/-- The off-boundary part of the closed coordinate cap is open in the sphere. -/
public theorem isOpen_roundedHemisphereClosedCapZero_offBoundary :
    IsOpen (collaredCutSideOffBoundary coordinateClosedCapZero
      coordinateEquator) := by
  rw [roundedHemisphereClosedCapZero_offBoundary]
  exact roundedHemisphereOpenCapZeroOpens.2

/-- The explicit equator collar on the closed coordinate cap. -/
@[expose] public def roundedHemisphereClosedCapCollarAmbient
    (p : EuclideanFourBallCollarDomain) : Sphere 4 :=
  equatorCollarSphereMap (p.1, roundedHemisphereEquatorTime p.2)

theorem roundedHemisphereClosedCapCollarAmbient_eq_sphereMap
    (p : EuclideanFourBallCollarDomain) :
    roundedHemisphereClosedCapCollarAmbient p =
      roundedHemisphereSphereMap (euclideanFourBallSmoothCollar p) := by
  exact (roundedHemisphereSphereMap_euclideanFourBallSmoothCollar p).symm

/-- The explicit equator collar takes values in the closed coordinate cap. -/
public theorem range_roundedHemisphereClosedCapCollarAmbient_subset :
    range roundedHemisphereClosedCapCollarAmbient ⊆
      coordinateClosedCapZero := by
  rintro _ ⟨p, rfl⟩
  rw [roundedHemisphereClosedCapCollarAmbient_eq_sphereMap]
  exact roundedHemisphereSphereMap_mem_coordinateClosedCapZero
    (euclideanFourBallSmoothCollar p)

/-- The explicit equator collar corestricted to the closed coordinate cap. -/
@[expose] public def roundedHemisphereClosedCapBoundaryCollar
    (p : EuclideanFourBallCollarDomain) :
    CollaredCutSide coordinateClosedCapZero :=
  collaredCutSideHalfCollarMap coordinateClosedCapZero
    roundedHemisphereClosedCapCollarAmbient
    range_roundedHemisphereClosedCapCollarAmbient_subset p

/-- Coercing the corestricted collar recovers its ambient sphere map. -/
@[simp] public theorem roundedHemisphereClosedCapBoundaryCollar_coe
    (p : EuclideanFourBallCollarDomain) :
    (roundedHemisphereClosedCapBoundaryCollar p : Sphere 4) =
      roundedHemisphereClosedCapCollarAmbient p :=
  rfl

/-- The corestricted equator collar is an open embedding. -/
public theorem isOpenEmbedding_roundedHemisphereClosedCapBoundaryCollar :
    IsOpenEmbedding roundedHemisphereClosedCapBoundaryCollar := by
  have hcomp : IsOpenEmbedding
      (roundedHemisphereClosedCapHomeomorph ∘
        euclideanFourBallSmoothCollar) :=
    roundedHemisphereClosedCapHomeomorph.isOpenEmbedding.comp
      isOpenEmbedding_euclideanFourBallSmoothCollar
  convert hcomp using 1
  funext p
  apply Subtype.ext
  exact roundedHemisphereClosedCapCollarAmbient_eq_sphereMap p

/-- The cap is covered by its off-boundary region and its explicit collar. -/
public theorem roundedHemisphereClosedCapZero_cover
    (z : CollaredCutSide coordinateClosedCapZero) :
    z.1 ∈ collaredCutSideOffBoundary coordinateClosedCapZero
        coordinateEquator ∨
      z.1 ∈ range roundedHemisphereClosedCapCollarAmbient := by
  let zClosed : coordinateClosedCapZero := ⟨z.1, z.2⟩
  let u : EuclideanFourBall := roundedHemisphereClosedCapHomeomorph.symm zClosed
  have hmap : roundedHemisphereSphereMap u = z.1 := by
    have h := roundedHemisphereClosedCapHomeomorph.apply_symm_apply zClosed
    exact congrArg Subtype.val h
  by_cases hu : ‖u.1‖ < 1
  · left
    rw [roundedHemisphereClosedCapZero_offBoundary]
    rw [← hmap]
    exact roundedHemisphereSphereMap_mem_coordinateOpenCap_zero_iff u |>.mpr hu
  · right
    have huNorm : ‖u.1‖ = 1 := by
      exact le_antisymm (mem_closedBall_zero_iff.mp u.2)
        (le_of_not_gt hu)
    let s : Sphere 3 := ⟨u.1, by
      simpa [mem_sphere_zero_iff_norm] using huNorm⟩
    refine ⟨(s, euclideanFourBallCollarZero), ?_⟩
    rw [roundedHemisphereClosedCapCollarAmbient_eq_sphereMap]
    rw [show euclideanFourBallSmoothCollar
        (s, euclideanFourBallCollarZero) = u by
      apply Subtype.ext
      exact euclideanFourBallSmoothCollar_zero_coe s]
    exact hmap

/-- The equator pulls back along the collar to precisely the collar-domain model boundary. -/
public theorem preimage_roundedHemisphereClosedCapCollarAmbient_equator :
    roundedHemisphereClosedCapCollarAmbient ⁻¹' coordinateEquator =
      euclideanFourBallCollarModel.boundary
        EuclideanFourBallCollarDomain := by
  rw [euclideanFourBallCollarModel_boundary]
  ext p
  change (roundedHemisphereClosedCapCollarAmbient p).1 3 = 0 ↔
    p.1 ∈ (univ : Set (Sphere 3)) ∧
      p.2 ∈ ({euclideanFourBallCollarZero} :
        Set EuclideanFourBallCollarInterval)
  simp only [mem_univ, mem_singleton_iff, true_and]
  rw [roundedHemisphereClosedCapCollarAmbient,
    equatorCollarSphereMap_coord_three,
    roundedHemisphereEquatorTime_value]
  constructor
  · intro hp
    apply Subtype.ext
    apply Subtype.ext
    simpa using (neg_eq_zero.mp hp)
  · intro hp
    rw [hp]
    simp

theorem isLocalDiffeomorphOn_roundedHemisphereClosedCapCollarAmbient_natural :
    IsLocalDiffeomorphOn euclideanFourBallCollarModel (𝓡 4) ∞
      roundedHemisphereClosedCapCollarAmbient
      (roundedHemisphereClosedCapCollarAmbient ⁻¹'
        collaredCutSideOffBoundary coordinateClosedCapZero
          coordinateEquator) := by
  rintro ⟨p, hp⟩
  have hcap : roundedHemisphereSphereMap
      (euclideanFourBallSmoothCollar p) ∈ coordinateOpenCap 0 := by
    rw [← roundedHemisphereClosedCapCollarAmbient_eq_sphereMap]
    simpa only [mem_preimage,
      roundedHemisphereClosedCapZero_offBoundary] using hp
  have hinterior :
      ‖(euclideanFourBallSmoothCollar p : EuclideanFourBall).1‖ < 1 :=
    roundedHemisphereSphereMap_mem_coordinateOpenCap_zero_iff
      (euclideanFourBallSmoothCollar p) |>.mp hcap
  have hOne := isLocalDiffeomorph_euclideanFourBallSmoothCollar p
  have hTwo :=
    isLocalDiffeomorphAt_roundedHemisphereSphereMap_of_mem_interior
      (euclideanFourBallSmoothCollar p) hinterior
  have hcomp := hOne.comp (𝓡 4) (Sphere 4) hTwo
  apply rounded_isLocalDiffeomorphAt_congr_of_eventuallyEq
    euclideanFourBallCollarModel (𝓡 4) hcomp
  filter_upwards [] with q
  exact roundedHemisphereClosedCapCollarAmbient_eq_sphereMap q

private theorem roundedHemisphereCommonFourBallAtlas_compatible :
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
    ∀ i j : CollaredCutSideAtlasIndex euclideanFourBallAmbientCarrier
        euclideanFourBallAmbientBoundary EuclideanFourBallCollarDomain,
      (collaredCutSideAtlasChart
        euclideanFourBallAmbientCarrier euclideanFourBallAmbientBoundary
        isOpen_euclideanFourBallAmbientOffBoundary
        euclideanFourBallSmoothCollarAmbient
        range_euclideanFourBallSmoothCollarAmbient_subset
        isOpenEmbedding_collaredCutSide_euclideanFourBallSmoothCollarAmbient i).symm.trans
      (collaredCutSideAtlasChart
        euclideanFourBallAmbientCarrier euclideanFourBallAmbientBoundary
        isOpen_euclideanFourBallAmbientOffBoundary
        euclideanFourBallSmoothCollarAmbient
        range_euclideanFourBallSmoothCollarAmbient_subset
        isOpenEmbedding_collaredCutSide_euclideanFourBallSmoothCollarAmbient j) ∈
        contDiffGroupoid ∞ coordinateUnlinkExteriorModel := by
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ EuclideanFourBall :=
    isManifold_coordinateUnlinkExteriorCommonModelEuclideanFourBall
  intro i j
  apply IsManifold.compatible_of_mem_maximalAtlas
  · apply IsManifold.subset_maximalAtlas
    exact ⟨i, rfl⟩
  · apply IsManifold.subset_maximalAtlas
    exact ⟨j, rfl⟩

private theorem isLocalDiffeomorph_roundedHemisphereCommonFourBallOffMap :
    letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (collaredCutSideOffBoundaryOpensMap euclideanFourBallAmbientCarrier
        euclideanFourBallAmbientBoundary
        isOpen_euclideanFourBallAmbientOffBoundary) := by
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (EuclideanSpace ℝ (Fin 4)) := by
    exact
      isOpenEmbedding_coordinateUnlinkExteriorEuclideanAmbientChart.isManifold_singleton
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
  exact isLocalDiffeomorph_collaredCutSideOffBoundaryMap
    coordinateUnlinkExteriorModel ∞ euclideanFourBallAmbientCarrier
    euclideanFourBallAmbientBoundary
    isOpen_euclideanFourBallAmbientOffBoundary
    euclideanFourBallSmoothCollarAmbient
    range_euclideanFourBallSmoothCollarAmbient_subset
    isOpenEmbedding_collaredCutSide_euclideanFourBallSmoothCollarAmbient
    euclideanFourBallAmbient_cover
    roundedHemisphereCommonFourBallAtlas_compatible

section CommonSphereAtlas

variable [ChartedSpace CoordinateUnlinkExteriorModelSpace (Sphere 4)]
variable [IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4)]

omit [IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4)] in
theorem isLocalDiffeomorphOn_roundedHemisphereClosedCapCollarAmbient_common
    (eSphere : Sphere 4 ≃ₘ^∞⟮𝓡 4,
      coordinateUnlinkExteriorModel⟯ Sphere 4)
    (heSphere : ∀ x, eSphere x = x) :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      roundedHemisphereClosedCapCollarAmbient
      (roundedHemisphereClosedCapCollarAmbient ⁻¹'
        collaredCutSideOffBoundary coordinateClosedCapZero
          coordinateEquator) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  rintro ⟨p, hp⟩
  have hOne :=
    coordinateUnlinkExteriorRechartedFourBallCollarIdentityDiffeomorph
      |>.isLocalDiffeomorph p
  have hTwo :=
    isLocalDiffeomorphOn_roundedHemisphereClosedCapCollarAmbient_natural
      ⟨p, hp⟩
  have hThree := eSphere.isLocalDiffeomorph
    (roundedHemisphereClosedCapCollarAmbient p)
  have hcomp := hOne.comp (𝓡 4) (Sphere 4) hTwo |>.comp
    coordinateUnlinkExteriorModel (Sphere 4) hThree
  apply rounded_isLocalDiffeomorphAt_congr_of_eventuallyEq
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel hcomp
  filter_upwards [] with q
  simp only [Function.comp_apply,
    coordinateUnlinkExteriorRechartedFourBallCollarIdentityDiffeomorph_apply,
    heSphere]

@[instance_reducible]
def roundedHemisphereClosedCapChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CollaredCutSide coordinateClosedCapZero) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  exact collaredCutSideChartedSpace coordinateClosedCapZero
    coordinateEquator
    isOpen_roundedHemisphereClosedCapZero_offBoundary
    roundedHemisphereClosedCapCollarAmbient
    range_roundedHemisphereClosedCapCollarAmbient_subset
    isOpenEmbedding_roundedHemisphereClosedCapBoundaryCollar
    roundedHemisphereClosedCapZero_cover

theorem isManifold_roundedHemisphereClosedCapChartedSpace
    (hlocal :
      letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
      IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        roundedHemisphereClosedCapCollarAmbient
        (roundedHemisphereClosedCapCollarAmbient ⁻¹'
          collaredCutSideOffBoundary coordinateClosedCapZero
            coordinateEquator)) :
    letI := roundedHemisphereClosedCapChartedSpace
    IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide coordinateClosedCapZero) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  exact isManifold_collaredCutSideChartedSpace_of_localDiffeomorphOn
    coordinateUnlinkExteriorModel ∞ coordinateClosedCapZero
    coordinateEquator
    isOpen_roundedHemisphereClosedCapZero_offBoundary
    roundedHemisphereClosedCapCollarAmbient
    range_roundedHemisphereClosedCapCollarAmbient_subset
    isOpenEmbedding_roundedHemisphereClosedCapBoundaryCollar
    roundedHemisphereClosedCapZero_cover hlocal

private theorem roundedHemisphereClosedCapAtlas_compatible
    (hlocal :
      letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
      IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        roundedHemisphereClosedCapCollarAmbient
        (roundedHemisphereClosedCapCollarAmbient ⁻¹'
          collaredCutSideOffBoundary coordinateClosedCapZero
            coordinateEquator)) :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    letI := roundedHemisphereClosedCapChartedSpace
    ∀ i j : CollaredCutSideAtlasIndex coordinateClosedCapZero
        coordinateEquator EuclideanFourBallCollarDomain,
      (collaredCutSideAtlasChart coordinateClosedCapZero
        coordinateEquator
        isOpen_roundedHemisphereClosedCapZero_offBoundary
        roundedHemisphereClosedCapCollarAmbient
        range_roundedHemisphereClosedCapCollarAmbient_subset
        isOpenEmbedding_roundedHemisphereClosedCapBoundaryCollar i).symm.trans
      (collaredCutSideAtlasChart coordinateClosedCapZero
        coordinateEquator
        isOpen_roundedHemisphereClosedCapZero_offBoundary
        roundedHemisphereClosedCapCollarAmbient
        range_roundedHemisphereClosedCapCollarAmbient_subset
        isOpenEmbedding_roundedHemisphereClosedCapBoundaryCollar j) ∈
        contDiffGroupoid ∞ coordinateUnlinkExteriorModel := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let _ := roundedHemisphereClosedCapChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide coordinateClosedCapZero) :=
    isManifold_roundedHemisphereClosedCapChartedSpace hlocal
  intro i j
  apply IsManifold.compatible_of_mem_maximalAtlas
  · apply IsManifold.subset_maximalAtlas
    exact ⟨i, rfl⟩
  · apply IsManifold.subset_maximalAtlas
    exact ⟨j, rfl⟩

private theorem isLocalDiffeomorph_roundedHemisphereClosedCapOffMap
    (hlocal :
      letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
      IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        roundedHemisphereClosedCapCollarAmbient
        (roundedHemisphereClosedCapCollarAmbient ⁻¹'
          collaredCutSideOffBoundary coordinateClosedCapZero
            coordinateEquator)) :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    letI := roundedHemisphereClosedCapChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (collaredCutSideOffBoundaryOpensMap coordinateClosedCapZero
        coordinateEquator
        isOpen_roundedHemisphereClosedCapZero_offBoundary) := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ := roundedHemisphereClosedCapChartedSpace
  exact isLocalDiffeomorph_collaredCutSideOffBoundaryMap
    coordinateUnlinkExteriorModel ∞ coordinateClosedCapZero
    coordinateEquator
    isOpen_roundedHemisphereClosedCapZero_offBoundary
    roundedHemisphereClosedCapCollarAmbient
    range_roundedHemisphereClosedCapCollarAmbient_subset
    isOpenEmbedding_roundedHemisphereClosedCapBoundaryCollar
    roundedHemisphereClosedCapZero_cover
    (roundedHemisphereClosedCapAtlas_compatible hlocal)

private theorem isLocalDiffeomorph_roundedHemisphereClosedCapBoundaryCollar
    (hlocal :
      letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
      IsLocalDiffeomorphOn coordinateUnlinkExteriorModel
        coordinateUnlinkExteriorModel ∞
        roundedHemisphereClosedCapCollarAmbient
        (roundedHemisphereClosedCapCollarAmbient ⁻¹'
          collaredCutSideOffBoundary coordinateClosedCapZero
            coordinateEquator)) :
    letI := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
    letI := roundedHemisphereClosedCapChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      roundedHemisphereClosedCapBoundaryCollar := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let _ := roundedHemisphereClosedCapChartedSpace
  exact isLocalDiffeomorph_collaredCutSideHalfCollarMap
    coordinateUnlinkExteriorModel ∞ coordinateClosedCapZero
    coordinateEquator
    isOpen_roundedHemisphereClosedCapZero_offBoundary
    roundedHemisphereClosedCapCollarAmbient
    range_roundedHemisphereClosedCapCollarAmbient_subset
    isOpenEmbedding_roundedHemisphereClosedCapBoundaryCollar
    roundedHemisphereClosedCapZero_cover
    (roundedHemisphereClosedCapAtlas_compatible hlocal)

theorem isLocalDiffeomorph_roundedHemisphereClosedCapHomeomorph
    (eEuclidean :
      letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
      EuclideanSpace ℝ (Fin 4) ≃ₘ^∞⟮𝓡 4,
        coordinateUnlinkExteriorModel⟯ EuclideanSpace ℝ (Fin 4))
    (heEuclidean : ∀ x, eEuclidean x = x)
    (eSphere : Sphere 4 ≃ₘ^∞⟮𝓡 4,
      coordinateUnlinkExteriorModel⟯ Sphere 4)
    (heSphere : ∀ x, eSphere x = x) :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
    letI := roundedHemisphereClosedCapChartedSpace
    IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      roundedHemisphereClosedCapHomeomorph := by
  let _ := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
  let hlocal :=
    isLocalDiffeomorphOn_roundedHemisphereClosedCapCollarAmbient_common
      eSphere heSphere
  let _ := roundedHemisphereClosedCapChartedSpace
  let U := collaredCutSideOffBoundaryOpens euclideanFourBallAmbientCarrier
    euclideanFourBallAmbientBoundary
    isOpen_euclideanFourBallAmbientOffBoundary
  let V := collaredCutSideOffBoundaryOpens coordinateClosedCapZero
    coordinateEquator
    isOpen_roundedHemisphereClosedCapZero_offBoundary
  let cOne : U → EuclideanFourBall :=
    collaredCutSideOffBoundaryOpensMap euclideanFourBallAmbientCarrier
      euclideanFourBallAmbientBoundary
      isOpen_euclideanFourBallAmbientOffBoundary
  let cTwo : EuclideanFourBallCollarDomain → EuclideanFourBall :=
    coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar
  let dOne : V → CollaredCutSide coordinateClosedCapZero :=
    collaredCutSideOffBoundaryOpensMap coordinateClosedCapZero
      coordinateEquator
      isOpen_roundedHemisphereClosedCapZero_offBoundary
  have heEuclideanSymm (x : EuclideanSpace ℝ (Fin 4)) :
      eEuclidean.symm x = x := by
    calc
      eEuclidean.symm x = eEuclidean.symm (eEuclidean x) :=
        congrArg eEuclidean.symm (heEuclidean x).symm
      _ = x := eEuclidean.symm_apply_apply x
  have hSourceMem (x : U) : eEuclidean.symm x.1 ∈
      roundedHemisphereOpenUnitBallOpens := by
    have hx : x.1 ∈ ball (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
      have hx' := x.2
      change x.1 ∈ collaredCutSideOffBoundary
        euclideanFourBallAmbientCarrier euclideanFourBallAmbientBoundary at hx'
      rwa [collaredCutSideOffBoundary, closedBall_sdiff_sphere] at hx'
    change eEuclidean.symm x.1 ∈
      ball (0 : EuclideanSpace ℝ (Fin 4)) 1
    rwa [heEuclideanSymm]
  let qSource : U → roundedHemisphereOpenUnitBallOpens :=
    restrictToOpens eEuclidean.symm
      (collaredCutSideOffBoundaryOpens euclideanFourBallAmbientCarrier
        euclideanFourBallAmbientBoundary
        isOpen_euclideanFourBallAmbientOffBoundary)
      roundedHemisphereOpenUnitBallOpens hSourceMem
  have hqSource : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      (𝓡 4) ∞ qSource :=
    isLocalDiffeomorph_restrictToOpens coordinateUnlinkExteriorModel
      (𝓡 4) eEuclidean.symm
      (collaredCutSideOffBoundaryOpens euclideanFourBallAmbientCarrier
        euclideanFourBallAmbientBoundary
        isOpen_euclideanFourBallAmbientOffBoundary)
      roundedHemisphereOpenUnitBallOpens hSourceMem
      eEuclidean.symm.isLocalDiffeomorph
  have hTargetMem (y : roundedHemisphereOpenCapZeroOpens) :
      eSphere y.1 ∈ V := by
    change eSphere y.1 ∈
      collaredCutSideOffBoundary coordinateClosedCapZero
        coordinateEquator
    rw [roundedHemisphereClosedCapZero_offBoundary,
      heSphere]
    exact y.2
  let qTarget : roundedHemisphereOpenCapZeroOpens → V :=
    restrictToOpens eSphere roundedHemisphereOpenCapZeroOpens
      (collaredCutSideOffBoundaryOpens coordinateClosedCapZero
        coordinateEquator
        isOpen_roundedHemisphereClosedCapZero_offBoundary)
      hTargetMem
  have hqTarget : IsLocalDiffeomorph (𝓡 4)
      coordinateUnlinkExteriorModel ∞ qTarget :=
    isLocalDiffeomorph_restrictToOpens (𝓡 4)
      coordinateUnlinkExteriorModel eSphere
      roundedHemisphereOpenCapZeroOpens
      (collaredCutSideOffBoundaryOpens coordinateClosedCapZero
        coordinateEquator
        isOpen_roundedHemisphereClosedCapZero_offBoundary)
      hTargetMem eSphere.isLocalDiffeomorph
  let q : U → V :=
    qTarget ∘ roundedHemisphereInteriorDiffeomorph ∘ qSource
  have hq : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ q := by
    intro x
    exact hqSource x |>.comp (𝓡 4)
      roundedHemisphereOpenCapZeroOpens
      (roundedHemisphereInteriorDiffeomorph.isLocalDiffeomorph (qSource x)) |>.comp
      coordinateUnlinkExteriorModel V
      (hqTarget (roundedHemisphereInteriorDiffeomorph (qSource x)))
  have hdOne : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ dOne :=
    isLocalDiffeomorph_roundedHemisphereClosedCapOffMap hlocal
  have hFcOne : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (roundedHemisphereClosedCapHomeomorph ∘ cOne) := by
    intro x
    have hcomp := hq x |>.comp coordinateUnlinkExteriorModel
      (CollaredCutSide coordinateClosedCapZero) (hdOne (q x))
    apply rounded_isLocalDiffeomorphAt_congr_of_eventuallyEq
      coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel hcomp
    filter_upwards [] with z
    apply Subtype.ext
    simp only [Function.comp_apply]
    rw [roundedHemisphereClosedCapHomeomorph_apply_coe]
    change roundedHemisphereSphereMap (cOne z) =
      eSphere (roundedHemisphereInteriorMap (qSource z))
    rw [heSphere]
    apply congrArg roundedHemisphereSphereMap
    apply Subtype.ext
    exact (heEuclideanSymm z.1).symm
  have hcOne : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ cOne :=
    isLocalDiffeomorph_roundedHemisphereCommonFourBallOffMap
  have hcTwo : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞ cTwo :=
    isLocalDiffeomorph_coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar
  have hdTwo : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      roundedHemisphereClosedCapBoundaryCollar :=
    isLocalDiffeomorph_roundedHemisphereClosedCapBoundaryCollar hlocal
  have hFcTwo : IsLocalDiffeomorph coordinateUnlinkExteriorModel
      coordinateUnlinkExteriorModel ∞
      (roundedHemisphereClosedCapHomeomorph ∘ cTwo) := by
    intro p
    apply rounded_isLocalDiffeomorphAt_congr_of_eventuallyEq
      coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel (hdTwo p)
    filter_upwards [] with q
    apply Subtype.ext
    exact (roundedHemisphereClosedCapCollarAmbient_eq_sphereMap q).symm
  apply isLocalDiffeomorph_of_three_localDiffeomorph_parametrizations
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    roundedHemisphereClosedCapHomeomorph cOne cTwo cTwo
    hcOne hcTwo hcTwo hFcOne hFcTwo hFcTwo
  intro z
  rcases euclideanFourBallAmbient_cover z with hz | hz
  · exact Or.inl ⟨⟨z.1, hz⟩, Subtype.ext rfl⟩
  · rcases hz with ⟨p, hp⟩
    exact Or.inr (Or.inl ⟨p, Subtype.ext hp⟩)

noncomputable def roundedHemisphereClosedCapDiffeomorph
    (eEuclidean :
      letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
      EuclideanSpace ℝ (Fin 4) ≃ₘ^∞⟮𝓡 4,
        coordinateUnlinkExteriorModel⟯ EuclideanSpace ℝ (Fin 4))
    (heEuclidean : ∀ x, eEuclidean x = x)
    (eSphere : Sphere 4 ≃ₘ^∞⟮𝓡 4,
      coordinateUnlinkExteriorModel⟯ Sphere 4)
    (heSphere : ∀ x, eSphere x = x) :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
    letI := roundedHemisphereClosedCapChartedSpace
    EuclideanFourBall ≃ₘ^∞⟮coordinateUnlinkExteriorModel,
      coordinateUnlinkExteriorModel⟯
      CollaredCutSide coordinateClosedCapZero := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
  let _ := roundedHemisphereClosedCapChartedSpace
  exact diffeomorphOfHomeomorphIsLocalDiffeomorph
    coordinateUnlinkExteriorModel coordinateUnlinkExteriorModel
    roundedHemisphereClosedCapHomeomorph
    (isLocalDiffeomorph_roundedHemisphereClosedCapHomeomorph
      eEuclidean heEuclidean eSphere heSphere)

@[simp] theorem roundedHemisphereClosedCapDiffeomorph_apply_coe
    (eEuclidean :
      letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
      EuclideanSpace ℝ (Fin 4) ≃ₘ^∞⟮𝓡 4,
        coordinateUnlinkExteriorModel⟯ EuclideanSpace ℝ (Fin 4))
    (heEuclidean : ∀ x, eEuclidean x = x)
    (eSphere : Sphere 4 ≃ₘ^∞⟮𝓡 4,
      coordinateUnlinkExteriorModel⟯ Sphere 4)
    (heSphere : ∀ x, eSphere x = x)
    (u : EuclideanFourBall) :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
    letI := roundedHemisphereClosedCapChartedSpace
    ((roundedHemisphereClosedCapDiffeomorph eEuclidean heEuclidean
      eSphere heSphere u : CollaredCutSide coordinateClosedCapZero) :
      Sphere 4) = roundedHemisphereSphereMap u := by
  rfl

theorem roundedHemisphereClosedCapDiffeomorph_boundaryCollar
    (eEuclidean :
      letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
      EuclideanSpace ℝ (Fin 4) ≃ₘ^∞⟮𝓡 4,
        coordinateUnlinkExteriorModel⟯ EuclideanSpace ℝ (Fin 4))
    (heEuclidean : ∀ x, eEuclidean x = x)
    (eSphere : Sphere 4 ≃ₘ^∞⟮𝓡 4,
      coordinateUnlinkExteriorModel⟯ Sphere 4)
    (heSphere : ∀ x, eSphere x = x)
    (p : EuclideanFourBallCollarDomain) :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
    letI := roundedHemisphereClosedCapChartedSpace
    roundedHemisphereClosedCapDiffeomorph eEuclidean heEuclidean
        eSphere heSphere
        (coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar p) =
      roundedHemisphereClosedCapBoundaryCollar p := by
  apply Subtype.ext
  exact (roundedHemisphereClosedCapCollarAmbient_eq_sphereMap p).symm

theorem roundedHemisphereClosedCapDiffeomorph_boundaryZero_coe
    (eEuclidean :
      letI := coordinateUnlinkExteriorEuclideanAmbientChartedSpace
      EuclideanSpace ℝ (Fin 4) ≃ₘ^∞⟮𝓡 4,
        coordinateUnlinkExteriorModel⟯ EuclideanSpace ℝ (Fin 4))
    (heEuclidean : ∀ x, eEuclidean x = x)
    (eSphere : Sphere 4 ≃ₘ^∞⟮𝓡 4,
      coordinateUnlinkExteriorModel⟯ Sphere 4)
    (heSphere : ∀ x, eSphere x = x)
    (s : Sphere 3) :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
    letI := roundedHemisphereClosedCapChartedSpace
    ((roundedHemisphereClosedCapDiffeomorph eEuclidean heEuclidean
        eSphere heSphere
        (coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar
          (s, euclideanFourBallCollarZero)) :
      CollaredCutSide coordinateClosedCapZero) : Sphere 4) =
      equatorSphereMap s := by
  rw [roundedHemisphereClosedCapDiffeomorph_apply_coe,
    coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar_apply,
    roundedHemisphereSphereMap_euclideanFourBallSmoothCollar,
    show roundedHemisphereEquatorTime euclideanFourBallCollarZero =
        ⟨0, show (0 : ℝ) ∈
          Ioo (-(1 / 2 : ℝ)) (1 / 2) by norm_num⟩ by
      apply Subtype.ext
      simp]
  exact equatorCollarSphereMap_zero s

theorem roundedHemisphereClosedCap_boundary
    (eSphere : Sphere 4 ≃ₘ^∞⟮𝓡 4,
      coordinateUnlinkExteriorModel⟯ Sphere 4)
    (heSphere : ∀ x, eSphere x = x)
    (hSphereBoundary : coordinateUnlinkExteriorModel.boundary
      (Sphere 4) = ∅) :
    letI := roundedHemisphereClosedCapChartedSpace
    coordinateUnlinkExteriorModel.boundary
        (CollaredCutSide coordinateClosedCapZero) =
      (Subtype.val : CollaredCutSide coordinateClosedCapZero → Sphere 4) ⁻¹'
        coordinateEquator := by
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      EuclideanFourBallCollarDomain :=
    isManifold_coordinateUnlinkExteriorRechartedFourBallCollarDomain
  let hlocal :=
    isLocalDiffeomorphOn_roundedHemisphereClosedCapCollarAmbient_common
      eSphere heSphere
  let _ := roundedHemisphereClosedCapChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide coordinateClosedCapZero) :=
    isManifold_roundedHemisphereClosedCapChartedSpace hlocal
  have hpreimage : roundedHemisphereClosedCapCollarAmbient ⁻¹'
      (coordinateUnlinkExteriorModel.boundary (Sphere 4) ∪
        coordinateEquator) =
      coordinateUnlinkExteriorModel.boundary
        EuclideanFourBallCollarDomain := by
    rw [hSphereBoundary, empty_union,
      preimage_roundedHemisphereClosedCapCollarAmbient_equator,
      coordinateUnlinkExteriorRechartedFourBallCollar_boundary]
  have h := boundary_collaredCutSideChartedSpace_of_localDiffeomorphOn
    coordinateUnlinkExteriorModel ∞ coordinateClosedCapZero
    coordinateEquator
    isOpen_roundedHemisphereClosedCapZero_offBoundary
    roundedHemisphereClosedCapCollarAmbient
    range_roundedHemisphereClosedCapCollarAmbient_subset
    isOpenEmbedding_roundedHemisphereClosedCapBoundaryCollar
    roundedHemisphereClosedCapZero_cover hlocal (by simp) hpreimage
  rwa [hSphereBoundary, empty_union] at h

end CommonSphereAtlas


/-- The direct common-model atlas on the closed rounded coordinate cap. -/
@[instance_reducible, expose]
public def coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace :
    ChartedSpace CoordinateUnlinkExteriorModelSpace
      (CollaredCutSide coordinateClosedCapZero) := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ := coordinateUnlinkExteriorRechartedFourBallCollarChartedSpace
  exact collaredCutSideChartedSpace coordinateClosedCapZero
    coordinateEquator
    isOpen_roundedHemisphereClosedCapZero_offBoundary
    roundedHemisphereClosedCapCollarAmbient
    range_roundedHemisphereClosedCapCollarAmbient_subset
    isOpenEmbedding_roundedHemisphereClosedCapBoundaryCollar
    roundedHemisphereClosedCapZero_cover

/-- The direct rounded closed-cap atlas is a smooth four-manifold atlas. -/
public theorem isManifold_coordinateUnlinkExteriorRoundedHemisphereClosedCap :
    letI := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
    IsManifold coordinateUnlinkExteriorModel ∞
      (CollaredCutSide coordinateClosedCapZero) := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  let hlocal :=
    isLocalDiffeomorphOn_roundedHemisphereClosedCapCollarAmbient_common
      standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph
      (fun x ↦
        standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph_apply x)
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  exact isManifold_roundedHemisphereClosedCapChartedSpace hlocal

/-- There is a common-model diffeomorphism from the Euclidean four-ball to the rounded cap which
agrees exactly with the specified boundary collars. -/
public theorem exists_euclideanFourBallRoundedHemisphereDiffeomorph :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
    letI := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
    ∃ e : EuclideanFourBall ≃ₘ^∞⟮coordinateUnlinkExteriorModel,
        coordinateUnlinkExteriorModel⟯ CollaredCutSide coordinateClosedCapZero,
      ∀ p : EuclideanFourBallCollarDomain,
        e (coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar p) =
          roundedHemisphereClosedCapBoundaryCollar p := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  let e := roundedHemisphereClosedCapDiffeomorph
    standardToCoordinateUnlinkExteriorCommonModelEuclideanIdentityDiffeomorph
    (fun x ↦
      standardToCoordinateUnlinkExteriorCommonModelEuclideanIdentityDiffeomorph_apply x)
    standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph
    (fun x ↦
      standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph_apply x)
  refine ⟨e, ?_⟩
  intro p
  exact roundedHemisphereClosedCapDiffeomorph_boundaryCollar
    standardToCoordinateUnlinkExteriorCommonModelEuclideanIdentityDiffeomorph
    (fun x ↦
      standardToCoordinateUnlinkExteriorCommonModelEuclideanIdentityDiffeomorph_apply x)
    standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph
    (fun x ↦
      standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph_apply x) p

/-- The chosen common-model diffeomorphism from the Euclidean four-ball to the rounded cap. -/
public noncomputable def euclideanFourBallRoundedHemisphereDiffeomorph :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
    letI := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
    EuclideanFourBall ≃ₘ^∞⟮coordinateUnlinkExteriorModel,
      coordinateUnlinkExteriorModel⟯ CollaredCutSide coordinateClosedCapZero :=
  Classical.choose exists_euclideanFourBallRoundedHemisphereDiffeomorph

/-- The chosen ball-to-cap diffeomorphism agrees exactly with the two boundary collars. -/
public theorem euclideanFourBallRoundedHemisphereDiffeomorph_boundaryCollar
    (p : EuclideanFourBallCollarDomain) :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
    letI := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
    euclideanFourBallRoundedHemisphereDiffeomorph
        (coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar p) =
      roundedHemisphereClosedCapBoundaryCollar p := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  exact Classical.choose_spec
    exists_euclideanFourBallRoundedHemisphereDiffeomorph p

/-- On the zero slice, the chosen ball-to-cap diffeomorphism is exactly the equator sphere map. -/
public theorem euclideanFourBallRoundedHemisphereDiffeomorph_boundaryZero_coe
    (s : Sphere 3) :
    letI := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
    letI := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
    ((euclideanFourBallRoundedHemisphereDiffeomorph
        (coordinateUnlinkExteriorCommonModelEuclideanFourBallBoundaryCollar
          (s, euclideanFourBallCollarZero)) :
      CollaredCutSide coordinateClosedCapZero) : Sphere 4) =
      equatorSphereMap s := by
  let _ := coordinateUnlinkExteriorCommonModelEuclideanFourBallChartedSpace
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  rw [euclideanFourBallRoundedHemisphereDiffeomorph_boundaryCollar,
    roundedHemisphereClosedCapBoundaryCollar_coe,
    roundedHemisphereClosedCapCollarAmbient]
  rw [show roundedHemisphereEquatorTime euclideanFourBallCollarZero =
      ⟨0, show (0 : ℝ) ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) by norm_num⟩ by
    apply Subtype.ext
    simp]
  exact equatorCollarSphereMap_zero s

/-- The model boundary of the direct rounded cap is exactly its equator. -/
public theorem coordinateUnlinkExteriorRoundedHemisphereClosedCap_boundary :
    letI := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
    coordinateUnlinkExteriorModel.boundary
        (CollaredCutSide coordinateClosedCapZero) =
      (Subtype.val : CollaredCutSide coordinateClosedCapZero → Sphere 4) ⁻¹'
        coordinateEquator := by
  let _ := coordinateUnlinkExteriorCommonModelSphereChartedSpace
  let _ : IsManifold coordinateUnlinkExteriorModel ∞ (Sphere 4) :=
    isManifold_coordinateUnlinkExteriorCommonModelSphere
  let _ := coordinateUnlinkExteriorRoundedHemisphereClosedCapChartedSpace
  exact roundedHemisphereClosedCap_boundary
    standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph
    (fun x ↦
      standardToCoordinateUnlinkExteriorCommonModelSphereIdentityDiffeomorph_apply x)
    coordinateUnlinkExteriorCommonModelSphere_boundary

end SplittingSpheres
