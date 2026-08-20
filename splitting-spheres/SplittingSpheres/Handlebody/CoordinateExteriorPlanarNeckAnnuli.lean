/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.DirectionalRadialAnnulus
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarNeckPushout
public import SplittingSpheres.Handlebody.PartialSphereSpinAnnulus

/-!
# Radial annulus coordinates on the two polynomial neck halves

The left half is first considered downstairs in the polynomial coordinate `w = z ^ m`.  After
translation by `1`, it is radial about the left puncture `-1`.  The actual right half of the
degree-`m` flower is radial about `0`.  In each case the outer radial bound is the minimum of the
round polynomial boundary and the vertical seam `re w = -1 / 2`; the active formula switches at
angular real part `sqrt 3 / 3`.

This file identifies those two literal point-set halves with `Sphere 1 × [0,1]` and records
their endpoint sets.  It does not trivialize the `m` sheets over the left base half, classify a
surface, or make a smoothness assertion.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open scoped unitInterval

namespace SplittingSpheres

/-! ## Scalar switching formulas -/

/-- The angular real part at which the round outer circle meets the vertical seam. -/
def planarNeckAngularThreshold : ℝ :=
  Real.sqrt 3 / 3

theorem planarNeckAngularThreshold_pos :
    0 < planarNeckAngularThreshold := by
  unfold planarNeckAngularThreshold
  positivity

theorem planarNeckAngularThreshold_sq :
    planarNeckAngularThreshold ^ 2 = (1 / 3 : ℝ) := by
  unfold planarNeckAngularThreshold
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem planarNeckAngularThreshold_lt_one :
    planarNeckAngularThreshold < 1 := by
  have hsq := planarNeckAngularThreshold_sq
  have hpos := planarNeckAngularThreshold_pos
  nlinarith

theorem neg_one_lt_neg_planarNeckAngularThreshold :
    (-1 : ℝ) < -planarNeckAngularThreshold := by
  linarith [planarNeckAngularThreshold_lt_one]

/-- The outer radial bound about the left puncture, as a function of angular real part. -/
def coordinateUnlinkExteriorPlanarLeftOuterRadiusScalar (a : ℝ) : ℝ :=
  if a ≤ planarNeckAngularThreshold then
    planarOuterQuadraticRadius (-a)
  else
    1 / (2 * a)

/-- The outer radial bound about zero on the right half, before taking an `m`th root. -/
def coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar (a : ℝ) : ℝ :=
  if a ≤ -planarNeckAngularThreshold then
    -1 / (2 * a)
  else
    planarOuterQuadraticRadius a

theorem planarOuterQuadraticRadius_neg_threshold :
    planarOuterQuadraticRadius (-planarNeckAngularThreshold) =
      1 / (2 * planarNeckAngularThreshold) := by
  symm
  apply (sq_add_mul_eq_quarter_iff_eq_planarOuterQuadraticRadius
    (a := -planarNeckAngularThreshold)
    (s := 1 / (2 * planarNeckAngularThreshold))
    (by linarith [planarNeckAngularThreshold_lt_one])
    (by linarith [planarNeckAngularThreshold_pos])
    ((one_div_pos.mpr (mul_pos (by norm_num)
      planarNeckAngularThreshold_pos)).le)).mp
  have hk := planarNeckAngularThreshold_sq
  field_simp [planarNeckAngularThreshold_pos.ne']
  nlinarith

theorem neg_one_div_neg_threshold :
    -1 / (2 * (-planarNeckAngularThreshold)) =
      1 / (2 * planarNeckAngularThreshold) := by
  field_simp [planarNeckAngularThreshold_pos.ne']

theorem continuous_coordinateUnlinkExteriorPlanarLeftOuterRadiusScalar :
    Continuous coordinateUnlinkExteriorPlanarLeftOuterRadiusScalar := by
  unfold coordinateUnlinkExteriorPlanarLeftOuterRadiusScalar
  apply continuous_if_le continuous_id continuous_const
  · exact (continuous_planarOuterQuadraticRadius.comp continuous_neg).continuousOn
  · intro a ha
    have ha0 : 0 < a := planarNeckAngularThreshold_pos.trans_le ha
    apply ContinuousWithinAt.div continuousWithinAt_const
      (continuousWithinAt_const.mul continuousWithinAt_id)
    exact mul_ne_zero (by norm_num) ha0.ne'
  · intro a ha
    change a = planarNeckAngularThreshold at ha
    subst a
    exact planarOuterQuadraticRadius_neg_threshold

theorem continuous_coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar :
    Continuous coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar := by
  unfold coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar
  apply continuous_if_le continuous_id continuous_const
  · intro a ha
    apply ContinuousWithinAt.div continuousWithinAt_const
      (continuousWithinAt_const.mul continuousWithinAt_id)
    intro hzero
    have ha0 : a < 0 := ha.trans_lt (neg_lt_zero.mpr planarNeckAngularThreshold_pos)
    exact (mul_ne_zero (by norm_num) ha0.ne) hzero
  · exact continuous_planarOuterQuadraticRadius.continuousOn
  · intro a ha
    change a = -planarNeckAngularThreshold at ha
    subst a
    rw [neg_one_div_neg_threshold, planarOuterQuadraticRadius_neg_threshold]

/-- A useful strict strengthening of the uniform `1/8` lower bound. -/
theorem oneEighth_lt_planarOuterQuadraticRadius
    {a : ℝ} (ha : a ≤ 1) :
    (1 / 8 : ℝ) < planarOuterQuadraticRadius a := by
  let p := planarOuterQuadraticRadius a
  have hp : 0 < p := planarOuterQuadraticRadius_pos ha
  have heq : p ^ 2 + a * p = 1 / 4 :=
    planarOuterQuadraticRadius_sq_add_mul a
  have hap : a * p ≤ p := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha hp.le
  by_contra h
  have hp8 : p ≤ 1 / 8 := le_of_not_gt h
  nlinarith [sq_nonneg (p - 1 / 8)]

theorem mul_planarOuterQuadraticRadius_neg_le_half
    {a : ℝ} (haLower : -1 ≤ a)
    (ha : a ≤ planarNeckAngularThreshold) :
    a * planarOuterQuadraticRadius (-a) ≤ 1 / 2 := by
  let p := planarOuterQuadraticRadius (-a)
  have hp : 0 < p := planarOuterQuadraticRadius_pos (by linarith)
  have heq : p ^ 2 - a * p = 1 / 4 := by
    simpa [p, sub_eq_add_neg] using
      planarOuterQuadraticRadius_sq_add_mul (-a)
  by_contra h
  have hy : 1 / 2 < a * p := lt_of_not_ge h
  have ha0 : 0 < a := by
    by_contra ha'
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt ha') hp.le
    linarith
  have ha2 : a ^ 2 ≤ 1 / 3 := by
    rw [← planarNeckAngularThreshold_sq]
    exact (sq_le_sq₀ ha0.le planarNeckAngularThreshold_pos.le).2 ha
  have hbase : 0 ≤ 1 / 4 + a * p := by positivity
  have hmul := mul_le_mul_of_nonneg_right ha2 hbase
  have hid : (a * p) ^ 2 = a ^ 2 * (1 / 4 + a * p) := by
    calc
      (a * p) ^ 2 = a ^ 2 * p ^ 2 := by ring
      _ = a ^ 2 * (1 / 4 + a * p) := by
        rw [show p ^ 2 = 1 / 4 + a * p by linarith]
  nlinarith [sq_nonneg (a * p - 1 / 2)]

theorem one_div_two_mul_le_planarOuterQuadraticRadius_neg
    {a : ℝ} (ha : planarNeckAngularThreshold < a) (haUpper : a ≤ 1) :
    1 / (2 * a) ≤ planarOuterQuadraticRadius (-a) := by
  have ha0 : 0 < a := planarNeckAngularThreshold_pos.trans ha
  apply (sq_add_mul_le_quarter_iff_le_planarOuterQuadraticRadius
    (a := -a) (s := 1 / (2 * a))
    (by linarith) (by linarith) (by positivity)).mp
  have ha2 : (1 / 3 : ℝ) < a ^ 2 := by
    rw [← planarNeckAngularThreshold_sq]
    exact (sq_lt_sq₀ planarNeckAngularThreshold_pos.le ha0.le).2 ha
  have hid : (1 / (2 * a)) ^ 2 + -a * (1 / (2 * a)) =
      1 / (4 * a ^ 2) - 1 / 2 := by
    field_simp [ha0.ne']
    ring
  rw [hid]
  have hden : 0 < 4 * a ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos ha0)
  have hdiv : 1 / (4 * a ^ 2) < 3 / 4 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  linarith

theorem neg_one_div_two_mul_le_planarOuterQuadraticRadius
    {a : ℝ} (haLower : -1 ≤ a)
    (ha : a ≤ -planarNeckAngularThreshold) :
    -1 / (2 * a) ≤ planarOuterQuadraticRadius a := by
  rcases ha.eq_or_lt with haEq | haLt
  · subst a
    rw [neg_one_div_neg_threshold, planarOuterQuadraticRadius_neg_threshold]
  · have ha0 : a < 0 := ha.trans_lt
      (neg_lt_zero.mpr planarNeckAngularThreshold_pos)
    apply (sq_add_mul_le_quarter_iff_le_planarOuterQuadraticRadius
      (a := a) (s := -1 / (2 * a))
      haLower (by linarith)
      ((div_pos_of_neg_of_neg (by norm_num)
        (mul_neg_of_pos_of_neg (by norm_num) ha0)).le)).mp
    have hneg : planarNeckAngularThreshold < -a := by linarith [haLt]
    have ha2 : (1 / 3 : ℝ) < a ^ 2 := by
      rw [← planarNeckAngularThreshold_sq]
      have hs := (sq_lt_sq₀ planarNeckAngularThreshold_pos.le
        (neg_nonneg.mpr ha0.le)).2 hneg
      nlinarith
    have hid : (-1 / (2 * a)) ^ 2 + a * (-1 / (2 * a)) =
        1 / (4 * a ^ 2) - 1 / 2 := by
      field_simp [ha0.ne]
      ring
    rw [hid]
    have hden : 0 < 4 * a ^ 2 := mul_pos (by norm_num) (sq_pos_of_neg ha0)
    have hdiv : 1 / (4 * a ^ 2) < 3 / 4 := by
      rw [div_lt_iff₀ hden]
      nlinarith
    linarith

theorem planarLeftHalf_constraints_iff_le_outerRadius
    {a s : ℝ} (haLower : -1 ≤ a) (haUpper : a ≤ 1) (hs : 0 ≤ s) :
    (s ^ 2 - a * s ≤ 1 / 4 ∧ s * a ≤ 1 / 2) ↔
      s ≤ coordinateUnlinkExteriorPlanarLeftOuterRadiusScalar a := by
  rw [coordinateUnlinkExteriorPlanarLeftOuterRadiusScalar]
  split_ifs with ha
  · have houter : s ^ 2 - a * s ≤ 1 / 4 ↔
        s ≤ planarOuterQuadraticRadius (-a) := by
      simpa [sub_eq_add_neg] using
        (sq_add_mul_le_quarter_iff_le_planarOuterQuadraticRadius
          (a := -a) (s := s) (by linarith) (by linarith) hs)
    constructor
    · exact fun h ↦ houter.mp h.1
    · intro h
      have hsOuter := houter.mpr h
      refine ⟨hsOuter, ?_⟩
      by_cases ha0 : a ≤ 0
      · exact (mul_nonpos_of_nonneg_of_nonpos hs ha0).trans (by norm_num)
      · have hamul := mul_le_mul_of_nonneg_right h (lt_of_not_ge ha0).le
        nlinarith [mul_planarOuterQuadraticRadius_neg_le_half haLower ha]
  · have ha0 : 0 < a := planarNeckAngularThreshold_pos.trans (lt_of_not_ge ha)
    have hhalf : s * a ≤ 1 / 2 ↔ s ≤ 1 / (2 * a) := by
      rw [le_div_iff₀ (mul_pos (by norm_num) ha0)]
      constructor <;> intro h <;> nlinarith
    constructor
    · exact fun h ↦ hhalf.mp h.2
    · intro h
      refine ⟨?_, hhalf.mpr h⟩
      have hsOuter : s ≤ planarOuterQuadraticRadius (-a) :=
        h.trans (one_div_two_mul_le_planarOuterQuadraticRadius_neg
          (lt_of_not_ge ha) haUpper)
      exact (by
        simpa [sub_eq_add_neg] using
          (sq_add_mul_le_quarter_iff_le_planarOuterQuadraticRadius
            (a := -a) (s := s) (by linarith) (by linarith) hs).mpr hsOuter)

theorem planarRightHalf_constraints_iff_le_outerRadiusBase
    {a s : ℝ} (haLower : -1 ≤ a) (haUpper : a ≤ 1) (hs : 0 ≤ s) :
    (s ^ 2 + a * s ≤ 1 / 4 ∧ -1 / 2 ≤ a * s) ↔
      s ≤ coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar a := by
  rw [coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar]
  split_ifs with ha
  · have ha0 : a < 0 := ha.trans_lt (neg_lt_zero.mpr planarNeckAngularThreshold_pos)
    have hhalf : -1 / 2 ≤ a * s ↔ s ≤ -1 / (2 * a) := by
      have hden : 0 < -2 * a := mul_pos_of_neg_of_neg (by norm_num) ha0
      have hrewrite : -1 / (2 * a) = 1 / (-2 * a) := by
        field_simp [ha0.ne]
      rw [hrewrite]
      constructor
      · intro h
        apply (le_div_iff₀ hden).2
        nlinarith
      · intro h
        have h' := (le_div_iff₀ hden).1 h
        nlinarith
    constructor
    · exact fun h ↦ hhalf.mp h.2
    · intro h
      refine ⟨?_, hhalf.mpr h⟩
      have hsOuter : s ≤ planarOuterQuadraticRadius a :=
        h.trans (neg_one_div_two_mul_le_planarOuterQuadraticRadius
          haLower ha)
      exact (sq_add_mul_le_quarter_iff_le_planarOuterQuadraticRadius
        (a := a) (s := s) haLower haUpper hs).mpr hsOuter
  · have houter : s ^ 2 + a * s ≤ 1 / 4 ↔
        s ≤ planarOuterQuadraticRadius a :=
      sq_add_mul_le_quarter_iff_le_planarOuterQuadraticRadius
        haLower haUpper hs
    constructor
    · exact fun h ↦ houter.mp h.1
    · intro h
      have hsOuter := houter.mpr h
      refine ⟨hsOuter, ?_⟩
      have hbound : (-a) * planarOuterQuadraticRadius a ≤ 1 / 2 :=
        by
          simpa only [neg_neg] using
            (mul_planarOuterQuadraticRadius_neg_le_half
              (a := -a) (by linarith) (by linarith [lt_of_not_ge ha]))
      by_cases ha0 : 0 ≤ a
      · nlinarith [mul_nonneg ha0 hs]
      · have hmul := mul_le_mul_of_nonneg_right h (neg_pos.mpr (lt_of_not_ge ha0)).le
        nlinarith

theorem planarLeftHalf_eq_outerRadius_iff
    {a s : ℝ} (haLower : -1 ≤ a) (haUpper : a ≤ 1) (hs : 0 ≤ s)
    (hconstraints : s ^ 2 - a * s ≤ 1 / 4 ∧ s * a ≤ 1 / 2) :
    s = coordinateUnlinkExteriorPlanarLeftOuterRadiusScalar a ↔
      s ^ 2 - a * s = 1 / 4 ∨ s * a = 1 / 2 := by
  rw [coordinateUnlinkExteriorPlanarLeftOuterRadiusScalar]
  split_ifs with ha
  · constructor
    · rintro rfl
      left
      have h := planarOuterQuadraticRadius_sq_add_mul (-a)
      simpa [sub_eq_add_neg] using h
    · rintro (houter | hseam)
      · exact (by
          simpa [sub_eq_add_neg] using
            (sq_add_mul_eq_quarter_iff_eq_planarOuterQuadraticRadius
              (a := -a) (s := s) (by linarith) (by linarith) hs).mp
                (by simpa [sub_eq_add_neg] using houter))
      · by_cases ha0 : a ≤ 0
        · have := mul_nonpos_of_nonneg_of_nonpos hs ha0
          nlinarith
        · have haPos : 0 < a := lt_of_not_ge ha0
          apply le_antisymm
          · simpa [sub_eq_add_neg] using
              (sq_add_mul_le_quarter_iff_le_planarOuterQuadraticRadius
                (a := -a) (s := s) (by linarith) (by linarith) hs).mp
                  (by simpa [sub_eq_add_neg] using hconstraints.1)
          · have hp := mul_planarOuterQuadraticRadius_neg_le_half haLower ha
            apply le_of_mul_le_mul_right _ haPos
            nlinarith
  · have haPos : 0 < a :=
      planarNeckAngularThreshold_pos.trans (lt_of_not_ge ha)
    have hhalfEq : s * a = 1 / 2 ↔ s = 1 / (2 * a) := by
      constructor <;> intro h
      · apply (eq_div_iff (mul_ne_zero (by norm_num) haPos.ne')).2
        nlinarith
      · rw [h]
        field_simp [haPos.ne']
    constructor
    · rintro rfl
      exact Or.inr (hhalfEq.mpr rfl)
    · rintro (houter | hseam)
      · have hsP : s = planarOuterQuadraticRadius (-a) := by
          simpa [sub_eq_add_neg] using
            (sq_add_mul_eq_quarter_iff_eq_planarOuterQuadraticRadius
              (a := -a) (s := s) (by linarith) (by linarith) hs).mp
                (by simpa [sub_eq_add_neg] using houter)
        have hhalfP := one_div_two_mul_le_planarOuterQuadraticRadius_neg
          (lt_of_not_ge ha) haUpper
        have hsHalf : s ≤ 1 / (2 * a) := by
          have := hconstraints.2
          apply (le_div_iff₀ (mul_pos (by norm_num) haPos)).2
          nlinarith
        exact le_antisymm hsHalf (hsP.symm ▸ hhalfP)
      · exact hhalfEq.mp hseam

theorem planarRightHalf_eq_outerRadiusBase_iff
    {a s : ℝ} (haLower : -1 ≤ a) (haUpper : a ≤ 1) (hs : 0 ≤ s)
    (hconstraints : s ^ 2 + a * s ≤ 1 / 4 ∧ -1 / 2 ≤ a * s) :
    s = coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar a ↔
      s ^ 2 + a * s = 1 / 4 ∨ a * s = -1 / 2 := by
  rw [coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar]
  split_ifs with ha
  · have haNeg : a < 0 := ha.trans_lt
      (neg_lt_zero.mpr planarNeckAngularThreshold_pos)
    have hhalfEq : a * s = -1 / 2 ↔ s = -1 / (2 * a) := by
      constructor <;> intro h
      · apply (eq_div_iff (mul_ne_zero (by norm_num) haNeg.ne)).2
        nlinarith
      · rw [h]
        field_simp [haNeg.ne]
    constructor
    · rintro rfl
      exact Or.inr (hhalfEq.mpr rfl)
    · rintro (houter | hseam)
      · have hsP : s = planarOuterQuadraticRadius a :=
          (sq_add_mul_eq_quarter_iff_eq_planarOuterQuadraticRadius
            haLower haUpper hs).mp houter
        have hhalfP := neg_one_div_two_mul_le_planarOuterQuadraticRadius
          haLower ha
        have hsHalf : s ≤ -1 / (2 * a) := by
          have hden : 0 < -2 * a := mul_pos_of_neg_of_neg (by norm_num) haNeg
          have hrewrite : -1 / (2 * a) = 1 / (-2 * a) := by
            field_simp [haNeg.ne]
          rw [hrewrite]
          apply (le_div_iff₀ hden).2
          nlinarith [hconstraints.2]
        exact le_antisymm hsHalf (hsP.symm ▸ hhalfP)
      · exact hhalfEq.mp hseam
  · constructor
    · rintro rfl
      exact Or.inl (planarOuterQuadraticRadius_sq_add_mul a)
    · rintro (houter | hseam)
      · exact (sq_add_mul_eq_quarter_iff_eq_planarOuterQuadraticRadius
          haLower haUpper hs).mp houter
      · by_cases haNonneg : 0 ≤ a
        · have := mul_nonneg haNonneg hs
          nlinarith
        · have haNeg : a < 0 := lt_of_not_ge haNonneg
          let p := planarOuterQuadraticRadius a
          have hsP : s ≤ p :=
            (sq_add_mul_le_quarter_iff_le_planarOuterQuadraticRadius
              haLower haUpper hs).mp hconstraints.1
          have hpBound : (-a) * p ≤ 1 / 2 := by
            simpa only [neg_neg] using
              (mul_planarOuterQuadraticRadius_neg_le_half
                (a := -a) (by linarith) (by linarith [lt_of_not_ge ha]))
          have hmul : a * p ≤ a * s :=
            mul_le_mul_of_nonpos_left hsP haNeg.le
          have hEq : a * p = a * s := by nlinarith
          exact (mul_left_cancel₀ haNeg.ne hEq).symm

/-! ## The left polynomial base half -/

/-- The twice-punctured polynomial base disk. -/
def coordinateUnlinkExteriorPlanarBaseSet : Set ℂ :=
  {w |
    ‖w + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius ∧
      (1 / 8 : ℝ) ≤ ‖w‖ ∧
        (1 / 8 : ℝ) ≤ ‖w + 1‖}

/-- The closed left half of the twice-punctured polynomial base disk. -/
def coordinateUnlinkExteriorPlanarBaseLeftHalfSet : Set ℂ :=
  coordinateUnlinkExteriorPlanarBaseSet ∩ {w | w.re ≤ -1 / 2}

abbrev CoordinateUnlinkExteriorPlanarBaseLeftHalf : Type :=
  ↑coordinateUnlinkExteriorPlanarBaseLeftHalfSet

@[simp]
theorem mem_coordinateUnlinkExteriorPlanarBaseSet_iff (w : ℂ) :
    w ∈ coordinateUnlinkExteriorPlanarBaseSet ↔
      ‖w + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius ∧
        (1 / 8 : ℝ) ≤ ‖w‖ ∧
          (1 / 8 : ℝ) ≤ ‖w + 1‖ :=
  Iff.rfl

@[simp]
theorem mem_coordinateUnlinkExteriorPlanarBaseLeftHalfSet_iff (w : ℂ) :
    w ∈ coordinateUnlinkExteriorPlanarBaseLeftHalfSet ↔
      ‖w + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius ∧
        (1 / 8 : ℝ) ≤ ‖w‖ ∧
          (1 / 8 : ℝ) ≤ ‖w + 1‖ ∧
            w.re ≤ -1 / 2 := by
  change ((‖w + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius ∧
      (1 / 8 : ℝ) ≤ ‖w‖ ∧ (1 / 8 : ℝ) ≤ ‖w + 1‖) ∧
      w.re ≤ -1 / 2) ↔ _
  tauto

theorem complexUnit_re_bounds (u : sphere (0 : ℂ) 1) :
    -1 ≤ u.1.re ∧ u.1.re ≤ 1 := by
  have h := Complex.abs_re_le_norm u.1
  rw [mem_sphere_zero_iff_norm.mp u.2] at h
  exact abs_le.mp h

/-- Direction-dependent outer radius of the left base half, centered at `-1`. -/
def coordinateUnlinkExteriorPlanarLeftOuterRadius
    (u : sphere (0 : ℂ) 1) : ℝ :=
  coordinateUnlinkExteriorPlanarLeftOuterRadiusScalar u.1.re

theorem continuous_coordinateUnlinkExteriorPlanarLeftOuterRadius :
    Continuous coordinateUnlinkExteriorPlanarLeftOuterRadius := by
  exact continuous_coordinateUnlinkExteriorPlanarLeftOuterRadiusScalar.comp
    (Complex.continuous_re.comp continuous_subtype_val)

theorem oneEighth_lt_coordinateUnlinkExteriorPlanarLeftOuterRadius
    (u : sphere (0 : ℂ) 1) :
    (1 / 8 : ℝ) < coordinateUnlinkExteriorPlanarLeftOuterRadius u := by
  have hu := complexUnit_re_bounds u
  unfold coordinateUnlinkExteriorPlanarLeftOuterRadius
  rw [coordinateUnlinkExteriorPlanarLeftOuterRadiusScalar]
  split_ifs with hbranch
  · exact oneEighth_lt_planarOuterQuadraticRadius (by linarith)
  · have ha0 : 0 < u.1.re :=
      planarNeckAngularThreshold_pos.trans (lt_of_not_ge hbranch)
    have hden : 0 < 2 * u.1.re := mul_pos (by norm_num) ha0
    have hhalf : (1 / 2 : ℝ) ≤ 1 / (2 * u.1.re) := by
      apply (le_div_iff₀ hden).2
      nlinarith [hu.2]
    linarith

theorem complex_re_eq_norm_mul_direction
    {z : ℂ} (hz : z ≠ 0) :
    z.re = ‖z‖ * (nonzeroUnitDirection ⟨z, hz⟩).1.re := by
  have h := congrArg Complex.re (NormedSpace.norm_smul_normalize z)
  rw [Complex.real_smul] at h
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  simpa only [nonzeroUnitDirection_coe] using h.symm

theorem norm_sub_half_sq (z : ℂ) :
    ‖z - (1 / 2 : ℂ)‖ ^ 2 = ‖z‖ ^ 2 - z.re + 1 / 4 := by
  rw [Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq]
  ring

theorem coordinateUnlinkExteriorPlanarLeft_center_outer_iff
    {z : ℂ} (hz : z ≠ 0) :
    ‖(-1 : ℂ) + z + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius ↔
      ‖z‖ ^ 2 -
          (nonzeroUnitDirection ⟨z, hz⟩).1.re * ‖z‖ ≤ 1 / 4 := by
  have hvec : (-1 : ℂ) + z + (1 / 2 : ℂ) = z - (1 / 2 : ℂ) := by ring
  rw [hvec, ← sq_le_sq₀ (norm_nonneg _) sphereHandleRadius_pos.le,
    sphereHandleRadius_sq, norm_sub_half_sq,
    complex_re_eq_norm_mul_direction hz]
  constructor <;> intro h <;> nlinarith

theorem coordinateUnlinkExteriorPlanarLeft_center_seam_iff
    {z : ℂ} (hz : z ≠ 0) :
    ((-1 : ℂ) + z).re ≤ -1 / 2 ↔
      ‖z‖ * (nonzeroUnitDirection ⟨z, hz⟩).1.re ≤ 1 / 2 := by
  rw [Complex.add_re, Complex.neg_re, Complex.one_re,
    complex_re_eq_norm_mul_direction hz]
  norm_num

theorem oneEighth_le_norm_of_re_le_neg_half
    {w : ℂ} (hw : w.re ≤ -1 / 2) :
    (1 / 8 : ℝ) ≤ ‖w‖ := by
  calc
    (1 / 8 : ℝ) ≤ 1 / 2 := by norm_num
    _ ≤ |w.re| := by rw [abs_of_nonpos (by linarith)]; linarith
    _ ≤ ‖w‖ := Complex.abs_re_le_norm w

theorem add_neg_one_mem_baseLeftHalf_iff_mem_directionalRadialAnnulus
    (z : ℂ) :
    (-1 : ℂ) + z ∈ coordinateUnlinkExteriorPlanarBaseLeftHalfSet ↔
      z ∈ directionalRadialAnnulus (1 / 8 : ℝ)
        coordinateUnlinkExteriorPlanarLeftOuterRadius := by
  constructor
  · intro hzLeft
    rw [mem_coordinateUnlinkExteriorPlanarBaseLeftHalfSet_iff] at hzLeft
    have hzLower : (1 / 8 : ℝ) ≤ ‖z‖ := by
      have h := hzLeft.2.2.1
      rw [show (-1 : ℂ) + z + 1 = z by ring] at h
      exact h
    have hz : z ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hzLower
      norm_num at hzLower
    refine ⟨hz, hzLower, ?_⟩
    let u := nonzeroUnitDirection ⟨z, hz⟩
    have hu := complexUnit_re_bounds u
    apply (planarLeftHalf_constraints_iff_le_outerRadius
      hu.1 hu.2 (norm_nonneg z)).mp
    constructor
    · exact (coordinateUnlinkExteriorPlanarLeft_center_outer_iff hz).mp hzLeft.1
    · exact (coordinateUnlinkExteriorPlanarLeft_center_seam_iff hz).mp hzLeft.2.2.2
  · rintro ⟨hz, hzLower, hzUpper⟩
    let u := nonzeroUnitDirection ⟨z, hz⟩
    have hu := complexUnit_re_bounds u
    have hconstraints := (planarLeftHalf_constraints_iff_le_outerRadius
      hu.1 hu.2 (norm_nonneg z)).mpr hzUpper
    have houter := (coordinateUnlinkExteriorPlanarLeft_center_outer_iff hz).mpr
      hconstraints.1
    have hseam := (coordinateUnlinkExteriorPlanarLeft_center_seam_iff hz).mpr
      hconstraints.2
    rw [mem_coordinateUnlinkExteriorPlanarBaseLeftHalfSet_iff]
    refine ⟨houter, oneEighth_le_norm_of_re_le_neg_half hseam, ?_, hseam⟩
    rw [show (-1 : ℂ) + z + 1 = z by ring]
    exact hzLower

/-- Translation by `-1` identifies the centered literal annulus with the actual left base half. -/
def coordinateUnlinkExteriorPlanarLeftCenteredAnnulusHomeomorph :
    ↑(directionalRadialAnnulus (1 / 8 : ℝ)
      coordinateUnlinkExteriorPlanarLeftOuterRadius) ≃ₜ
      CoordinateUnlinkExteriorPlanarBaseLeftHalf :=
  (Homeomorph.addLeft (-1 : ℂ)).subtype fun z ↦
    (add_neg_one_mem_baseLeftHalf_iff_mem_directionalRadialAnnulus z).symm

/-- The closed left polynomial base half is a literal annulus. -/
def coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph :
    PartialSphereSpinAnnulus ≃ₜ CoordinateUnlinkExteriorPlanarBaseLeftHalf :=
  (unlinkUnitCircleHomeomorph.prodCongr
      (Homeomorph.refl (Set.Icc (0 : ℝ) 1))).trans <|
    (directionalRadialAnnulusHomeomorph
      (1 / 8 : ℝ) coordinateUnlinkExteriorPlanarLeftOuterRadius
      (by norm_num) oneEighth_lt_coordinateUnlinkExteriorPlanarLeftOuterRadius
      continuous_coordinateUnlinkExteriorPlanarLeftOuterRadius).trans
        coordinateUnlinkExteriorPlanarLeftCenteredAnnulusHomeomorph

@[simp]
theorem coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_apply_coe
    (x : PartialSphereSpinAnnulus) :
    (coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x : ℂ) =
      (-1 : ℂ) +
        directionalRadialAnnulusRadius (1 / 8 : ℝ)
          coordinateUnlinkExteriorPlanarLeftOuterRadius
          (unlinkUnitCircleHomeomorph x.1) x.2 •
            unlinkUnitCircleComplex x.1 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_zero_coe
    (u : Sphere 1) :
    (coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph (u, 0) : ℂ) =
      (-1 : ℂ) + (1 / 8 : ℝ) • unlinkUnitCircleComplex u := by
  rw [coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_apply_coe,
    directionalRadialAnnulusRadius_zero]

@[simp]
theorem coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_one_coe
    (u : Sphere 1) :
    (coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph (u, 1) : ℂ) =
      (-1 : ℂ) +
        coordinateUnlinkExteriorPlanarLeftOuterRadius
          (unlinkUnitCircleHomeomorph u) • unlinkUnitCircleComplex u := by
  rw [coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_apply_coe,
    directionalRadialAnnulusRadius_one]

/-! ## The actual right flower half -/

/-- Angular real part of the `m`th power of a complex unit direction. -/
def coordinateUnlinkExteriorPlanarRightAngularReal
    (m : ℕ) (u : sphere (0 : ℂ) 1) : ℝ :=
  (u.1 ^ m).re

theorem continuous_coordinateUnlinkExteriorPlanarRightAngularReal (m : ℕ) :
    Continuous (coordinateUnlinkExteriorPlanarRightAngularReal m) := by
  exact Complex.continuous_re.comp
    ((continuous_subtype_val.pow m))

theorem coordinateUnlinkExteriorPlanarRightAngularReal_bounds
    (m : ℕ) (u : sphere (0 : ℂ) 1) :
    -1 ≤ coordinateUnlinkExteriorPlanarRightAngularReal m u ∧
      coordinateUnlinkExteriorPlanarRightAngularReal m u ≤ 1 := by
  have h := Complex.abs_re_le_norm (u.1 ^ m)
  rw [norm_pow, mem_sphere_zero_iff_norm.mp u.2, one_pow] at h
  exact abs_le.mp h

/-- The constant inner radius in the power coordinate. -/
def coordinateUnlinkExteriorPlanarRightInnerRadius (m : ℕ) : ℝ :=
  (1 / 8 : ℝ) ^ ((m : ℝ)⁻¹ : ℝ)

/-- The direction-dependent outer radius of the actual right flower half. -/
def coordinateUnlinkExteriorPlanarRightOuterRadius
    (m : ℕ) (u : sphere (0 : ℂ) 1) : ℝ :=
  coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar
      (coordinateUnlinkExteriorPlanarRightAngularReal m u) ^
    ((m : ℝ)⁻¹ : ℝ)

theorem oneEighth_lt_coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar
    {a : ℝ} (haLower : -1 ≤ a) (haUpper : a ≤ 1) :
    (1 / 8 : ℝ) <
      coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar a := by
  rw [coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar]
  split_ifs with hbranch
  · have ha0 : a < 0 := hbranch.trans_lt
      (neg_lt_zero.mpr planarNeckAngularThreshold_pos)
    have hden : 0 < -2 * a := mul_pos_of_neg_of_neg (by norm_num) ha0
    have hrewrite : -1 / (2 * a) = 1 / (-2 * a) := by
      field_simp [ha0.ne]
    rw [hrewrite]
    have hhalf : (1 / 2 : ℝ) ≤ 1 / (-2 * a) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    linarith
  · exact oneEighth_lt_planarOuterQuadraticRadius haUpper

theorem coordinateUnlinkExteriorPlanarRightInnerRadius_pos
    (m : ℕ) :
    0 < coordinateUnlinkExteriorPlanarRightInnerRadius m := by
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem coordinateUnlinkExteriorPlanarRightInnerRadius_pow
    (m : ℕ) [NeZero m] :
    coordinateUnlinkExteriorPlanarRightInnerRadius m ^ m = (1 / 8 : ℝ) := by
  apply Real.rpow_inv_natCast_pow (by norm_num)
  exact NeZero.ne m

theorem coordinateUnlinkExteriorPlanarRightOuterRadiusBase_pos
    (m : ℕ) (u : sphere (0 : ℂ) 1) :
    0 < coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar
      (coordinateUnlinkExteriorPlanarRightAngularReal m u) :=
  (by
    have hu := coordinateUnlinkExteriorPlanarRightAngularReal_bounds m u
    exact (by norm_num : (0 : ℝ) < 1 / 8).trans <|
      oneEighth_lt_coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar hu.1 hu.2)

theorem coordinateUnlinkExteriorPlanarRightOuterRadius_pos
    (m : ℕ) (u : sphere (0 : ℂ) 1) :
    0 < coordinateUnlinkExteriorPlanarRightOuterRadius m u := by
  exact Real.rpow_pos_of_pos
    (coordinateUnlinkExteriorPlanarRightOuterRadiusBase_pos m u) _

theorem coordinateUnlinkExteriorPlanarRightOuterRadius_pow
    (m : ℕ) [NeZero m] (u : sphere (0 : ℂ) 1) :
    coordinateUnlinkExteriorPlanarRightOuterRadius m u ^ m =
      coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar
        (coordinateUnlinkExteriorPlanarRightAngularReal m u) := by
  apply Real.rpow_inv_natCast_pow
    (coordinateUnlinkExteriorPlanarRightOuterRadiusBase_pos m u).le
  exact NeZero.ne m

theorem continuous_coordinateUnlinkExteriorPlanarRightOuterRadius
    (m : ℕ) :
    Continuous (coordinateUnlinkExteriorPlanarRightOuterRadius m) := by
  unfold coordinateUnlinkExteriorPlanarRightOuterRadius
  apply Continuous.rpow_const
  · exact continuous_coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar.comp
      (continuous_coordinateUnlinkExteriorPlanarRightAngularReal m)
  · exact fun _ ↦ Or.inr (inv_nonneg.mpr (Nat.cast_nonneg m))

theorem coordinateUnlinkExteriorPlanarRightInner_lt_outer
    (m : ℕ) [NeZero m] (u : sphere (0 : ℂ) 1) :
    coordinateUnlinkExteriorPlanarRightInnerRadius m <
      coordinateUnlinkExteriorPlanarRightOuterRadius m u := by
  apply (pow_lt_pow_iff_left₀
    (coordinateUnlinkExteriorPlanarRightInnerRadius_pos m).le
    (coordinateUnlinkExteriorPlanarRightOuterRadius_pos m u).le
    (NeZero.ne m)).mp
  rw [coordinateUnlinkExteriorPlanarRightInnerRadius_pow,
    coordinateUnlinkExteriorPlanarRightOuterRadius_pow]
  have hu := coordinateUnlinkExteriorPlanarRightAngularReal_bounds m u
  exact oneEighth_lt_coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar hu.1 hu.2

theorem coordinateUnlinkExteriorPlanarRightInnerRadius_le_norm_iff
    (m : ℕ) [NeZero m] (z : ℂ) :
    coordinateUnlinkExteriorPlanarRightInnerRadius m ≤ ‖z‖ ↔
      (1 / 8 : ℝ) ≤ ‖z ^ m‖ := by
  rw [norm_pow, ← coordinateUnlinkExteriorPlanarRightInnerRadius_pow m]
  exact (pow_le_pow_iff_left₀
    (coordinateUnlinkExteriorPlanarRightInnerRadius_pos m).le
    (norm_nonneg z) (NeZero.ne m)).symm

theorem norm_le_coordinateUnlinkExteriorPlanarRightOuterRadius_iff
    (m : ℕ) [NeZero m] (z : ℂ) (u : sphere (0 : ℂ) 1) :
    ‖z‖ ≤ coordinateUnlinkExteriorPlanarRightOuterRadius m u ↔
      ‖z‖ ^ m ≤
        coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar
          (coordinateUnlinkExteriorPlanarRightAngularReal m u) := by
  rw [← coordinateUnlinkExteriorPlanarRightOuterRadius_pow m u]
  exact (pow_le_pow_iff_left₀ (norm_nonneg z)
    (coordinateUnlinkExteriorPlanarRightOuterRadius_pos m u).le
    (NeZero.ne m)).symm

/-- The actual right half, flattened from its nested flower subtype to a set in `ℂ`. -/
def coordinateUnlinkExteriorPlanarFlowerRightHalfRawSet (m : ℕ) : Set ℂ :=
  {z | z ≠ 0 ∧
    ‖z ^ m + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius ∧
      (1 / 8 : ℝ) ≤ ‖z ^ m‖ ∧
        (1 / 8 : ℝ) ≤ ‖z ^ m + 1‖ ∧
          -1 / 2 ≤ (z ^ m).re}

@[simp]
theorem mem_coordinateUnlinkExteriorPlanarFlowerRightHalfRawSet_iff
    (m : ℕ) (z : ℂ) :
    z ∈ coordinateUnlinkExteriorPlanarFlowerRightHalfRawSet m ↔
      z ≠ 0 ∧
        ‖z ^ m + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius ∧
          (1 / 8 : ℝ) ≤ ‖z ^ m‖ ∧
            (1 / 8 : ℝ) ≤ ‖z ^ m + 1‖ ∧
              -1 / 2 ≤ (z ^ m).re :=
  Iff.rfl

theorem oneEighth_le_norm_add_one_of_neg_half_le_re
    {w : ℂ} (hw : -1 / 2 ≤ w.re) :
    (1 / 8 : ℝ) ≤ ‖w + 1‖ := by
  calc
    (1 / 8 : ℝ) ≤ 1 / 2 := by norm_num
    _ ≤ |(w + 1).re| := by
      rw [Complex.add_re, Complex.one_re, abs_of_nonneg (by linarith)]
      linarith
    _ ≤ ‖w + 1‖ := Complex.abs_re_le_norm _

theorem directionalRadialAnnulus_rightOuter_eq_rightHalfRawSet
    (m : ℕ) [NeZero m] :
    directionalRadialAnnulus
        (coordinateUnlinkExteriorPlanarRightInnerRadius m)
        (coordinateUnlinkExteriorPlanarRightOuterRadius m) =
      coordinateUnlinkExteriorPlanarFlowerRightHalfRawSet m := by
  ext z
  rw [mem_directionalRadialAnnulus_iff,
    mem_coordinateUnlinkExteriorPlanarFlowerRightHalfRawSet_iff]
  constructor
  · rintro ⟨hz, hzLower, hzUpper⟩
    let u := nonzeroUnitDirection ⟨z, hz⟩
    have hu := coordinateUnlinkExteriorPlanarRightAngularReal_bounds m u
    have hpowUpper : ‖z‖ ^ m ≤
        coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar
          (coordinateUnlinkExteriorPlanarRightAngularReal m u) :=
      (norm_le_coordinateUnlinkExteriorPlanarRightOuterRadius_iff m z u).mp hzUpper
    have hconstraints := (planarRightHalf_constraints_iff_le_outerRadiusBase
      hu.1 hu.2 (pow_nonneg (norm_nonneg z) m)).mpr hpowUpper
    have houter : ‖z ^ m + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius := by
      rw [norm_pow_add_half_le_sphereHandleRadius_iff]
      simpa only [u, coordinateUnlinkExteriorPlanarRightAngularReal,
        nonzeroUnitDirection_coe, planarOuterAngularReal] using hconstraints.1
    have hseam : -1 / 2 ≤ (z ^ m).re := by
      rw [re_pow_eq_norm_pow_mul_planarOuterAngularReal]
      simpa only [u, coordinateUnlinkExteriorPlanarRightAngularReal,
        nonzeroUnitDirection_coe, planarOuterAngularReal, mul_comm] using hconstraints.2
    refine ⟨hz, houter,
      (coordinateUnlinkExteriorPlanarRightInnerRadius_le_norm_iff m z).mp hzLower,
      oneEighth_le_norm_add_one_of_neg_half_le_re hseam, hseam⟩
  · rintro ⟨hz, houter, hzLower, _hzLeftHole, hseam⟩
    refine ⟨hz,
      (coordinateUnlinkExteriorPlanarRightInnerRadius_le_norm_iff m z).mpr hzLower, ?_⟩
    let u := nonzeroUnitDirection ⟨z, hz⟩
    apply (norm_le_coordinateUnlinkExteriorPlanarRightOuterRadius_iff m z u).mpr
    have hu := coordinateUnlinkExteriorPlanarRightAngularReal_bounds m u
    apply (planarRightHalf_constraints_iff_le_outerRadiusBase
      hu.1 hu.2 (pow_nonneg (norm_nonneg z) m)).mp
    constructor
    · have h := (norm_pow_add_half_le_sphereHandleRadius_iff m z).mp houter
      simpa only [u, coordinateUnlinkExteriorPlanarRightAngularReal,
        nonzeroUnitDirection_coe, planarOuterAngularReal] using h
    · rw [re_pow_eq_norm_pow_mul_planarOuterAngularReal] at hseam
      simpa only [u, coordinateUnlinkExteriorPlanarRightAngularReal,
        nonzeroUnitDirection_coe, planarOuterAngularReal, mul_comm] using hseam

/-- Flattening does not change the actual right flower half. -/
def coordinateUnlinkExteriorPlanarFlowerRightHalfRawHomeomorph
    (m : ℕ) :
    ↑(coordinateUnlinkExteriorPlanarFlowerRightHalfRawSet m) ≃ₜ
      CoordinateUnlinkExteriorPlanarFlowerRightHalf m where
  toFun z := ⟨⟨⟨z.1, z.2.1⟩, ⟨z.2.2.1, z.2.2.2.1, z.2.2.2.2.1⟩⟩,
    z.2.2.2.2.2⟩
  invFun z := ⟨z.1.1.1, ⟨z.1.1.2, z.1.2.1, z.1.2.2.1, z.1.2.2.2, z.2⟩⟩
  left_inv z := by rfl
  right_inv z := by rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The actual closed right flower half is a literal annulus. -/
def coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph
    (m : ℕ) [NeZero m] :
    PartialSphereSpinAnnulus ≃ₜ
      CoordinateUnlinkExteriorPlanarFlowerRightHalf m :=
  (unlinkUnitCircleHomeomorph.prodCongr
      (Homeomorph.refl (Set.Icc (0 : ℝ) 1))).trans <|
    (directionalRadialAnnulusHomeomorph
      (coordinateUnlinkExteriorPlanarRightInnerRadius m)
      (coordinateUnlinkExteriorPlanarRightOuterRadius m)
      (coordinateUnlinkExteriorPlanarRightInnerRadius_pos m)
      (coordinateUnlinkExteriorPlanarRightInner_lt_outer m)
      (continuous_coordinateUnlinkExteriorPlanarRightOuterRadius m)).trans <|
        (Homeomorph.setCongr
          (directionalRadialAnnulus_rightOuter_eq_rightHalfRawSet m)).trans <|
            coordinateUnlinkExteriorPlanarFlowerRightHalfRawHomeomorph m

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_apply_coe
    (m : ℕ) [NeZero m] (x : PartialSphereSpinAnnulus) :
    (coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m x).1.1.1 =
      directionalRadialAnnulusRadius
          (coordinateUnlinkExteriorPlanarRightInnerRadius m)
          (coordinateUnlinkExteriorPlanarRightOuterRadius m)
          (unlinkUnitCircleHomeomorph x.1) x.2 •
        unlinkUnitCircleComplex x.1 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_zero_coe
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    (coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m (u, 0)).1.1.1 =
      coordinateUnlinkExteriorPlanarRightInnerRadius m •
        unlinkUnitCircleComplex u := by
  rw [coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_apply_coe,
    directionalRadialAnnulusRadius_zero]

@[simp]
theorem coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_one_coe
    (m : ℕ) [NeZero m] (u : Sphere 1) :
    (coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m (u, 1)).1.1.1 =
      coordinateUnlinkExteriorPlanarRightOuterRadius m
          (unlinkUnitCircleHomeomorph u) • unlinkUnitCircleComplex u := by
  rw [coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_apply_coe,
    directionalRadialAnnulusRadius_one]

/-! ## Exact endpoint ranges -/

theorem coordinateUnlinkExteriorPlanarLeft_center_outer_eq_iff
    {z : ℂ} (hz : z ≠ 0) :
    ‖(-1 : ℂ) + z + (1 / 2 : ℂ)‖ = sphereHandleRadius ↔
      ‖z‖ ^ 2 -
          (nonzeroUnitDirection ⟨z, hz⟩).1.re * ‖z‖ = 1 / 4 := by
  have hvec : (-1 : ℂ) + z + (1 / 2 : ℂ) = z - (1 / 2 : ℂ) := by ring
  rw [hvec, ← sq_eq_sq₀ (norm_nonneg _) sphereHandleRadius_pos.le,
    sphereHandleRadius_sq, norm_sub_half_sq,
    complex_re_eq_norm_mul_direction hz]
  constructor <;> intro h <;> nlinarith

theorem coordinateUnlinkExteriorPlanarLeft_center_seam_eq_iff
    {z : ℂ} (hz : z ≠ 0) :
    ((-1 : ℂ) + z).re = -1 / 2 ↔
      ‖z‖ * (nonzeroUnitDirection ⟨z, hz⟩).1.re = 1 / 2 := by
  rw [Complex.add_re, Complex.neg_re, Complex.one_re,
    complex_re_eq_norm_mul_direction hz]
  norm_num
  constructor <;> intro h <;> linarith

theorem coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_add_one
    (x : PartialSphereSpinAnnulus) :
    (coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x : ℂ) + 1 =
      directionalRadialAnnulusRadius (1 / 8 : ℝ)
          coordinateUnlinkExteriorPlanarLeftOuterRadius
          (unlinkUnitCircleHomeomorph x.1) x.2 •
        unlinkUnitCircleComplex x.1 := by
  rw [coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_apply_coe]
  ring

theorem norm_coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_add_one
    (x : PartialSphereSpinAnnulus) :
    ‖(coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x : ℂ) + 1‖ =
      directionalRadialAnnulusRadius (1 / 8 : ℝ)
        coordinateUnlinkExteriorPlanarLeftOuterRadius
        (unlinkUnitCircleHomeomorph x.1) x.2 := by
  rw [coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_add_one,
    norm_smul, Real.norm_eq_abs,
    abs_of_pos (directionalRadialAnnulusRadius_pos (by norm_num)
      oneEighth_lt_coordinateUnlinkExteriorPlanarLeftOuterRadius _ _),
    norm_unlinkUnitCircleComplex, mul_one]

theorem direction_coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_add_one
    (x : PartialSphereSpinAnnulus)
    (hne : (coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x : ℂ) + 1 ≠ 0) :
    nonzeroUnitDirection
        ⟨(coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x : ℂ) + 1,
          hne⟩ =
      unlinkUnitCircleHomeomorph x.1 := by
  apply Subtype.ext
  change NormedSpace.normalize
      ((coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x : ℂ) + 1) =
    unlinkUnitCircleComplex x.1
  rw [coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_add_one,
    NormedSpace.normalize_smul_of_pos
      (directionalRadialAnnulusRadius_pos (by norm_num)
        oneEighth_lt_coordinateUnlinkExteriorPlanarLeftOuterRadius _ _)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (norm_unlinkUnitCircleComplex x.1)

/-- Inner endpoint of the left annulus: the left radius-`1/8` circle. -/
def coordinateUnlinkExteriorPlanarBaseLeftHalfInnerEndpointSet :
    Set CoordinateUnlinkExteriorPlanarBaseLeftHalf :=
  {w | ‖w.1 + 1‖ = (1 / 8 : ℝ)}

/-- Outer endpoint of the left annulus: the vertical seam together with the left round arc. -/
def coordinateUnlinkExteriorPlanarBaseLeftHalfOuterEndpointSet :
    Set CoordinateUnlinkExteriorPlanarBaseLeftHalf :=
  {w | w.1.re = -1 / 2 ∨
    ‖w.1 + (1 / 2 : ℂ)‖ = sphereHandleRadius}

theorem range_coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_zero :
    range (fun u : Sphere 1 ↦
      coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph (u, 0)) =
      coordinateUnlinkExteriorPlanarBaseLeftHalfInnerEndpointSet := by
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    change ‖(coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph
      (u, 0) : ℂ) + 1‖ = (1 / 8 : ℝ)
    rw [norm_coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_add_one,
      directionalRadialAnnulusRadius_zero]
  · intro hw
    let x := coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.symm w
    have hxApply : coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x = w :=
      coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.apply_symm_apply w
    have hRadius : directionalRadialAnnulusRadius (1 / 8 : ℝ)
        coordinateUnlinkExteriorPlanarLeftOuterRadius
        (unlinkUnitCircleHomeomorph x.1) x.2 = 1 / 8 := by
      rw [← norm_coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_add_one x,
        hxApply]
      exact hw
    have hgap := oneEighth_lt_coordinateUnlinkExteriorPlanarLeftOuterRadius
      (unlinkUnitCircleHomeomorph x.1)
    have ht : (x.2 : ℝ) = 0 := by
      unfold directionalRadialAnnulusRadius at hRadius
      have hprod : (x.2 : ℝ) *
          (coordinateUnlinkExteriorPlanarLeftOuterRadius
            (unlinkUnitCircleHomeomorph x.1) - 1 / 8) = 0 := by
        linarith
      exact (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hgap.ne')
    refine ⟨x.1, ?_⟩
    calc
      coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph (x.1, 0) =
          coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x := by
            apply congrArg coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph
            exact Prod.ext rfl (Subtype.ext ht.symm)
      _ = w := hxApply

theorem range_coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_one :
    range (fun u : Sphere 1 ↦
      coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph (u, 1)) =
      coordinateUnlinkExteriorPlanarBaseLeftHalfOuterEndpointSet := by
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    let x : PartialSphereSpinAnnulus := (u, 1)
    let z : ℂ :=
      (coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x : ℂ) + 1
    have hzNorm : ‖z‖ = coordinateUnlinkExteriorPlanarLeftOuterRadius
        (unlinkUnitCircleHomeomorph u) := by
      simpa only [x, z, directionalRadialAnnulusRadius_one] using
        norm_coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_add_one x
    have hOuterPos : 0 < coordinateUnlinkExteriorPlanarLeftOuterRadius
        (unlinkUnitCircleHomeomorph u) :=
      (by norm_num : (0 : ℝ) < 1 / 8).trans
        (oneEighth_lt_coordinateUnlinkExteriorPlanarLeftOuterRadius _)
    have hz : z ≠ 0 := norm_ne_zero_iff.mp <|
      hzNorm.trans_ne hOuterPos.ne'
    have hdir := direction_coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_add_one
      x hz
    have hu := complexUnit_re_bounds (unlinkUnitCircleHomeomorph u)
    have hconstraints := (planarLeftHalf_constraints_iff_le_outerRadius
      hu.1 hu.2 (norm_nonneg z)).mpr hzNorm.le
    have hend := (planarLeftHalf_eq_outerRadius_iff
      hu.1 hu.2 (norm_nonneg z) hconstraints).mp hzNorm
    change ((coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x : ℂ)).re =
        -1 / 2 ∨
      ‖(coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x : ℂ) +
        (1 / 2 : ℂ)‖ = sphereHandleRadius
    have hcenter : (-1 : ℂ) + z =
        (coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x : ℂ) := by
      dsimp only [z]
      ring
    rcases hend with houter | hseam
    · right
      have h := (coordinateUnlinkExteriorPlanarLeft_center_outer_eq_iff hz).mpr <| by
        rw [hdir]
        simpa only [z, mul_comm] using houter
      rw [hcenter] at h
      exact h
    · left
      have h := (coordinateUnlinkExteriorPlanarLeft_center_seam_eq_iff hz).mpr <| by
        rw [hdir]
        simpa only [z, mul_comm] using hseam
      rw [hcenter] at h
      exact h
  · intro hw
    let x := coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.symm w
    have hxApply : coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x = w :=
      coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph.apply_symm_apply w
    let z : ℂ := (w : ℂ) + 1
    have hzLower : (1 / 8 : ℝ) ≤ ‖z‖ := by
      have := w.2.1.2.2
      simpa only [z] using this
    have hz : z ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hzLower
      norm_num at hzLower
    have hRadius : ‖z‖ = directionalRadialAnnulusRadius (1 / 8 : ℝ)
        coordinateUnlinkExteriorPlanarLeftOuterRadius
        (unlinkUnitCircleHomeomorph x.1) x.2 := by
      rw [← norm_coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_add_one x,
        hxApply]
    have hcenter : (-1 : ℂ) + z = (w : ℂ) := by
      dsimp only [z]
      ring
    have hdir : nonzeroUnitDirection ⟨z, hz⟩ =
        unlinkUnitCircleHomeomorph x.1 := by
      have hne : (coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x : ℂ) +
          1 ≠ 0 := by simpa only [hxApply, z] using hz
      simpa only [hxApply, z] using
        direction_coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph_add_one x hne
    have hu := complexUnit_re_bounds (nonzeroUnitDirection ⟨z, hz⟩)
    have houterActual : ‖(-1 : ℂ) + z + (1 / 2 : ℂ)‖ ≤
        sphereHandleRadius := by rw [hcenter]; exact w.2.1.1
    have hseamActual : ((-1 : ℂ) + z).re ≤ -1 / 2 := by
      rw [hcenter]
      exact w.2.2
    have houterLe :=
      (coordinateUnlinkExteriorPlanarLeft_center_outer_iff hz).mp houterActual
    have hseamLe :=
      (coordinateUnlinkExteriorPlanarLeft_center_seam_iff hz).mp hseamActual
    have hconstraints : ‖z‖ ^ 2 -
          (nonzeroUnitDirection ⟨z, hz⟩).1.re * ‖z‖ ≤ 1 / 4 ∧
        ‖z‖ * (nonzeroUnitDirection ⟨z, hz⟩).1.re ≤ 1 / 2 :=
      ⟨houterLe, hseamLe⟩
    have hend : ‖z‖ ^ 2 -
          (nonzeroUnitDirection ⟨z, hz⟩).1.re * ‖z‖ = 1 / 4 ∨
        ‖z‖ * (nonzeroUnitDirection ⟨z, hz⟩).1.re = 1 / 2 := by
      rcases hw with hseam | houter
      · exact Or.inr <|
          (coordinateUnlinkExteriorPlanarLeft_center_seam_eq_iff hz).mp <| by
            rw [hcenter]
            exact hseam
      · exact Or.inl <|
          (coordinateUnlinkExteriorPlanarLeft_center_outer_eq_iff hz).mp <| by
            rw [hcenter]
            exact houter
    have hzOuter := (planarLeftHalf_eq_outerRadius_iff
      hu.1 hu.2 (norm_nonneg z) hconstraints).mpr hend
    rw [hdir] at hzOuter
    have hOne : (x.2 : ℝ) = 1 := by
      rw [hRadius] at hzOuter
      unfold directionalRadialAnnulusRadius at hzOuter
      change (1 / 8 : ℝ) + (x.2 : ℝ) *
          (coordinateUnlinkExteriorPlanarLeftOuterRadius
            (unlinkUnitCircleHomeomorph x.1) - 1 / 8) =
        coordinateUnlinkExteriorPlanarLeftOuterRadius
          (unlinkUnitCircleHomeomorph x.1) at hzOuter
      have hgap := oneEighth_lt_coordinateUnlinkExteriorPlanarLeftOuterRadius
        (unlinkUnitCircleHomeomorph x.1)
      have hprod : ((x.2 : ℝ) - 1) *
          (coordinateUnlinkExteriorPlanarLeftOuterRadius
            (unlinkUnitCircleHomeomorph x.1) - 1 / 8) = 0 := by
        calc
          _ = (x.2 : ℝ) *
                (coordinateUnlinkExteriorPlanarLeftOuterRadius
                  (unlinkUnitCircleHomeomorph x.1) - 1 / 8) -
              (coordinateUnlinkExteriorPlanarLeftOuterRadius
                (unlinkUnitCircleHomeomorph x.1) - 1 / 8) := by ring
          _ = 0 := by linarith
      have := (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hgap.ne')
      linarith
    refine ⟨x.1, ?_⟩
    calc
      coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph (x.1, 1) =
          coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph x := by
            apply congrArg coordinateUnlinkExteriorPlanarBaseLeftHalfAnnulusHomeomorph
            exact Prod.ext rfl (Subtype.ext hOne.symm)
      _ = w := hxApply

theorem norm_coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_apply
    (m : ℕ) [NeZero m] (x : PartialSphereSpinAnnulus) :
    ‖(coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m x).1.1.1‖ =
      directionalRadialAnnulusRadius
        (coordinateUnlinkExteriorPlanarRightInnerRadius m)
        (coordinateUnlinkExteriorPlanarRightOuterRadius m)
        (unlinkUnitCircleHomeomorph x.1) x.2 := by
  rw [coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_apply_coe,
    norm_smul, Real.norm_eq_abs,
    abs_of_pos (directionalRadialAnnulusRadius_pos
      (coordinateUnlinkExteriorPlanarRightInnerRadius_pos m)
      (coordinateUnlinkExteriorPlanarRightInner_lt_outer m) _ _),
    norm_unlinkUnitCircleComplex, mul_one]

theorem direction_coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_apply
    (m : ℕ) [NeZero m] (x : PartialSphereSpinAnnulus)
    (hne : (coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m x).1.1.1 ≠ 0) :
    nonzeroUnitDirection
        ⟨(coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m x).1.1.1,
          hne⟩ =
      unlinkUnitCircleHomeomorph x.1 := by
  apply Subtype.ext
  change NormedSpace.normalize
      (coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m x).1.1.1 =
    unlinkUnitCircleComplex x.1
  rw [coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_apply_coe,
    NormedSpace.normalize_smul_of_pos
      (directionalRadialAnnulusRadius_pos
        (coordinateUnlinkExteriorPlanarRightInnerRadius_pos m)
        (coordinateUnlinkExteriorPlanarRightInner_lt_outer m) _ _)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (norm_unlinkUnitCircleComplex x.1)

/-- Inner endpoint of the right flower annulus, expressed in the polynomial coordinate. -/
def coordinateUnlinkExteriorPlanarFlowerRightHalfInnerEndpointSet
    (m : ℕ) : Set (CoordinateUnlinkExteriorPlanarFlowerRightHalf m) :=
  {z | ‖z.1.1.1 ^ m‖ = (1 / 8 : ℝ)}

/-- Outer endpoint of the right flower annulus: all lifted seam arcs together with the round
polynomial outer-boundary sectors. -/
def coordinateUnlinkExteriorPlanarFlowerRightHalfOuterEndpointSet
    (m : ℕ) : Set (CoordinateUnlinkExteriorPlanarFlowerRightHalf m) :=
  {z | (z.1.1.1 ^ m).re = -1 / 2 ∨
    ‖z.1.1.1 ^ m + (1 / 2 : ℂ)‖ = sphereHandleRadius}

theorem range_coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_zero
    (m : ℕ) [NeZero m] :
    range (fun u : Sphere 1 ↦
      coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m (u, 0)) =
      coordinateUnlinkExteriorPlanarFlowerRightHalfInnerEndpointSet m := by
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    change ‖(coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph
      m (u, 0)).1.1.1 ^ m‖ = (1 / 8 : ℝ)
    rw [norm_pow,
      norm_coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_apply,
      directionalRadialAnnulusRadius_zero,
      coordinateUnlinkExteriorPlanarRightInnerRadius_pow]
  · intro hw
    let x := (coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m).symm w
    have hxApply :
        coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m x = w :=
      (coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m).apply_symm_apply w
    have hPowRadius :
        (directionalRadialAnnulusRadius
          (coordinateUnlinkExteriorPlanarRightInnerRadius m)
          (coordinateUnlinkExteriorPlanarRightOuterRadius m)
          (unlinkUnitCircleHomeomorph x.1) x.2) ^ m = 1 / 8 := by
      rw [← norm_coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_apply m x,
        ← norm_pow, hxApply]
      exact hw
    have hRadius : directionalRadialAnnulusRadius
          (coordinateUnlinkExteriorPlanarRightInnerRadius m)
          (coordinateUnlinkExteriorPlanarRightOuterRadius m)
          (unlinkUnitCircleHomeomorph x.1) x.2 =
        coordinateUnlinkExteriorPlanarRightInnerRadius m := by
      apply (pow_left_inj₀
        (directionalRadialAnnulusRadius_pos
          (coordinateUnlinkExteriorPlanarRightInnerRadius_pos m)
          (coordinateUnlinkExteriorPlanarRightInner_lt_outer m) _ _).le
        (coordinateUnlinkExteriorPlanarRightInnerRadius_pos m).le
        (NeZero.ne m)).mp
      rw [hPowRadius, coordinateUnlinkExteriorPlanarRightInnerRadius_pow]
    have hgap := coordinateUnlinkExteriorPlanarRightInner_lt_outer m
      (unlinkUnitCircleHomeomorph x.1)
    have ht : (x.2 : ℝ) = 0 := by
      unfold directionalRadialAnnulusRadius at hRadius
      have hprod : (x.2 : ℝ) *
          (coordinateUnlinkExteriorPlanarRightOuterRadius m
            (unlinkUnitCircleHomeomorph x.1) -
              coordinateUnlinkExteriorPlanarRightInnerRadius m) = 0 := by
        linarith
      exact (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hgap.ne')
    refine ⟨x.1, ?_⟩
    calc
      coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m (x.1, 0) =
          coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m x := by
            apply congrArg
              (coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m)
            exact Prod.ext rfl (Subtype.ext ht.symm)
      _ = w := hxApply

theorem range_coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_one
    (m : ℕ) [NeZero m] :
    range (fun u : Sphere 1 ↦
      coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m (u, 1)) =
      coordinateUnlinkExteriorPlanarFlowerRightHalfOuterEndpointSet m := by
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    let x : PartialSphereSpinAnnulus := (u, 1)
    let z : ℂ :=
      (coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m x).1.1.1
    have hzNorm : ‖z‖ = coordinateUnlinkExteriorPlanarRightOuterRadius m
        (unlinkUnitCircleHomeomorph u) := by
      simpa only [x, z, directionalRadialAnnulusRadius_one] using
        norm_coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_apply m x
    have hz : z ≠ 0 := norm_ne_zero_iff.mp <|
      hzNorm.trans_ne
        (coordinateUnlinkExteriorPlanarRightOuterRadius_pos m _).ne'
    have hdir :=
      direction_coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_apply
        m x hz
    have hdirZ : nonzeroUnitDirection ⟨z, hz⟩ =
        unlinkUnitCircleHomeomorph u := by
      simpa only [x, z] using hdir
    have hangular : planarOuterAngularReal m z =
        coordinateUnlinkExteriorPlanarRightAngularReal m
          (unlinkUnitCircleHomeomorph u) := by
      unfold planarOuterAngularReal coordinateUnlinkExteriorPlanarRightAngularReal
      rw [show NormedSpace.normalize z = unlinkUnitCircleComplex u from
        congrArg Subtype.val hdirZ]
      rw [unlinkUnitCircleHomeomorph_coe]
    have hu := coordinateUnlinkExteriorPlanarRightAngularReal_bounds m
      (unlinkUnitCircleHomeomorph u)
    have hpowNorm : ‖z‖ ^ m =
        coordinateUnlinkExteriorPlanarRightOuterRadiusBaseScalar
          (coordinateUnlinkExteriorPlanarRightAngularReal m
            (unlinkUnitCircleHomeomorph u)) := by
      rw [hzNorm, coordinateUnlinkExteriorPlanarRightOuterRadius_pow]
    have hconstraints := (planarRightHalf_constraints_iff_le_outerRadiusBase
      hu.1 hu.2 (pow_nonneg (norm_nonneg z) m)).mpr hpowNorm.le
    have hend := (planarRightHalf_eq_outerRadiusBase_iff
      hu.1 hu.2 (pow_nonneg (norm_nonneg z) m) hconstraints).mp hpowNorm
    change (z ^ m).re = -1 / 2 ∨
      ‖z ^ m + (1 / 2 : ℂ)‖ = sphereHandleRadius
    rcases hend with houter | hseam
    · right
      apply (norm_pow_add_half_eq_sphereHandleRadius_iff m z).mpr
      rw [hangular]
      exact houter
    · left
      rw [re_pow_eq_norm_pow_mul_planarOuterAngularReal]
      rw [hangular]
      calc
        ‖z‖ ^ m * coordinateUnlinkExteriorPlanarRightAngularReal m
            (unlinkUnitCircleHomeomorph u) =
            coordinateUnlinkExteriorPlanarRightAngularReal m
              (unlinkUnitCircleHomeomorph u) * ‖z‖ ^ m := mul_comm _ _
        _ = -1 / 2 := hseam
  · intro hw
    let x := (coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m).symm w
    have hxApply :
        coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m x = w :=
      (coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m).apply_symm_apply w
    let z : ℂ := w.1.1.1
    have hz : z ≠ 0 := w.1.1.2
    have hRadius : ‖z‖ = directionalRadialAnnulusRadius
        (coordinateUnlinkExteriorPlanarRightInnerRadius m)
        (coordinateUnlinkExteriorPlanarRightOuterRadius m)
        (unlinkUnitCircleHomeomorph x.1) x.2 := by
      rw [← norm_coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_apply m x,
        hxApply]
    have hdir : nonzeroUnitDirection ⟨z, hz⟩ =
        unlinkUnitCircleHomeomorph x.1 := by
      have hne :
          (coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m x).1.1.1 ≠
            0 := by simpa only [hxApply, z] using hz
      simpa only [hxApply, z] using
        direction_coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph_apply
          m x hne
    have hu := coordinateUnlinkExteriorPlanarRightAngularReal_bounds m
      (nonzeroUnitDirection ⟨z, hz⟩)
    have houterConstraint :=
      (norm_pow_add_half_le_sphereHandleRadius_iff m z).mp w.1.2.1
    have hseamConstraint : -1 / 2 ≤ ‖z‖ ^ m * planarOuterAngularReal m z := by
      rw [← re_pow_eq_norm_pow_mul_planarOuterAngularReal]
      exact w.2
    have hconstraints : (‖z‖ ^ m) ^ 2 +
          coordinateUnlinkExteriorPlanarRightAngularReal m
              (nonzeroUnitDirection ⟨z, hz⟩) * ‖z‖ ^ m ≤ 1 / 4 ∧
        -1 / 2 ≤ coordinateUnlinkExteriorPlanarRightAngularReal m
            (nonzeroUnitDirection ⟨z, hz⟩) * ‖z‖ ^ m := by
      constructor
      · simpa only [coordinateUnlinkExteriorPlanarRightAngularReal,
          planarOuterAngularReal, nonzeroUnitDirection_coe] using houterConstraint
      · simpa only [coordinateUnlinkExteriorPlanarRightAngularReal,
          planarOuterAngularReal, nonzeroUnitDirection_coe, mul_comm] using hseamConstraint
    have hend : (‖z‖ ^ m) ^ 2 +
          coordinateUnlinkExteriorPlanarRightAngularReal m
              (nonzeroUnitDirection ⟨z, hz⟩) * ‖z‖ ^ m = 1 / 4 ∨
        coordinateUnlinkExteriorPlanarRightAngularReal m
            (nonzeroUnitDirection ⟨z, hz⟩) * ‖z‖ ^ m = -1 / 2 := by
      rcases hw with hseam | houter
      · right
        rw [re_pow_eq_norm_pow_mul_planarOuterAngularReal] at hseam
        simpa only [coordinateUnlinkExteriorPlanarRightAngularReal,
          planarOuterAngularReal, nonzeroUnitDirection_coe, mul_comm] using hseam
      · left
        have h := (norm_pow_add_half_eq_sphereHandleRadius_iff m z).mp houter
        simpa only [coordinateUnlinkExteriorPlanarRightAngularReal,
          planarOuterAngularReal, nonzeroUnitDirection_coe] using h
    have hpowOuter := (planarRightHalf_eq_outerRadiusBase_iff
      hu.1 hu.2 (pow_nonneg (norm_nonneg z) m) hconstraints).mpr hend
    rw [hdir] at hpowOuter
    have hzOuter : ‖z‖ = coordinateUnlinkExteriorPlanarRightOuterRadius m
        (unlinkUnitCircleHomeomorph x.1) := by
      apply (pow_left_inj₀ (norm_nonneg z)
        (coordinateUnlinkExteriorPlanarRightOuterRadius_pos m _).le
        (NeZero.ne m)).mp
      rw [coordinateUnlinkExteriorPlanarRightOuterRadius_pow]
      exact hpowOuter
    have hOne : (x.2 : ℝ) = 1 := by
      rw [hRadius] at hzOuter
      unfold directionalRadialAnnulusRadius at hzOuter
      change coordinateUnlinkExteriorPlanarRightInnerRadius m + (x.2 : ℝ) *
          (coordinateUnlinkExteriorPlanarRightOuterRadius m
              (unlinkUnitCircleHomeomorph x.1) -
            coordinateUnlinkExteriorPlanarRightInnerRadius m) =
        coordinateUnlinkExteriorPlanarRightOuterRadius m
          (unlinkUnitCircleHomeomorph x.1) at hzOuter
      have hgap := coordinateUnlinkExteriorPlanarRightInner_lt_outer m
        (unlinkUnitCircleHomeomorph x.1)
      have hprod : ((x.2 : ℝ) - 1) *
          (coordinateUnlinkExteriorPlanarRightOuterRadius m
              (unlinkUnitCircleHomeomorph x.1) -
            coordinateUnlinkExteriorPlanarRightInnerRadius m) = 0 := by
        calc
          _ = (x.2 : ℝ) *
                (coordinateUnlinkExteriorPlanarRightOuterRadius m
                    (unlinkUnitCircleHomeomorph x.1) -
                  coordinateUnlinkExteriorPlanarRightInnerRadius m) -
              (coordinateUnlinkExteriorPlanarRightOuterRadius m
                  (unlinkUnitCircleHomeomorph x.1) -
                coordinateUnlinkExteriorPlanarRightInnerRadius m) := by ring
          _ = 0 := by linarith
      have := (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hgap.ne')
      linarith
    refine ⟨x.1, ?_⟩
    calc
      coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m (x.1, 1) =
          coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m x := by
            apply congrArg
              (coordinateUnlinkExteriorPlanarFlowerRightHalfAnnulusHomeomorph m)
            exact Prod.ext rfl (Subtype.ext hOne.symm)
      _ = w := hxApply

end SplittingSpheres
