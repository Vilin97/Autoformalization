/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.DirectionalRadialHomeomorph
public import SplittingSpheres.Handlebody.CoordinateExteriorPlanarFlower

/-!
# Radial straightening data for the planar flower's outer disk

The outer flower inequality is the inverse image of the disk
`closedBall (-1/2) sphereHandleRadius` under `z ↦ z ^ m`.  Along every ray it has one positive
endpoint.  This file constructs the corresponding continuous positive radial scale and the
resulting ambient homeomorphism.

The exact identification of its radial body with the polynomial inequality is kept separate from
the abstract radial-topology constructor.  No assertion about the inner holes or compact-surface
classification is made here.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology

namespace SplittingSpheres

/-- The positive root of `s² + a s = 1/4`. -/
def planarOuterQuadraticRadius (a : ℝ) : ℝ :=
  (Real.sqrt (a ^ 2 + 1) - a) / 2

theorem planarOuterQuadraticRadius_sq_add_mul (a : ℝ) :
    planarOuterQuadraticRadius a ^ 2 + a * planarOuterQuadraticRadius a = 1 / 4 := by
  have hs : 0 ≤ a ^ 2 + 1 := by positivity
  have hsqrt := Real.sq_sqrt hs
  rw [planarOuterQuadraticRadius]
  nlinarith

theorem oneEighth_le_planarOuterQuadraticRadius
    {a : ℝ} (ha : a ≤ 1) :
    (1 / 8 : ℝ) ≤ planarOuterQuadraticRadius a := by
  have hs : 0 ≤ Real.sqrt (a ^ 2 + 1) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (a ^ 2 + 1) ^ 2 = a ^ 2 + 1 :=
    Real.sq_sqrt (by positivity)
  rw [planarOuterQuadraticRadius]
  nlinarith

theorem planarOuterQuadraticRadius_le_two
    {a : ℝ} (ha : -1 ≤ a) :
    planarOuterQuadraticRadius a ≤ 2 := by
  have hs : 0 ≤ Real.sqrt (a ^ 2 + 1) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (a ^ 2 + 1) ^ 2 = a ^ 2 + 1 :=
    Real.sq_sqrt (by positivity)
  rw [planarOuterQuadraticRadius]
  nlinarith

theorem planarOuterQuadraticRadius_pos {a : ℝ} (ha : a ≤ 1) :
    0 < planarOuterQuadraticRadius a :=
  (by norm_num : (0 : ℝ) < 1 / 8).trans_le
    (oneEighth_le_planarOuterQuadraticRadius ha)

theorem planarOuterQuadraticRadius_add_arg_pos
    {a : ℝ} (ha : -1 ≤ a) :
    0 < planarOuterQuadraticRadius a + a := by
  have h := planarOuterQuadraticRadius_pos (a := -a) (by linarith)
  simp only [planarOuterQuadraticRadius] at h ⊢
  have hsquare : (-a) ^ 2 = a ^ 2 := by ring
  rw [hsquare] at h
  linarith

/-- On the nonnegative ray, the quadratic disk inequality stops exactly at its positive root. -/
theorem sq_add_mul_le_quarter_iff_le_planarOuterQuadraticRadius
    {a s : ℝ} (ha : -1 ≤ a) (ha' : a ≤ 1) (hs : 0 ≤ s) :
    s ^ 2 + a * s ≤ 1 / 4 ↔ s ≤ planarOuterQuadraticRadius a := by
  let p := planarOuterQuadraticRadius a
  have hp : 0 < p := planarOuterQuadraticRadius_pos ha'
  have hpa : 0 < p + a := planarOuterQuadraticRadius_add_arg_pos ha
  have hpEq : p ^ 2 + a * p = 1 / 4 :=
    planarOuterQuadraticRadius_sq_add_mul a
  have hfactor (t : ℝ) :
      t ^ 2 + a * t - 1 / 4 = (t - p) * (t + p + a) := by
    nlinarith
  constructor
  · intro h
    by_contra hle
    have htp : 0 < s - p := sub_pos.mpr (lt_of_not_ge hle)
    have hsecond : 0 < s + p + a := by nlinarith
    have hprod : 0 < (s - p) * (s + p + a) := mul_pos htp hsecond
    rw [← hfactor] at hprod
    linarith
  · intro h
    have hfirst : s - p ≤ 0 := sub_nonpos.mpr h
    have hsecond : 0 ≤ s + p + a := by linarith
    have hprod : (s - p) * (s + p + a) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hfirst hsecond
    rw [← hfactor] at hprod
    linarith

theorem sq_add_mul_eq_quarter_iff_eq_planarOuterQuadraticRadius
    {a s : ℝ} (ha : -1 ≤ a) (ha' : a ≤ 1) (hs : 0 ≤ s) :
    s ^ 2 + a * s = 1 / 4 ↔ s = planarOuterQuadraticRadius a := by
  let p := planarOuterQuadraticRadius a
  have hp : 0 < p := planarOuterQuadraticRadius_pos ha'
  have hpa : 0 < p + a := planarOuterQuadraticRadius_add_arg_pos ha
  have hpEq : p ^ 2 + a * p = 1 / 4 :=
    planarOuterQuadraticRadius_sq_add_mul a
  constructor
  · intro h
    have hfactor : (s - p) * (s + p + a) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hsp | hsecond
    · exact sub_eq_zero.mp hsp
    · have : 0 < s + p + a := by nlinarith
      exact (this.ne' hsecond).elim
  · rintro rfl
    exact hpEq

/-- The real part of the normalized angular `m`th power.  At the origin it is set to zero by
`NormedSpace.normalize`. -/
def planarOuterAngularReal (m : ℕ) (z : ℂ) : ℝ :=
  (NormedSpace.normalize z ^ m).re

theorem abs_planarOuterAngularReal_le_one (m : ℕ) (z : ℂ) :
    |planarOuterAngularReal m z| ≤ 1 := by
  calc
    |planarOuterAngularReal m z| ≤ ‖NormedSpace.normalize z ^ m‖ :=
      Complex.abs_re_le_norm _
    _ = ‖NormedSpace.normalize z‖ ^ m := norm_pow _ _
    _ ≤ 1 ^ m := by
      apply pow_le_pow_left₀ (norm_nonneg _) ?_
      by_cases hz : z = 0
      · simp [hz]
      · simp [NormedSpace.norm_normalize hz]
    _ = 1 := one_pow _

theorem neg_one_le_planarOuterAngularReal (m : ℕ) (z : ℂ) :
    -1 ≤ planarOuterAngularReal m z :=
  (abs_le.mp (abs_planarOuterAngularReal_le_one m z)).1

theorem planarOuterAngularReal_le_one (m : ℕ) (z : ℂ) :
    planarOuterAngularReal m z ≤ 1 :=
  (abs_le.mp (abs_planarOuterAngularReal_le_one m z)).2

theorem re_pow_eq_norm_pow_mul_planarOuterAngularReal (m : ℕ) (z : ℂ) :
    (z ^ m).re = ‖z‖ ^ m * planarOuterAngularReal m z := by
  calc
    (z ^ m).re = ((‖z‖ • NormedSpace.normalize z) ^ m).re :=
      congrArg (fun w : ℂ ↦ (w ^ m).re) (NormedSpace.norm_smul_normalize z).symm
    _ = ‖z‖ ^ m * planarOuterAngularReal m z := by
      rw [Complex.real_smul, mul_pow, ← Complex.ofReal_pow]
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rfl

theorem norm_add_half_sq (w : ℂ) :
    ‖w + (1 / 2 : ℂ)‖ ^ 2 = ‖w‖ ^ 2 + w.re + 1 / 4 := by
  rw [Complex.sq_norm (w + (1 / 2 : ℂ)), Complex.sq_norm w]
  simp [Complex.normSq]
  ring

theorem norm_pow_add_half_le_sphereHandleRadius_iff
    (m : ℕ) (z : ℂ) :
    ‖z ^ m + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius ↔
      (‖z‖ ^ m) ^ 2 + planarOuterAngularReal m z * (‖z‖ ^ m) ≤ 1 / 4 := by
  rw [← sq_le_sq₀ (norm_nonneg _) sphereHandleRadius_pos.le,
    sphereHandleRadius_sq, norm_add_half_sq, norm_pow,
    re_pow_eq_norm_pow_mul_planarOuterAngularReal]
  constructor <;> intro h <;> nlinarith

theorem norm_pow_add_half_eq_sphereHandleRadius_iff
    (m : ℕ) (z : ℂ) :
    ‖z ^ m + (1 / 2 : ℂ)‖ = sphereHandleRadius ↔
      (‖z‖ ^ m) ^ 2 + planarOuterAngularReal m z * (‖z‖ ^ m) = 1 / 4 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) sphereHandleRadius_pos.le,
    sphereHandleRadius_sq, norm_add_half_sq, norm_pow,
    re_pow_eq_norm_pow_mul_planarOuterAngularReal]
  constructor <;> intro h <;> nlinarith

/-- The `m`th root of the positive quadratic endpoint on the ray through `z`. -/
def planarOuterDirectionScale (m : ℕ) (z : ℂ) : ℝ :=
  planarOuterQuadraticRadius (planarOuterAngularReal m z) ^ ((m : ℝ)⁻¹ : ℝ)

theorem planarOuterDirectionScale_pos (m : ℕ) [NeZero m] (z : ℂ) :
    0 < planarOuterDirectionScale m z := by
  apply Real.rpow_pos_of_pos
  exact planarOuterQuadraticRadius_pos (planarOuterAngularReal_le_one m z)

theorem planarOuterDirectionScale_pow (m : ℕ) [NeZero m] (z : ℂ) :
    planarOuterDirectionScale m z ^ m =
      planarOuterQuadraticRadius (planarOuterAngularReal m z) := by
  rw [planarOuterDirectionScale]
  apply Real.rpow_inv_natCast_pow
  · exact (planarOuterQuadraticRadius_pos
      (planarOuterAngularReal_le_one m z)).le
  · exact NeZero.ne m

theorem norm_pow_add_half_le_sphereHandleRadius_iff_norm_le_scale
    (m : ℕ) [NeZero m] (z : ℂ) :
    ‖z ^ m + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius ↔
      ‖z‖ ≤ planarOuterDirectionScale m z := by
  rw [norm_pow_add_half_le_sphereHandleRadius_iff]
  rw [sq_add_mul_le_quarter_iff_le_planarOuterQuadraticRadius
    (neg_one_le_planarOuterAngularReal m z)
    (planarOuterAngularReal_le_one m z) (pow_nonneg (norm_nonneg z) m)]
  rw [← planarOuterDirectionScale_pow m z]
  exact pow_le_pow_iff_left₀ (norm_nonneg z)
    (planarOuterDirectionScale_pos m z).le (NeZero.ne m)

theorem norm_pow_add_half_eq_sphereHandleRadius_iff_norm_eq_scale
    (m : ℕ) [NeZero m] (z : ℂ) :
    ‖z ^ m + (1 / 2 : ℂ)‖ = sphereHandleRadius ↔
      ‖z‖ = planarOuterDirectionScale m z := by
  rw [norm_pow_add_half_eq_sphereHandleRadius_iff]
  rw [sq_add_mul_eq_quarter_iff_eq_planarOuterQuadraticRadius
    (neg_one_le_planarOuterAngularReal m z)
    (planarOuterAngularReal_le_one m z) (pow_nonneg (norm_nonneg z) m)]
  rw [← planarOuterDirectionScale_pow m z]
  exact pow_left_inj₀ (norm_nonneg z)
    (planarOuterDirectionScale_pos m z).le (NeZero.ne m)

/-- A uniform positive lower bound for the direction scale. -/
def planarOuterDirectionScaleLower (m : ℕ) : ℝ :=
  (1 / 8 : ℝ) ^ ((m : ℝ)⁻¹ : ℝ)

/-- A uniform upper bound for the direction scale. -/
def planarOuterDirectionScaleUpper (m : ℕ) : ℝ :=
  (2 : ℝ) ^ ((m : ℝ)⁻¹ : ℝ)

theorem planarOuterDirectionScaleLower_pos (m : ℕ) :
    0 < planarOuterDirectionScaleLower m := by
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem planarOuterDirectionScaleUpper_pos (m : ℕ) :
    0 < planarOuterDirectionScaleUpper m := by
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem planarOuterDirectionScaleLower_le (m : ℕ) [NeZero m] (z : ℂ) :
    planarOuterDirectionScaleLower m ≤ planarOuterDirectionScale m z := by
  apply Real.rpow_le_rpow (by norm_num)
  · exact oneEighth_le_planarOuterQuadraticRadius
      (planarOuterAngularReal_le_one m z)
  · exact inv_nonneg.mpr (Nat.cast_nonneg m)

theorem planarOuterDirectionScale_le_upper (m : ℕ) [NeZero m] (z : ℂ) :
    planarOuterDirectionScale m z ≤ planarOuterDirectionScaleUpper m := by
  apply Real.rpow_le_rpow
    (planarOuterQuadraticRadius_pos (planarOuterAngularReal_le_one m z)).le
  · exact planarOuterQuadraticRadius_le_two
      (neg_one_le_planarOuterAngularReal m z)
  · exact inv_nonneg.mpr (Nat.cast_nonneg m)

theorem planarOuterAngularReal_smul_of_pos
    (m : ℕ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    planarOuterAngularReal m (r • z) = planarOuterAngularReal m z := by
  exact congrArg (fun w : ℂ ↦ (w ^ m).re)
    (NormedSpace.normalize_smul_of_pos hr z)

theorem planarOuterDirectionScale_smul_of_pos
    (m : ℕ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    planarOuterDirectionScale m (r • z) = planarOuterDirectionScale m z := by
  change planarOuterQuadraticRadius (planarOuterAngularReal m (r • z)) ^
      ((m : ℝ)⁻¹ : ℝ) =
    planarOuterQuadraticRadius (planarOuterAngularReal m z) ^ ((m : ℝ)⁻¹ : ℝ)
  rw [planarOuterAngularReal_smul_of_pos m hr z]

theorem continuousOn_planarOuterAngularReal (m : ℕ) :
    ContinuousOn (planarOuterAngularReal m) (({0} : Set ℂ)ᶜ) := by
  intro z hz
  have hzne : z ≠ 0 := by simpa using hz
  unfold planarOuterAngularReal NormedSpace.normalize
  have hn : ContinuousAt (fun w : ℂ ↦ ‖w‖⁻¹) z :=
    continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hzne)
  have hnormalize : ContinuousAt (fun w : ℂ ↦ ‖w‖⁻¹ • w) z :=
    hn.smul continuousAt_id
  exact (Complex.continuous_re.continuousAt.comp
    (hnormalize.pow m)).continuousWithinAt

theorem continuous_planarOuterQuadraticRadius :
    Continuous planarOuterQuadraticRadius := by
  unfold planarOuterQuadraticRadius
  fun_prop

theorem continuousOn_planarOuterDirectionScale (m : ℕ) [NeZero m] :
    ContinuousOn (planarOuterDirectionScale m) (({0} : Set ℂ)ᶜ) := by
  have hbase : ContinuousOn
      (fun z : ℂ ↦ planarOuterQuadraticRadius (planarOuterAngularReal m z))
      (({0} : Set ℂ)ᶜ) := by
    simpa only [Function.comp_def] using
      continuous_planarOuterQuadraticRadius.comp_continuousOn
        (continuousOn_planarOuterAngularReal m)
  exact hbase.rpow_const fun z _ ↦ Or.inl <|
    (planarOuterQuadraticRadius_pos (planarOuterAngularReal_le_one m z)).ne'

/-- The global radial homeomorphism which straightens the flower's outer polynomial disk. -/
def planarOuterRadialHomeomorph (m : ℕ) [NeZero m] : ℂ ≃ₜ ℂ :=
  directionalRadialHomeomorph (planarOuterDirectionScale m)
    (planarOuterDirectionScaleLower_pos m)
    (planarOuterDirectionScaleUpper_pos m)
    (planarOuterDirectionScaleLower_le m)
    (planarOuterDirectionScale_le_upper m)
    (continuousOn_planarOuterDirectionScale m)
    (fun _r hr z ↦ planarOuterDirectionScale_smul_of_pos m hr z)

@[simp]
theorem planarOuterRadialHomeomorph_apply
    (m : ℕ) [NeZero m] (z : ℂ) :
    planarOuterRadialHomeomorph m z = planarOuterDirectionScale m z • z :=
  rfl

/-- The radial body reached from the closed unit disk. -/
abbrev CoordinateUnlinkExteriorPlanarOuterRadialBody (m : ℕ) : Type :=
  ↑(directionalRadialBody (planarOuterDirectionScale m))

/-- The closed unit disk is homeomorphic to the outer radial body. -/
def planarOuterRadialBodyHomeomorph (m : ℕ) [NeZero m] :
    closedBall (0 : ℂ) 1 ≃ₜ CoordinateUnlinkExteriorPlanarOuterRadialBody m :=
  directionalRadialBodyHomeomorph (planarOuterDirectionScale m)
    (planarOuterDirectionScaleLower_pos m)
    (planarOuterDirectionScaleUpper_pos m)
    (planarOuterDirectionScaleLower_le m)
    (planarOuterDirectionScale_le_upper m)
    (continuousOn_planarOuterDirectionScale m)
    (fun _r hr z ↦ planarOuterDirectionScale_smul_of_pos m hr z)

/-- The polynomial outer disk appearing in the flower inequalities. -/
def coordinateUnlinkExteriorPlanarOuterDiskSet (m : ℕ) : Set ℂ :=
  {z | ‖z ^ m + (1 / 2 : ℂ)‖ ≤ sphereHandleRadius}

/-- The exact polynomial boundary of the outer disk. -/
def coordinateUnlinkExteriorPlanarOuterDiskBoundarySet (m : ℕ) : Set ℂ :=
  {z | ‖z ^ m + (1 / 2 : ℂ)‖ = sphereHandleRadius}

theorem directionalRadialBody_planarOuterDirectionScale
    (m : ℕ) [NeZero m] :
    directionalRadialBody (planarOuterDirectionScale m) =
      coordinateUnlinkExteriorPlanarOuterDiskSet m := by
  ext z
  exact (norm_pow_add_half_le_sphereHandleRadius_iff_norm_le_scale m z).symm

theorem directionalRadialBoundary_planarOuterDirectionScale
    (m : ℕ) [NeZero m] :
    directionalRadialBoundary (planarOuterDirectionScale m) =
      coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m := by
  ext z
  exact (norm_pow_add_half_eq_sphereHandleRadius_iff_norm_eq_scale m z).symm

/-- The polynomial outer disk is an honest topological closed disk. -/
def planarOuterDiskHomeomorph (m : ℕ) [NeZero m] :
    closedBall (0 : ℂ) 1 ≃ₜ ↑(coordinateUnlinkExteriorPlanarOuterDiskSet m) :=
  (planarOuterRadialBodyHomeomorph m).trans <|
    Homeomorph.setCongr (directionalRadialBody_planarOuterDirectionScale m)

@[simp]
theorem planarOuterDiskHomeomorph_apply_val
    (m : ℕ) [NeZero m] (z : closedBall (0 : ℂ) 1) :
    (planarOuterDiskHomeomorph m z).1 = planarOuterDirectionScale m z.1 • z.1 :=
  rfl

/-- The polynomial outer boundary is an honest topological circle. -/
def planarOuterDiskBoundaryHomeomorph (m : ℕ) [NeZero m] :
    sphere (0 : ℂ) 1 ≃ₜ ↑(coordinateUnlinkExteriorPlanarOuterDiskBoundarySet m) :=
  (directionalRadialBoundaryHomeomorph (planarOuterDirectionScale m)
    (planarOuterDirectionScaleLower_pos m)
    (planarOuterDirectionScaleUpper_pos m)
    (planarOuterDirectionScaleLower_le m)
    (planarOuterDirectionScale_le_upper m)
    (continuousOn_planarOuterDirectionScale m)
    (fun _r hr z ↦ planarOuterDirectionScale_smul_of_pos m hr z)).trans <|
      Homeomorph.setCongr (directionalRadialBoundary_planarOuterDirectionScale m)

end SplittingSpheres
