/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.DiffeomorphOverLocalDiffeomorph
public import SplittingSpheres.Geometry.UnlinkClosedTubeExteriorPowerSmoothCover
public import SplittingSpheres.Geometry.UnlinkComplementSmoothExteriorDiffeomorph

/-!
# Smooth transport of the unlink power cover to the tube exterior

The smooth radial diffeomorphism from the strict unlink complement to the strict radius-`1/8`
tube exterior does not preserve the literal right-normal character.  Its normalized character
ratio nevertheless lies in the principal slit plane.  The principal logarithmic `m`th root of
that ratio gives a continuous gauge and hence a homeomorphism of the corresponding power
pullbacks.

The gauge is used only to construct the total-space homeomorphism.  Smoothness is reflected
through the two local-diffeomorphism projections: the total-space homeomorphism covers the
already smooth base diffeomorphism, so it is automatically a diffeomorphism for the explicit
pulled-back atlases.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open TopologicalSpace
open scoped ContDiff Manifold

namespace SplittingSpheres

private theorem smoothUnlinkNormalPlaneToComplex_real_smul (c : ℝ)
    (v : UnlinkNormalPlane) :
    unlinkNormalPlaneToComplex (c • v) = c • unlinkNormalPlaneToComplex v := by
  apply Complex.ext <;>
    simp [unlinkNormalPlaneToComplex, Complex.equivRealProdCLM_symm_apply]

private theorem smoothUnlinkNormalPlaneToComplex_sub (v w : UnlinkNormalPlane) :
    unlinkNormalPlaneToComplex (v - w) =
      unlinkNormalPlaneToComplex v - unlinkNormalPlaneToComplex w := by
  apply Complex.ext <;>
    simp [unlinkNormalPlaneToComplex, Complex.equivRealProdCLM_symm_apply]

private theorem unlinkSmoothEighthRadiusDiffeomorph_sub_self_bounds (r : ℝ) :
    0 ≤ unlinkSmoothEighthRadiusDiffeomorph r - r ∧
      unlinkSmoothEighthRadiusDiffeomorph r - r ≤ 1 / 8 := by
  have hstep :
      unlinkSmoothEighthStep (unlinkSmoothEighthRadiusDiffeomorph r) = r + eighth := by
    change unlinkSmoothEighthStep
        (unlinkSmoothEighthStep.symm (r + eighth)) = r + eighth
    exact Diffeomorph.apply_symm_apply _ _
  change smoothUpStep eighth eighth eighth
      (unlinkSmoothEighthRadiusDiffeomorph r) = r + eighth at hstep
  rw [smoothUpStep] at hstep
  have hnonneg := Real.smoothTransition.nonneg
      ((unlinkSmoothEighthRadiusDiffeomorph r - eighth) / eighth)
  have hle := Real.smoothTransition.le_one
      ((unlinkSmoothEighthRadiusDiffeomorph r - eighth) / eighth)
  constructor <;> norm_num [eighth] at hstep hnonneg hle ⊢ <;> linarith

private theorem standardUnlinkNormalProjection_smoothComplementTubeForward
    (i : Fin 2) (q : StandardUnlinkComplementTube i) :
    standardUnlinkNormalProjection (standardUnlinkSmoothComplementTubeForward i q) =
      centeredRadialMap unlinkSmoothEighthRadiusDiffeomorph
        (standardUnlinkNormalCenter i) (standardUnlinkNormalProjection q.1.1) := by
  rw [standardUnlinkSmoothComplementTubeForward,
    standardUnlinkSmoothPuncturedToExteriorEighthTubeDiffeomorph_coe,
    standardUnlinkNormalProjection_openTubeDiffeomorph,
    unlinkSmoothNormalEighthDiskDiffeomorph_apply_coe,
    unlinkSmoothNormalEighthDiffeomorph_apply_coe]
  congr 2

private theorem standardUnlinkRightDisplacementComplex_smoothExteriorForward_of_mem_one
    (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkRightDisplacementComplex
        (standardUnlinkComplementSmoothExteriorDiffeomorph q).1 =
      (unlinkSmoothEighthRadiusDiffeomorph
          ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1‖ /
        ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1‖) •
          standardUnlinkRightDisplacementComplex q.1 := by
  have hne : standardUnlinkNormalProjection q.1 ≠ standardUnlinkNormalCenter 1 := by
    intro h
    apply q.2
    right
    rw [← preimage_singleton_standardUnlinkNormalCenter 1]
    exact h
  rw [standardUnlinkRightDisplacementComplex,
    standardUnlinkComplementSmoothExteriorDiffeomorph_coe,
    standardUnlinkComplementSmoothExteriorForwardRaw_of_mem_one q hq,
    standardUnlinkNormalProjection_smoothComplementTubeForward,
    centeredRadialMap_sub_center unlinkSmoothEighthRadiusDiffeomorph
      (standardUnlinkNormalCenter 1) hne]
  exact smoothUnlinkNormalPlaneToComplex_real_smul _ _

private theorem norm_standardUnlinkNormalProjection_smoothComplementTubeForward_sub
    (i : Fin 2) (q : StandardUnlinkComplementTube i) :
    ‖standardUnlinkNormalProjection (standardUnlinkSmoothComplementTubeForward i q) -
        standardUnlinkNormalProjection q.1.1‖ ≤ 1 / 8 := by
  let v : UnlinkNormalPlane := standardUnlinkNormalProjection q.1.1
  let r : ℝ := ‖v - standardUnlinkNormalCenter i‖
  have hvne : v ≠ standardUnlinkNormalCenter i := by
    intro h
    apply q.1.2
    have hi : q.1.1 ∈ standardUnlinkComponent i := by
      rw [← preimage_singleton_standardUnlinkNormalCenter i]
      exact h
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  have hrpos : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hvne)
  have hrbound := unlinkSmoothEighthRadiusDiffeomorph_sub_self_bounds r
  rw [standardUnlinkNormalProjection_smoothComplementTubeForward,
    centeredRadialMap_of_ne unlinkSmoothEighthRadiusDiffeomorph
      (standardUnlinkNormalCenter i) hvne]
  have hformula : standardUnlinkNormalCenter i +
        (unlinkSmoothEighthRadiusDiffeomorph r / r) •
            (v - standardUnlinkNormalCenter i) - v =
      (unlinkSmoothEighthRadiusDiffeomorph r / r - 1) •
        (v - standardUnlinkNormalCenter i) := by
    module
  rw [hformula, norm_smul, Real.norm_eq_abs,
    show ‖v - standardUnlinkNormalCenter i‖ = r by rfl]
  have hcoef : 0 ≤ unlinkSmoothEighthRadiusDiffeomorph r / r - 1 := by
    rw [sub_nonneg, le_div_iff₀ hrpos]
    linarith [hrbound.1]
  rw [abs_of_nonneg hcoef]
  field_simp
  linarith [hrbound.2]

private theorem
    norm_standardUnlinkRightDisplacementComplex_smoothExteriorForward_sub_of_mem_zero
    (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)) :
    ‖standardUnlinkRightDisplacementComplex
          (standardUnlinkComplementSmoothExteriorDiffeomorph q).1 -
        standardUnlinkRightDisplacementComplex q.1‖ ≤ 1 / 8 := by
  let qt : StandardUnlinkComplementTube 0 := ⟨q, hq⟩
  have hnormal :=
    norm_standardUnlinkNormalProjection_smoothComplementTubeForward_sub 0 qt
  rw [standardUnlinkComplementSmoothExteriorDiffeomorph_coe,
    standardUnlinkComplementSmoothExteriorForwardRaw_of_mem_zero q hq,
    standardUnlinkRightDisplacementComplex]
  change ‖unlinkNormalPlaneToComplex
        (standardUnlinkNormalProjection (standardUnlinkSmoothComplementTubeForward 0 qt) -
          standardUnlinkNormalCenter 1) -
      unlinkNormalPlaneToComplex
        (standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1)‖ ≤ 1 / 8
  rw [← smoothUnlinkNormalPlaneToComplex_sub,
    show standardUnlinkNormalProjection (standardUnlinkSmoothComplementTubeForward 0 qt) -
        standardUnlinkNormalCenter 1 -
          (standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1) =
        standardUnlinkNormalProjection (standardUnlinkSmoothComplementTubeForward 0 qt) -
          standardUnlinkNormalProjection q.1 by abel,
    norm_unlinkNormalPlaneToComplex]
  change ‖standardUnlinkNormalProjection (standardUnlinkSmoothComplementTubeForward 0 qt) -
      standardUnlinkNormalProjection qt.1.1‖ ≤ 1 / 8 at hnormal
  exact hnormal

private theorem fiveEighth_lt_norm_standardUnlinkRightDisplacementComplex_of_mem_zero_smooth
    (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)) :
    5 / 8 < ‖standardUnlinkRightDisplacementComplex q.1‖ := by
  have hqR : dist (standardUnlinkNormalProjection q.1)
      (standardUnlinkNormalCenter 0) < 3 / 8 := hq
  have htriangle : dist (standardUnlinkNormalCenter 0)
      (standardUnlinkNormalCenter 1) ≤
        dist (standardUnlinkNormalCenter 0) (standardUnlinkNormalProjection q.1) +
          dist (standardUnlinkNormalProjection q.1) (standardUnlinkNormalCenter 1) :=
    dist_triangle _ _ _
  rw [dist_standardUnlinkNormalCenter_zero_one] at htriangle
  rw [standardUnlinkRightDisplacementComplex,
    norm_unlinkNormalPlaneToComplex, ← dist_eq_norm]
  rw [dist_comm] at hqR
  linarith

/-! ## The normalized smooth character ratio and its gauge -/

/-- The exact multiplicative change of the right-normal character under the smooth radial base
diffeomorphism. -/
def standardUnlinkComplementSmoothExteriorCharacterRatio
    (q : StandardUnlinkComplement) : ℂ :=
  standardUnlinkRightDisplacementComplex
      (standardUnlinkComplementSmoothExteriorDiffeomorph q).1 /
    standardUnlinkRightDisplacementComplex q.1

theorem continuous_standardUnlinkComplementSmoothExteriorCharacterRatio :
    Continuous standardUnlinkComplementSmoothExteriorCharacterRatio := by
  apply Continuous.div
  · exact continuous_standardUnlinkRightDisplacementComplex.comp
      (continuous_subtype_val.comp
        standardUnlinkComplementSmoothExteriorDiffeomorph.continuous)
  · exact continuous_standardUnlinkRightDisplacementComplex.comp continuous_subtype_val
  · exact fun q ↦ standardUnlinkRightDisplacementComplex_ne_zero q

private theorem standardUnlinkComplementSmoothExteriorCharacterRatio_of_mem_one
    (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkComplementSmoothExteriorCharacterRatio q =
      (unlinkSmoothEighthRadiusDiffeomorph
          ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1‖ /
        ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1‖ : ℝ) := by
  rw [standardUnlinkComplementSmoothExteriorCharacterRatio,
    standardUnlinkRightDisplacementComplex_smoothExteriorForward_of_mem_one q hq,
    Complex.real_smul]
  exact mul_div_cancel_right₀ _ (standardUnlinkRightDisplacementComplex_ne_zero q)

private theorem
    standardUnlinkComplementSmoothExteriorCharacterRatio_mem_slitPlane_of_mem_one
    (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkComplementSmoothExteriorCharacterRatio q ∈ Complex.slitPlane := by
  rw [standardUnlinkComplementSmoothExteriorCharacterRatio_of_mem_one q hq,
    Complex.ofReal_mem_slitPlane]
  have hnorm : 0 <
      ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (by
      intro h
      apply q.2
      right
      rw [← preimage_singleton_standardUnlinkNormalCenter 1]
      exact h))
  exact div_pos
    (lt_trans (by norm_num : (0 : ℝ) < 1 / 8)
      (unlinkSmoothEighthRadiusDiffeomorph_gt_eighth hnorm)) hnorm

private theorem
    standardUnlinkComplementSmoothExteriorCharacterRatio_mem_slitPlane_of_mem_zero
    (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)) :
    standardUnlinkComplementSmoothExteriorCharacterRatio q ∈ Complex.slitPlane := by
  rw [show standardUnlinkComplementSmoothExteriorCharacterRatio q =
      1 + (standardUnlinkComplementSmoothExteriorCharacterRatio q - 1) by ring]
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [standardUnlinkComplementSmoothExteriorCharacterRatio]
  have hdenom : standardUnlinkRightDisplacementComplex q.1 ≠ 0 :=
    standardUnlinkRightDisplacementComplex_ne_zero q
  rw [div_sub_one hdenom, norm_div]
  have hnum :=
    norm_standardUnlinkRightDisplacementComplex_smoothExteriorForward_sub_of_mem_zero q hq
  have hnorm :=
    fiveEighth_lt_norm_standardUnlinkRightDisplacementComplex_of_mem_zero_smooth q hq
  rw [div_lt_one (norm_pos_iff.mpr hdenom)]
  linarith

theorem standardUnlinkComplementSmoothExteriorCharacterRatio_mem_slitPlane
    (q : StandardUnlinkComplement) :
    standardUnlinkComplementSmoothExteriorCharacterRatio q ∈ Complex.slitPlane := by
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · exact
      standardUnlinkComplementSmoothExteriorCharacterRatio_mem_slitPlane_of_mem_zero q h0
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · exact
        standardUnlinkComplementSmoothExteriorCharacterRatio_mem_slitPlane_of_mem_one q h1
    · have hself :
          (standardUnlinkComplementSmoothExteriorDiffeomorph q : Sphere 4) = q.1 := by
        rw [standardUnlinkComplementSmoothExteriorDiffeomorph_coe,
          standardUnlinkComplementSmoothExteriorForwardRaw_of_not_mem q h0 h1]
      rw [standardUnlinkComplementSmoothExteriorCharacterRatio, hself,
        div_self (standardUnlinkRightDisplacementComplex_ne_zero q)]
      exact Complex.one_mem_slitPlane

/-- The principal logarithmic `m`th root of the smooth normalized character ratio. -/
def standardUnlinkComplementSmoothExteriorPowerGauge (m : ℕ)
    (q : StandardUnlinkComplement) : ℂ :=
  Complex.exp
    (Complex.log (standardUnlinkComplementSmoothExteriorCharacterRatio q) / (m : ℂ))

theorem standardUnlinkComplementSmoothExteriorPowerGauge_ne_zero (m : ℕ)
    (q : StandardUnlinkComplement) :
    standardUnlinkComplementSmoothExteriorPowerGauge m q ≠ 0 :=
  Complex.exp_ne_zero _

@[simp]
theorem standardUnlinkComplementSmoothExteriorPowerGauge_pow
    (m : ℕ) [NeZero m] (q : StandardUnlinkComplement) :
    standardUnlinkComplementSmoothExteriorPowerGauge m q ^ m =
      standardUnlinkComplementSmoothExteriorCharacterRatio q := by
  rw [standardUnlinkComplementSmoothExteriorPowerGauge, ← Complex.exp_nat_mul]
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [show (m : ℂ) *
      (Complex.log (standardUnlinkComplementSmoothExteriorCharacterRatio q) / (m : ℂ)) =
        Complex.log (standardUnlinkComplementSmoothExteriorCharacterRatio q) by field_simp]
  exact Complex.exp_log (Complex.slitPlane_ne_zero
    (standardUnlinkComplementSmoothExteriorCharacterRatio_mem_slitPlane q))

theorem continuous_standardUnlinkComplementSmoothExteriorPowerGauge (m : ℕ) :
    Continuous (standardUnlinkComplementSmoothExteriorPowerGauge m) := by
  rw [continuous_iff_continuousAt]
  intro q
  have hlogDiff : ContDiffAt ℂ 1 Complex.log
      (standardUnlinkComplementSmoothExteriorCharacterRatio q) :=
    Complex.contDiffAt_log
      (standardUnlinkComplementSmoothExteriorCharacterRatio_mem_slitPlane q)
  have hlog : ContinuousAt Complex.log
      (standardUnlinkComplementSmoothExteriorCharacterRatio q) :=
    hlogDiff.continuousAt
  have hquot : ContinuousAt
      (fun y : StandardUnlinkComplement ↦
        Complex.log (standardUnlinkComplementSmoothExteriorCharacterRatio y) / (m : ℂ)) q :=
    (hlog.comp
      continuous_standardUnlinkComplementSmoothExteriorCharacterRatio.continuousAt).div_const _
  exact Complex.continuous_exp.continuousAt.comp hquot

theorem standardUnlinkComplementSmoothExteriorPowerGauge_mul_character
    (m : ℕ) [NeZero m] (q : StandardUnlinkComplement) :
    standardUnlinkComplementSmoothExteriorPowerGauge m q ^ m *
        standardUnlinkRightDisplacementComplex q.1 =
      standardUnlinkRightDisplacementComplex
        (standardUnlinkComplementSmoothExteriorDiffeomorph q).1 := by
  rw [standardUnlinkComplementSmoothExteriorPowerGauge_pow,
    standardUnlinkComplementSmoothExteriorCharacterRatio,
    div_mul_cancel₀ _ (standardUnlinkRightDisplacementComplex_ne_zero q)]

theorem standardUnlinkComplementSmoothExteriorPowerGauge_eq_one_of_fixed
    (m : ℕ) (q : StandardUnlinkComplement)
    (hq : (standardUnlinkComplementSmoothExteriorDiffeomorph q : Sphere 4) = q.1) :
    standardUnlinkComplementSmoothExteriorPowerGauge m q = 1 := by
  rw [standardUnlinkComplementSmoothExteriorPowerGauge,
    standardUnlinkComplementSmoothExteriorCharacterRatio, hq,
    div_self (standardUnlinkRightDisplacementComplex_ne_zero q)]
  simp

@[simp]
theorem
    standardUnlinkComplementSmoothExteriorPowerGauge_eq_one_of_not_mem_closedTubes_quarter
    (m : ℕ) (q : StandardUnlinkComplement)
    (hq : q.1 ∉ standardUnlinkClosedTubes (1 / 4 : ℝ)) :
    standardUnlinkComplementSmoothExteriorPowerGauge m q = 1 := by
  apply standardUnlinkComplementSmoothExteriorPowerGauge_eq_one_of_fixed
  exact
    standardUnlinkComplementSmoothExteriorDiffeomorph_eq_self_of_not_mem_closedTubes_quarter
      q hq

theorem standardUnlinkComplementSmoothExteriorPowerGauge_of_mem_one
    (m : ℕ) (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkComplementSmoothExteriorPowerGauge m q =
      Complex.exp
        (Complex.log
          (unlinkSmoothEighthRadiusDiffeomorph
              ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1‖ /
            ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1‖ : ℝ) /
          (m : ℂ)) := by
  rw [standardUnlinkComplementSmoothExteriorPowerGauge,
    standardUnlinkComplementSmoothExteriorCharacterRatio_of_mem_one q hq]

/-! ## The gauge-corrected homeomorphism of power pullbacks -/

/-- Transport a point of the full power cover along the smooth base diffeomorphism, correcting
the power coordinate by the principal logarithmic gauge. -/
def standardUnlinkPowerPullbackToSmoothExterior (m : ℕ) [NeZero m]
    (z : StandardUnlinkPowerPullback m) :
    StandardUnlinkClosedTubeExteriorPowerPullback m := by
  let g := standardUnlinkComplementSmoothExteriorPowerGauge m z.1.1
  refine ⟨(standardUnlinkComplementSmoothExteriorDiffeomorph z.1.1,
    ⟨g * z.1.2.1,
      mul_ne_zero (standardUnlinkComplementSmoothExteriorPowerGauge_ne_zero m z.1.1)
        z.1.2.2⟩), ?_⟩
  apply Subtype.ext
  change standardUnlinkRightDisplacementComplex
      (standardUnlinkComplementSmoothExteriorDiffeomorph z.1.1).1 =
    (g * z.1.2.1) ^ m
  rw [mul_pow]
  have hz : z.1.2.1 ^ m = standardUnlinkRightDisplacementComplex z.1.1.1 := by
    exact (congrArg Subtype.val z.2).symm
  rw [hz]
  exact (standardUnlinkComplementSmoothExteriorPowerGauge_mul_character m z.1.1).symm

/-- Inverse smooth-base transport, dividing by the gauge at the inverse base point. -/
def standardUnlinkSmoothExteriorPowerPullbackToComplement (m : ℕ) [NeZero m]
    (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    StandardUnlinkPowerPullback m := by
  let q := standardUnlinkComplementSmoothExteriorDiffeomorph.symm z.1.1
  let g := standardUnlinkComplementSmoothExteriorPowerGauge m q
  refine ⟨(q, ⟨g⁻¹ * z.1.2.1,
    mul_ne_zero (inv_ne_zero
      (standardUnlinkComplementSmoothExteriorPowerGauge_ne_zero m q)) z.1.2.2⟩), ?_⟩
  apply Subtype.ext
  change standardUnlinkRightDisplacementComplex q.1 =
    (g⁻¹ * z.1.2.1) ^ m
  rw [mul_pow, inv_pow]
  have hz : z.1.2.1 ^ m = standardUnlinkRightDisplacementComplex z.1.1.1 := by
    exact (congrArg Subtype.val z.2).symm
  rw [hz]
  have hg := standardUnlinkComplementSmoothExteriorPowerGauge_mul_character m q
  have hbase :
      (standardUnlinkComplementSmoothExteriorDiffeomorph q : Sphere 4) = z.1.1 := by
    exact congrArg Subtype.val
      (standardUnlinkComplementSmoothExteriorDiffeomorph.apply_symm_apply z.1.1)
  rw [hbase] at hg
  have hg0 : g ^ m ≠ 0 :=
    pow_ne_zero m (standardUnlinkComplementSmoothExteriorPowerGauge_ne_zero m q)
  calc
    standardUnlinkRightDisplacementComplex q.1 =
        (g ^ m)⁻¹ * (g ^ m * standardUnlinkRightDisplacementComplex q.1) := by
      rw [← mul_assoc, inv_mul_cancel₀ hg0, one_mul]
    _ = (g ^ m)⁻¹ * standardUnlinkRightDisplacementComplex z.1.1 := by rw [hg]

@[simp]
theorem standardUnlinkPowerPullbackToSmoothExterior_base
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    (standardUnlinkPowerPullbackToSmoothExterior m z).1.1 =
      standardUnlinkComplementSmoothExteriorDiffeomorph z.1.1 :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackToSmoothExterior_powerCoordinate
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    (standardUnlinkPowerPullbackToSmoothExterior m z).1.2.1 =
      standardUnlinkComplementSmoothExteriorPowerGauge m z.1.1 * z.1.2.1 :=
  rfl

@[simp]
theorem standardUnlinkSmoothExteriorPowerPullbackToComplement_base
    (m : ℕ) [NeZero m]
    (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    (standardUnlinkSmoothExteriorPowerPullbackToComplement m z).1.1 =
      standardUnlinkComplementSmoothExteriorDiffeomorph.symm z.1.1 :=
  rfl

@[simp]
theorem standardUnlinkSmoothExteriorPowerPullbackToComplement_powerCoordinate
    (m : ℕ) [NeZero m]
    (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    (standardUnlinkSmoothExteriorPowerPullbackToComplement m z).1.2.1 =
      (standardUnlinkComplementSmoothExteriorPowerGauge m
        (standardUnlinkComplementSmoothExteriorDiffeomorph.symm z.1.1))⁻¹ * z.1.2.1 :=
  rfl

theorem continuous_standardUnlinkPowerPullbackToSmoothExterior
    (m : ℕ) [NeZero m] :
    Continuous (standardUnlinkPowerPullbackToSmoothExterior m) := by
  apply Continuous.subtype_mk
  exact (standardUnlinkComplementSmoothExteriorDiffeomorph.continuous.comp
    (continuous_fst.comp continuous_subtype_val)).prodMk <|
      ((continuous_standardUnlinkComplementSmoothExteriorPowerGauge m).comp
          (continuous_fst.comp continuous_subtype_val) |>.mul
        (continuous_subtype_val.comp
          (continuous_snd.comp continuous_subtype_val))).subtype_mk _

theorem continuous_standardUnlinkSmoothExteriorPowerPullbackToComplement
    (m : ℕ) [NeZero m] :
    Continuous (standardUnlinkSmoothExteriorPowerPullbackToComplement m) := by
  apply Continuous.subtype_mk
  exact (standardUnlinkComplementSmoothExteriorDiffeomorph.symm.continuous.comp
    (continuous_fst.comp continuous_subtype_val)).prodMk <|
      (((continuous_standardUnlinkComplementSmoothExteriorPowerGauge m).comp
          (standardUnlinkComplementSmoothExteriorDiffeomorph.symm.continuous.comp
            (continuous_fst.comp continuous_subtype_val))).inv₀
          (fun z ↦ standardUnlinkComplementSmoothExteriorPowerGauge_ne_zero m
            (standardUnlinkComplementSmoothExteriorDiffeomorph.symm z.1.1)) |>.mul
        (continuous_subtype_val.comp
          (continuous_snd.comp continuous_subtype_val))).subtype_mk _

/-- The gauge-corrected homeomorphism of the two literal power pullbacks. -/
def standardUnlinkPowerPullbackSmoothExteriorHomeomorph
    (m : ℕ) [NeZero m] :
    StandardUnlinkPowerPullback m ≃ₜ
      StandardUnlinkClosedTubeExteriorPowerPullback m where
  toFun := standardUnlinkPowerPullbackToSmoothExterior m
  invFun := standardUnlinkSmoothExteriorPowerPullbackToComplement m
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact standardUnlinkComplementSmoothExteriorDiffeomorph.symm_apply_apply z.1.1
    · apply Subtype.ext
      rw [standardUnlinkSmoothExteriorPowerPullbackToComplement_powerCoordinate,
        standardUnlinkPowerPullbackToSmoothExterior_base,
        standardUnlinkComplementSmoothExteriorDiffeomorph.symm_apply_apply,
        standardUnlinkPowerPullbackToSmoothExterior_powerCoordinate,
        inv_mul_cancel_left₀
          (standardUnlinkComplementSmoothExteriorPowerGauge_ne_zero m z.1.1)]
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact standardUnlinkComplementSmoothExteriorDiffeomorph.apply_symm_apply z.1.1
    · apply Subtype.ext
      change standardUnlinkComplementSmoothExteriorPowerGauge m
          (standardUnlinkComplementSmoothExteriorDiffeomorph.symm z.1.1) *
            ((standardUnlinkComplementSmoothExteriorPowerGauge m
              (standardUnlinkComplementSmoothExteriorDiffeomorph.symm z.1.1))⁻¹ * z.1.2.1) =
        z.1.2.1
      rw [← mul_assoc, mul_inv_cancel₀
        (standardUnlinkComplementSmoothExteriorPowerGauge_ne_zero m
          (standardUnlinkComplementSmoothExteriorDiffeomorph.symm z.1.1)), one_mul]
  continuous_toFun := continuous_standardUnlinkPowerPullbackToSmoothExterior m
  continuous_invFun := continuous_standardUnlinkSmoothExteriorPowerPullbackToComplement m

@[simp]
theorem standardUnlinkPowerPullbackSmoothExteriorHomeomorph_proj
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    standardUnlinkClosedTubeExteriorPowerPullbackProj m
        (standardUnlinkPowerPullbackSmoothExteriorHomeomorph m z) =
      standardUnlinkComplementSmoothExteriorDiffeomorph
        (standardUnlinkPowerPullbackProj m z) :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackSmoothExteriorHomeomorph_apply_base
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    (standardUnlinkPowerPullbackSmoothExteriorHomeomorph m z).1.1 =
      standardUnlinkComplementSmoothExteriorDiffeomorph z.1.1 :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackSmoothExteriorHomeomorph_apply_powerCoordinate
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    (standardUnlinkPowerPullbackSmoothExteriorHomeomorph m z).1.2.1 =
      standardUnlinkComplementSmoothExteriorPowerGauge m z.1.1 * z.1.2.1 :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackSmoothExteriorHomeomorph_symm_proj
    (m : ℕ) [NeZero m]
    (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    standardUnlinkPowerPullbackProj m
        ((standardUnlinkPowerPullbackSmoothExteriorHomeomorph m).symm z) =
      standardUnlinkComplementSmoothExteriorDiffeomorph.symm
        (standardUnlinkClosedTubeExteriorPowerPullbackProj m z) :=
  rfl

/-! ## Smoothness reflected through the covering projections -/

/-- The gauge-corrected transport is a genuine diffeomorphism for the explicit smooth atlases
pulled back along the source and target covering projections. -/
def standardUnlinkPowerPullbackSmoothExteriorDiffeomorph
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
    StandardUnlinkPowerPullback m ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯
      StandardUnlinkClosedTubeExteriorPowerPullback m := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkPowerPullback m) :=
    standardUnlinkPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
    isManifold_standardUnlinkPowerPullback m
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
    standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
  let _ : IsManifold (𝓡 4) ∞
      (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
    isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
  exact diffeomorphOfHomeomorphOverDiffeomorph
    (𝓡 4) (𝓡 4)
    (standardUnlinkPowerPullbackProj m)
    (standardUnlinkClosedTubeExteriorPowerPullbackProj m)
    (smoothCover_standardUnlinkPowerPullbackProj m).isLocalDiffeomorph
    (smoothCover_standardUnlinkClosedTubeExteriorPowerPullbackProj m).isLocalDiffeomorph
    standardUnlinkComplementSmoothExteriorDiffeomorph
    (standardUnlinkPowerPullbackSmoothExteriorHomeomorph m)
    (fun _ ↦ rfl)

/-- Forgetting smoothness recovers the gauge-corrected homeomorphism exactly. -/
@[simp]
theorem standardUnlinkPowerPullbackSmoothExteriorDiffeomorph_toHomeomorph
    (m : ℕ) [NeZero m] :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
    (standardUnlinkPowerPullbackSmoothExteriorDiffeomorph m).toHomeomorph =
      standardUnlinkPowerPullbackSmoothExteriorHomeomorph m :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackSmoothExteriorDiffeomorph_apply
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
    standardUnlinkPowerPullbackSmoothExteriorDiffeomorph m z =
      standardUnlinkPowerPullbackSmoothExteriorHomeomorph m z :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackSmoothExteriorDiffeomorph_symm_apply
    (m : ℕ) [NeZero m]
    (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
    (standardUnlinkPowerPullbackSmoothExteriorDiffeomorph m).symm z =
      (standardUnlinkPowerPullbackSmoothExteriorHomeomorph m).symm z :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackSmoothExteriorDiffeomorph_proj
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
    standardUnlinkClosedTubeExteriorPowerPullbackProj m
        (standardUnlinkPowerPullbackSmoothExteriorDiffeomorph m z) =
      standardUnlinkComplementSmoothExteriorDiffeomorph
        (standardUnlinkPowerPullbackProj m z) :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackSmoothExteriorDiffeomorph_apply_base
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
    (standardUnlinkPowerPullbackSmoothExteriorDiffeomorph m z).1.1 =
      standardUnlinkComplementSmoothExteriorDiffeomorph z.1.1 :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackSmoothExteriorDiffeomorph_apply_powerCoordinate
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
    (standardUnlinkPowerPullbackSmoothExteriorDiffeomorph m z).1.2.1 =
      standardUnlinkComplementSmoothExteriorPowerGauge m z.1.1 * z.1.2.1 :=
  rfl

/-! ## Deck equivariance and exact equatorial lifts -/

theorem standardUnlinkPowerPullbackSmoothExteriorDiffeomorph_deck_equivariant
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ)
    (z : StandardUnlinkPowerPullback m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
    standardUnlinkPowerPullbackSmoothExteriorDiffeomorph m (u • z) =
      standardUnlinkClosedTubeExteriorPowerDeckMap m u
        (standardUnlinkPowerPullbackSmoothExteriorDiffeomorph m z) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change standardUnlinkComplementSmoothExteriorPowerGauge m z.1.1 *
        (((u.1 : ℂˣ) : ℂ) * z.1.2.1) =
      ((u.1 : ℂˣ) : ℂ) *
        (standardUnlinkComplementSmoothExteriorPowerGauge m z.1.1 * z.1.2.1)
    ring

@[simp]
theorem standardUnlinkComplementSmoothExteriorPowerGauge_equator
    (m : ℕ) (x : Sphere 3) :
    standardUnlinkComplementSmoothExteriorPowerGauge m
        (equatorUnlinkComplementMap x) = 1 := by
  apply standardUnlinkComplementSmoothExteriorPowerGauge_eq_one_of_fixed
  exact congrArg Subtype.val
    (standardUnlinkComplementSmoothExteriorDiffeomorph_equator x)

theorem
    standardUnlinkPowerPullbackSmoothExteriorDiffeomorph_equatorUnlinkPowerLift
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
    standardUnlinkPowerPullbackSmoothExteriorDiffeomorph m
        (equatorUnlinkPowerLift m a x) =
      equatorUnlinkClosedTubeExteriorPowerLift m a x := by
  apply Subtype.ext
  apply Prod.ext
  · exact standardUnlinkComplementSmoothExteriorDiffeomorph_equator x
  · apply Subtype.ext
    change standardUnlinkComplementSmoothExteriorPowerGauge m
        (equatorUnlinkComplementMap x) * equatorUnlinkPowerRootTranslate m a x =
      equatorUnlinkPowerRootTranslate m a x
    rw [standardUnlinkComplementSmoothExteriorPowerGauge_equator, one_mul]

theorem
    standardUnlinkPowerPullbackSmoothExteriorDiffeomorph_equatorUnlinkPowerLift_range
    (m : ℕ) [NeZero m] (a : ZMod m) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkPowerPullback m) :=
      standardUnlinkPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞ (StandardUnlinkPowerPullback m) :=
      isManifold_standardUnlinkPowerPullback m
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      standardUnlinkClosedTubeExteriorPowerPullbackChartedSpace m
    letI : IsManifold (𝓡 4) ∞
        (StandardUnlinkClosedTubeExteriorPowerPullback m) :=
      isManifold_standardUnlinkClosedTubeExteriorPowerPullback m
    standardUnlinkPowerPullbackSmoothExteriorDiffeomorph m ''
        range (equatorUnlinkPowerLift m a) =
      range (equatorUnlinkClosedTubeExteriorPowerLift m a) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x,
      (standardUnlinkPowerPullbackSmoothExteriorDiffeomorph_equatorUnlinkPowerLift
        m a x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨equatorUnlinkPowerLift m a x, ⟨x, rfl⟩,
      standardUnlinkPowerPullbackSmoothExteriorDiffeomorph_equatorUnlinkPowerLift
        m a x⟩

end SplittingSpheres
