/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import SplittingSpheres.Geometry.UnlinkComplementExteriorHomeomorph
public import SplittingSpheres.Geometry.UnlinkEquatorPowerLift
public import SplittingSpheres.Geometry.UnlinkExteriorPowerCover
public import SplittingSpheres.Geometry.UnlinkExteriorPowerDeck
public import SplittingSpheres.Geometry.UnlinkMeridianCharacter
public import SplittingSpheres.Geometry.UnlinkPowerDeck

/-!
# Transporting the unlink power cover to the open tubular exterior

The radial homeomorphism from the strict unlink complement to the open interior of the
radius-`1/8` exterior does not preserve the chosen right-normal character.  This file first
records the canonical pullback obtained by transporting that character with the inverse base
homeomorphism, and then compares it with the literal exterior character.

The comparison with the literal right-normal character on the exterior requires a gauge.  In
the right tube the gauge is an `m`th root of the positive radial multiplier.  In the left tube
the multiplier is not real: radial motion about the left component changes the argument of the
right-normal character.  The normalized ratio nevertheless lies in the principal slit plane.
Its logarithmic `m`th root supplies an exact continuous gauge, producing a deck-equivariant
homeomorphism to the literal exterior pullback.  The final section identifies that pullback with
the exact strict-base inverse image inside the compact coordinate-exterior pullback and proves
that all explicit equatorial lifts are fixed by the gauge.
-/

@[expose] public section

noncomputable section

open Function Metric Set Topology
open TopologicalSpace

namespace SplittingSpheres

private theorem unlinkNormalPlaneToComplex_real_smul (c : ℝ)
    (v : UnlinkNormalPlane) :
    unlinkNormalPlaneToComplex (c • v) = c • unlinkNormalPlaneToComplex v := by
  apply Complex.ext <;>
    simp [unlinkNormalPlaneToComplex, Complex.equivRealProdCLM_symm_apply]

private theorem unlinkNormalPlaneToComplex_sub (v w : UnlinkNormalPlane) :
    unlinkNormalPlaneToComplex (v - w) =
      unlinkNormalPlaneToComplex v - unlinkNormalPlaneToComplex w := by
  apply Complex.ext <;>
    simp [unlinkNormalPlaneToComplex, Complex.equivRealProdCLM_symm_apply]

private theorem standardUnlinkNormalProjection_complementTubeForward
    (i : Fin 2) (q : StandardUnlinkComplementTube i) :
    standardUnlinkNormalProjection (standardUnlinkComplementTubeForward i q) =
      centeredRadialMap unlinkEighthRadiusForward
        (standardUnlinkNormalCenter i) (standardUnlinkNormalProjection q.1.1) := by
  rw [standardUnlinkComplementTubeForward,
    standardUnlinkPuncturedToExteriorEighthTubeHomeomorph_coe,
    standardUnlinkNormalProjection_openTubeHomeomorph]
  rfl

private theorem standardUnlinkRightDisplacementComplex_exteriorForward_of_mem_one
    (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkRightDisplacementComplex
        (standardUnlinkComplementExteriorHomeomorph q).1 =
      (unlinkEighthRadiusForward
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
    standardUnlinkComplementExteriorHomeomorph_coe,
    standardUnlinkComplementExteriorForwardRaw_of_mem_one q hq,
    standardUnlinkNormalProjection_complementTubeForward,
    centeredRadialMap_sub_center unlinkEighthRadiusForward
      (standardUnlinkNormalCenter 1) hne]
  exact unlinkNormalPlaneToComplex_real_smul _ _

private theorem norm_standardUnlinkNormalProjection_complementTubeForward_sub
    (i : Fin 2) (q : StandardUnlinkComplementTube i) :
    ‖standardUnlinkNormalProjection (standardUnlinkComplementTubeForward i q) -
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
  rw [standardUnlinkNormalProjection_complementTubeForward]
  by_cases hr : r ≤ 1 / 4
  · rw [centeredRadialMap_of_ne unlinkEighthRadiusForward
      (standardUnlinkNormalCenter i) hvne,
      unlinkEighthRadiusForward_of_le hr]
    have hformula : standardUnlinkNormalCenter i +
          ((1 / 8 + r / 2) / r) • (v - standardUnlinkNormalCenter i) - v =
        (((1 / 8 + r / 2) / r) - 1) •
          (v - standardUnlinkNormalCenter i) := by
      module
    rw [hformula, norm_smul, Real.norm_eq_abs, show ‖v - standardUnlinkNormalCenter i‖ = r by rfl]
    have hcoef : 0 ≤ (1 / 8 + r / 2) / r - 1 := by
      rw [sub_nonneg, le_div_iff₀ hrpos]
      linarith
    rw [abs_of_nonneg hcoef]
    field_simp
    linarith
  · have hge : 1 / 4 ≤ r := le_of_not_ge hr
    rw [centeredRadialMap_eq_self_of_radius_eq unlinkEighthRadiusForward
      (standardUnlinkNormalCenter i)
      (unlinkEighthRadiusForward_of_ge hge), sub_self, norm_zero]
    norm_num

private theorem norm_standardUnlinkRightDisplacementComplex_exteriorForward_sub_of_mem_zero
    (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)) :
    ‖standardUnlinkRightDisplacementComplex
          (standardUnlinkComplementExteriorHomeomorph q).1 -
        standardUnlinkRightDisplacementComplex q.1‖ ≤ 1 / 8 := by
  let qt : StandardUnlinkComplementTube 0 := ⟨q, hq⟩
  have hnormal :=
    norm_standardUnlinkNormalProjection_complementTubeForward_sub 0 qt
  rw [standardUnlinkComplementExteriorHomeomorph_coe,
    standardUnlinkComplementExteriorForwardRaw_of_mem_zero q hq,
    standardUnlinkRightDisplacementComplex]
  change ‖unlinkNormalPlaneToComplex
        (standardUnlinkNormalProjection (standardUnlinkComplementTubeForward 0 qt) -
          standardUnlinkNormalCenter 1) -
      unlinkNormalPlaneToComplex
        (standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1)‖ ≤ 1 / 8
  rw [← unlinkNormalPlaneToComplex_sub,
    show standardUnlinkNormalProjection (standardUnlinkComplementTubeForward 0 qt) -
        standardUnlinkNormalCenter 1 -
          (standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1) =
        standardUnlinkNormalProjection (standardUnlinkComplementTubeForward 0 qt) -
          standardUnlinkNormalProjection q.1 by abel,
    norm_unlinkNormalPlaneToComplex]
  change ‖standardUnlinkNormalProjection (standardUnlinkComplementTubeForward 0 qt) -
      standardUnlinkNormalProjection qt.1.1‖ ≤ 1 / 8 at hnormal
  exact hnormal

private theorem fiveEighth_lt_norm_standardUnlinkRightDisplacementComplex_of_mem_zero
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

/-! ## The normalized character ratio -/

/-- The exact multiplicative change of the right-normal character under the radial base
homeomorphism. -/
def standardUnlinkComplementExteriorCharacterRatio
    (q : StandardUnlinkComplement) : ℂ :=
  standardUnlinkRightDisplacementComplex
      (standardUnlinkComplementExteriorHomeomorph q).1 /
    standardUnlinkRightDisplacementComplex q.1

theorem continuous_standardUnlinkComplementExteriorCharacterRatio :
    Continuous standardUnlinkComplementExteriorCharacterRatio := by
  apply Continuous.div
  · exact continuous_standardUnlinkRightDisplacementComplex.comp
      (continuous_subtype_val.comp
        standardUnlinkComplementExteriorHomeomorph.continuous)
  · exact continuous_standardUnlinkRightDisplacementComplex.comp continuous_subtype_val
  · exact fun q ↦ standardUnlinkRightDisplacementComplex_ne_zero q

private theorem standardUnlinkComplementExteriorCharacterRatio_of_mem_one
    (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkComplementExteriorCharacterRatio q =
      (unlinkEighthRadiusForward
          ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1‖ /
        ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1‖ : ℝ) := by
  rw [standardUnlinkComplementExteriorCharacterRatio,
    standardUnlinkRightDisplacementComplex_exteriorForward_of_mem_one q hq,
    Complex.real_smul]
  exact mul_div_cancel_right₀ _ (standardUnlinkRightDisplacementComplex_ne_zero q)

private theorem standardUnlinkComplementExteriorCharacterRatio_mem_slitPlane_of_mem_one
    (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkComplementExteriorCharacterRatio q ∈ Complex.slitPlane := by
  rw [standardUnlinkComplementExteriorCharacterRatio_of_mem_one q hq,
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
      (unlinkEighthRadiusForward_gt_eighth hnorm)) hnorm

private theorem standardUnlinkComplementExteriorCharacterRatio_mem_slitPlane_of_mem_zero
    (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)) :
    standardUnlinkComplementExteriorCharacterRatio q ∈ Complex.slitPlane := by
  rw [show standardUnlinkComplementExteriorCharacterRatio q =
      1 + (standardUnlinkComplementExteriorCharacterRatio q - 1) by ring]
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [standardUnlinkComplementExteriorCharacterRatio]
  have hdenom : standardUnlinkRightDisplacementComplex q.1 ≠ 0 :=
    standardUnlinkRightDisplacementComplex_ne_zero q
  rw [div_sub_one hdenom, norm_div]
  have hnum :=
    norm_standardUnlinkRightDisplacementComplex_exteriorForward_sub_of_mem_zero q hq
  have hnorm :=
    fiveEighth_lt_norm_standardUnlinkRightDisplacementComplex_of_mem_zero q hq
  rw [div_lt_one (norm_pos_iff.mpr hdenom)]
  linarith

theorem standardUnlinkComplementExteriorCharacterRatio_mem_slitPlane
    (q : StandardUnlinkComplement) :
    standardUnlinkComplementExteriorCharacterRatio q ∈ Complex.slitPlane := by
  classical
  by_cases h0 : q.1 ∈ standardUnlinkOpenTube 0 (3 / 8 : ℝ)
  · exact standardUnlinkComplementExteriorCharacterRatio_mem_slitPlane_of_mem_zero q h0
  · by_cases h1 : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)
    · exact standardUnlinkComplementExteriorCharacterRatio_mem_slitPlane_of_mem_one q h1
    · have hself : (standardUnlinkComplementExteriorHomeomorph q : Sphere 4) = q.1 := by
        rw [standardUnlinkComplementExteriorHomeomorph_coe,
          standardUnlinkComplementExteriorForwardRaw_of_not_mem q h0 h1]
      rw [standardUnlinkComplementExteriorCharacterRatio, hself,
        div_self (standardUnlinkRightDisplacementComplex_ne_zero q)]
      exact Complex.one_mem_slitPlane

/-- The principal logarithmic `m`th root of the normalized character ratio. -/
def standardUnlinkComplementExteriorPowerGauge (m : ℕ)
    (q : StandardUnlinkComplement) : ℂ :=
  Complex.exp
    (Complex.log (standardUnlinkComplementExteriorCharacterRatio q) / (m : ℂ))

theorem standardUnlinkComplementExteriorPowerGauge_ne_zero (m : ℕ)
    (q : StandardUnlinkComplement) :
    standardUnlinkComplementExteriorPowerGauge m q ≠ 0 :=
  Complex.exp_ne_zero _

@[simp]
theorem standardUnlinkComplementExteriorPowerGauge_pow
    (m : ℕ) [NeZero m] (q : StandardUnlinkComplement) :
    standardUnlinkComplementExteriorPowerGauge m q ^ m =
      standardUnlinkComplementExteriorCharacterRatio q := by
  rw [standardUnlinkComplementExteriorPowerGauge, ← Complex.exp_nat_mul]
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [show (m : ℂ) *
      (Complex.log (standardUnlinkComplementExteriorCharacterRatio q) / (m : ℂ)) =
        Complex.log (standardUnlinkComplementExteriorCharacterRatio q) by field_simp]
  exact Complex.exp_log (Complex.slitPlane_ne_zero
    (standardUnlinkComplementExteriorCharacterRatio_mem_slitPlane q))

theorem continuous_standardUnlinkComplementExteriorPowerGauge (m : ℕ) :
    Continuous (standardUnlinkComplementExteriorPowerGauge m) := by
  rw [continuous_iff_continuousAt]
  intro q
  have hlogDiff : ContDiffAt ℂ 1 Complex.log
      (standardUnlinkComplementExteriorCharacterRatio q) :=
    Complex.contDiffAt_log
      (standardUnlinkComplementExteriorCharacterRatio_mem_slitPlane q)
  have hlog : ContinuousAt Complex.log
      (standardUnlinkComplementExteriorCharacterRatio q) :=
    hlogDiff.continuousAt
  have hquot : ContinuousAt
      (fun y : StandardUnlinkComplement ↦
        Complex.log (standardUnlinkComplementExteriorCharacterRatio y) / (m : ℂ)) q :=
    (hlog.comp
      continuous_standardUnlinkComplementExteriorCharacterRatio.continuousAt).div_const _
  exact Complex.continuous_exp.continuousAt.comp hquot

theorem standardUnlinkComplementExteriorPowerGauge_mul_character
    (m : ℕ) [NeZero m] (q : StandardUnlinkComplement) :
    standardUnlinkComplementExteriorPowerGauge m q ^ m *
        standardUnlinkRightDisplacementComplex q.1 =
      standardUnlinkRightDisplacementComplex
        (standardUnlinkComplementExteriorHomeomorph q).1 := by
  rw [standardUnlinkComplementExteriorPowerGauge_pow,
    standardUnlinkComplementExteriorCharacterRatio,
    div_mul_cancel₀ _ (standardUnlinkRightDisplacementComplex_ne_zero q)]

theorem standardUnlinkComplementExteriorPowerGauge_eq_one_of_fixed
    (m : ℕ) (q : StandardUnlinkComplement)
    (hq : (standardUnlinkComplementExteriorHomeomorph q : Sphere 4) = q.1) :
    standardUnlinkComplementExteriorPowerGauge m q = 1 := by
  rw [standardUnlinkComplementExteriorPowerGauge,
    standardUnlinkComplementExteriorCharacterRatio, hq,
    div_self (standardUnlinkRightDisplacementComplex_ne_zero q)]
  simp

theorem standardUnlinkComplementExteriorPowerGauge_of_mem_one
    (m : ℕ) (q : StandardUnlinkComplement)
    (hq : q.1 ∈ standardUnlinkOpenTube 1 (3 / 8 : ℝ)) :
    standardUnlinkComplementExteriorPowerGauge m q =
      Complex.exp
        (Complex.log
          (unlinkEighthRadiusForward
              ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1‖ /
            ‖standardUnlinkNormalProjection q.1 - standardUnlinkNormalCenter 1‖ : ℝ) /
          (m : ℂ)) := by
  rw [standardUnlinkComplementExteriorPowerGauge,
    standardUnlinkComplementExteriorCharacterRatio_of_mem_one q hq]

/-! ## The literal and transported characters on the open exterior -/

/-- Inclusion of the strict closed-tube exterior in the strict unlink complement. -/
def standardUnlinkClosedTubeExteriorToComplement
    (q : StandardUnlinkClosedTubeExterior) : StandardUnlinkComplement := by
  refine ⟨q.1, ?_⟩
  intro hq
  rcases hq with hq | hq
  · have hclosed : q.1 ∈ standardUnlinkClosedTube 0 (1 / 8 : ℝ) :=
      standardUnlinkOpenTube_subset_closedTube 0 (1 / 8 : ℝ)
        (standardUnlinkComponent_subset_openTube 0 (by norm_num) hq)
    exact q.2 (Or.inl hclosed)
  · have hclosed : q.1 ∈ standardUnlinkClosedTube 1 (1 / 8 : ℝ) :=
      standardUnlinkOpenTube_subset_closedTube 1 (1 / 8 : ℝ)
        (standardUnlinkComponent_subset_openTube 1 (by norm_num) hq)
    exact q.2 (Or.inr hclosed)

@[simp]
theorem standardUnlinkClosedTubeExteriorToComplement_coe
    (q : StandardUnlinkClosedTubeExterior) :
    (standardUnlinkClosedTubeExteriorToComplement q : Sphere 4) = q.1 :=
  rfl

theorem continuous_standardUnlinkClosedTubeExteriorToComplement :
    Continuous standardUnlinkClosedTubeExteriorToComplement :=
  continuous_subtype_val.subtype_mk _

/-- The literal right-normal character on the strict closed-tube exterior. -/
def standardUnlinkClosedTubeExteriorRightNormalMap :
    StandardUnlinkClosedTubeExterior → {z : ℂ // z ≠ 0} :=
  standardUnlinkRightNormalMap ∘ standardUnlinkClosedTubeExteriorToComplement

@[simp]
theorem standardUnlinkClosedTubeExteriorRightNormalMap_coe
    (q : StandardUnlinkClosedTubeExterior) :
    (standardUnlinkClosedTubeExteriorRightNormalMap q : ℂ) =
      standardUnlinkRightDisplacementComplex q.1 :=
  rfl

theorem continuous_standardUnlinkClosedTubeExteriorRightNormalMap :
    Continuous standardUnlinkClosedTubeExteriorRightNormalMap :=
  continuous_standardUnlinkRightNormalMap.comp
    continuous_standardUnlinkClosedTubeExteriorToComplement

/-- The literal power pullback over the strict closed-tube exterior. -/
abbrev StandardUnlinkClosedTubeExteriorPowerPullback (m : ℕ) :=
  TopologicalCoverPullback (nonzeroComplexPow m)
    standardUnlinkClosedTubeExteriorRightNormalMap

/-- Projection of the literal exterior power pullback. -/
def standardUnlinkClosedTubeExteriorPowerPullbackProj (m : ℕ) :
    StandardUnlinkClosedTubeExteriorPowerPullback m →
      StandardUnlinkClosedTubeExterior :=
  topologicalCoverPullbackProj (nonzeroComplexPow m)
    standardUnlinkClosedTubeExteriorRightNormalMap

@[simp]
theorem standardUnlinkClosedTubeExteriorPowerPullbackProj_apply
    (m : ℕ) (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    standardUnlinkClosedTubeExteriorPowerPullbackProj m z = z.1.1 :=
  rfl

/-- The right-normal character transported to the exterior by the inverse radial
homeomorphism. -/
def standardUnlinkClosedTubeExteriorTransportedRightNormalMap :
    StandardUnlinkClosedTubeExterior → {z : ℂ // z ≠ 0} :=
  standardUnlinkRightNormalMap ∘ standardUnlinkComplementExteriorHomeomorph.symm

@[simp]
theorem standardUnlinkClosedTubeExteriorTransportedRightNormalMap_apply
    (q : StandardUnlinkClosedTubeExterior) :
    standardUnlinkClosedTubeExteriorTransportedRightNormalMap q =
      standardUnlinkRightNormalMap
        (standardUnlinkComplementExteriorHomeomorph.symm q) :=
  rfl

theorem continuous_standardUnlinkClosedTubeExteriorTransportedRightNormalMap :
    Continuous standardUnlinkClosedTubeExteriorTransportedRightNormalMap :=
  continuous_standardUnlinkRightNormalMap.comp
    standardUnlinkComplementExteriorHomeomorph.symm.continuous

/-- The power pullback over the exterior for the transported character. -/
abbrev StandardUnlinkClosedTubeExteriorTransportedPowerPullback (m : ℕ) :=
  TopologicalCoverPullback (nonzeroComplexPow m)
    standardUnlinkClosedTubeExteriorTransportedRightNormalMap

/-- Projection of the transported power pullback. -/
def standardUnlinkClosedTubeExteriorTransportedPowerPullbackProj (m : ℕ) :
    StandardUnlinkClosedTubeExteriorTransportedPowerPullback m →
      StandardUnlinkClosedTubeExterior :=
  topologicalCoverPullbackProj (nonzeroComplexPow m)
    standardUnlinkClosedTubeExteriorTransportedRightNormalMap

@[simp]
theorem standardUnlinkClosedTubeExteriorTransportedPowerPullbackProj_apply
    (m : ℕ) (z : StandardUnlinkClosedTubeExteriorTransportedPowerPullback m) :
    standardUnlinkClosedTubeExteriorTransportedPowerPullbackProj m z = z.1.1 :=
  rfl

/-! ## Canonical transport of the full power pullback -/

/-- Change only the base coordinate by the radial exterior homeomorphism. -/
def standardUnlinkPowerPullbackToExteriorTransported (m : ℕ)
    (z : StandardUnlinkPowerPullback m) :
    StandardUnlinkClosedTubeExteriorTransportedPowerPullback m := by
  refine ⟨(standardUnlinkComplementExteriorHomeomorph z.1.1, z.1.2), ?_⟩
  change standardUnlinkRightNormalMap
      (standardUnlinkComplementExteriorHomeomorph.symm
        (standardUnlinkComplementExteriorHomeomorph z.1.1)) =
    nonzeroComplexPow m z.1.2
  rw [standardUnlinkComplementExteriorHomeomorph.symm_apply_apply]
  exact z.2

/-- Inverse change of the base coordinate. -/
def standardUnlinkExteriorTransportedPowerPullbackToComplement (m : ℕ)
    (z : StandardUnlinkClosedTubeExteriorTransportedPowerPullback m) :
    StandardUnlinkPowerPullback m := by
  refine ⟨(standardUnlinkComplementExteriorHomeomorph.symm z.1.1, z.1.2), ?_⟩
  exact z.2

@[simp]
theorem standardUnlinkPowerPullbackToExteriorTransported_base (m : ℕ)
    (z : StandardUnlinkPowerPullback m) :
    (standardUnlinkPowerPullbackToExteriorTransported m z).1.1 =
      standardUnlinkComplementExteriorHomeomorph z.1.1 :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackToExteriorTransported_powerCoordinate (m : ℕ)
    (z : StandardUnlinkPowerPullback m) :
    (standardUnlinkPowerPullbackToExteriorTransported m z).1.2 = z.1.2 :=
  rfl

@[simp]
theorem standardUnlinkExteriorTransportedPowerPullbackToComplement_base (m : ℕ)
    (z : StandardUnlinkClosedTubeExteriorTransportedPowerPullback m) :
    (standardUnlinkExteriorTransportedPowerPullbackToComplement m z).1.1 =
      standardUnlinkComplementExteriorHomeomorph.symm z.1.1 :=
  rfl

@[simp]
theorem standardUnlinkExteriorTransportedPowerPullbackToComplement_powerCoordinate
    (m : ℕ) (z : StandardUnlinkClosedTubeExteriorTransportedPowerPullback m) :
    (standardUnlinkExteriorTransportedPowerPullbackToComplement m z).1.2 = z.1.2 :=
  rfl

theorem continuous_standardUnlinkPowerPullbackToExteriorTransported (m : ℕ) :
    Continuous (standardUnlinkPowerPullbackToExteriorTransported m) := by
  apply Continuous.subtype_mk
  exact (standardUnlinkComplementExteriorHomeomorph.continuous.comp
    (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)

theorem continuous_standardUnlinkExteriorTransportedPowerPullbackToComplement (m : ℕ) :
    Continuous (standardUnlinkExteriorTransportedPowerPullbackToComplement m) := by
  apply Continuous.subtype_mk
  exact (standardUnlinkComplementExteriorHomeomorph.symm.continuous.comp
    (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)

/-- The full power pullback is canonically homeomorphic to the exterior pullback of the
transported character. -/
def standardUnlinkPowerPullbackExteriorTransportedHomeomorph (m : ℕ) :
    StandardUnlinkPowerPullback m ≃ₜ
      StandardUnlinkClosedTubeExteriorTransportedPowerPullback m where
  toFun := standardUnlinkPowerPullbackToExteriorTransported m
  invFun := standardUnlinkExteriorTransportedPowerPullbackToComplement m
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact standardUnlinkComplementExteriorHomeomorph.symm_apply_apply z.1.1
    · rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact standardUnlinkComplementExteriorHomeomorph.apply_symm_apply z.1.1
    · rfl
  continuous_toFun := continuous_standardUnlinkPowerPullbackToExteriorTransported m
  continuous_invFun :=
    continuous_standardUnlinkExteriorTransportedPowerPullbackToComplement m

@[simp]
theorem standardUnlinkPowerPullbackExteriorTransportedHomeomorph_apply_base
    (m : ℕ) (z : StandardUnlinkPowerPullback m) :
    (standardUnlinkPowerPullbackExteriorTransportedHomeomorph m z).1.1 =
      standardUnlinkComplementExteriorHomeomorph z.1.1 :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackExteriorTransportedHomeomorph_apply_powerCoordinate
    (m : ℕ) (z : StandardUnlinkPowerPullback m) :
    (standardUnlinkPowerPullbackExteriorTransportedHomeomorph m z).1.2 = z.1.2 :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackExteriorTransportedHomeomorph_proj
    (m : ℕ) (z : StandardUnlinkPowerPullback m) :
    standardUnlinkClosedTubeExteriorTransportedPowerPullbackProj m
        (standardUnlinkPowerPullbackExteriorTransportedHomeomorph m z) =
      standardUnlinkComplementExteriorHomeomorph
        (standardUnlinkPowerPullbackProj m z) :=
  rfl

/-! ## The corrected homeomorphism to the literal exterior character -/

/-- Transport a point of the full power cover to the literal exterior pullback, multiplying the
power coordinate by the normalized character gauge. -/
def standardUnlinkPowerPullbackToExterior (m : ℕ) [NeZero m]
    (z : StandardUnlinkPowerPullback m) :
    StandardUnlinkClosedTubeExteriorPowerPullback m := by
  let g := standardUnlinkComplementExteriorPowerGauge m z.1.1
  refine ⟨(standardUnlinkComplementExteriorHomeomorph z.1.1,
    ⟨g * z.1.2.1,
      mul_ne_zero (standardUnlinkComplementExteriorPowerGauge_ne_zero m z.1.1)
        z.1.2.2⟩), ?_⟩
  apply Subtype.ext
  change standardUnlinkRightDisplacementComplex
      (standardUnlinkComplementExteriorHomeomorph z.1.1).1 =
    (g * z.1.2.1) ^ m
  rw [mul_pow]
  have hz : z.1.2.1 ^ m = standardUnlinkRightDisplacementComplex z.1.1.1 := by
    exact (congrArg Subtype.val z.2).symm
  rw [hz]
  exact (standardUnlinkComplementExteriorPowerGauge_mul_character m z.1.1).symm

/-- The inverse corrected transport divides by the gauge at the inverse base point. -/
def standardUnlinkExteriorPowerPullbackToComplement (m : ℕ) [NeZero m]
    (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    StandardUnlinkPowerPullback m := by
  let q := standardUnlinkComplementExteriorHomeomorph.symm z.1.1
  let g := standardUnlinkComplementExteriorPowerGauge m q
  refine ⟨(q, ⟨g⁻¹ * z.1.2.1,
    mul_ne_zero (inv_ne_zero
      (standardUnlinkComplementExteriorPowerGauge_ne_zero m q)) z.1.2.2⟩), ?_⟩
  apply Subtype.ext
  change standardUnlinkRightDisplacementComplex q.1 =
    (g⁻¹ * z.1.2.1) ^ m
  rw [mul_pow, inv_pow]
  have hz : z.1.2.1 ^ m = standardUnlinkRightDisplacementComplex z.1.1.1 := by
    exact (congrArg Subtype.val z.2).symm
  rw [hz]
  have hg := standardUnlinkComplementExteriorPowerGauge_mul_character m q
  have hbase :
      (standardUnlinkComplementExteriorHomeomorph q : Sphere 4) = z.1.1 := by
    exact congrArg Subtype.val
      (standardUnlinkComplementExteriorHomeomorph.apply_symm_apply z.1.1)
  rw [hbase] at hg
  have hg0 : g ^ m ≠ 0 :=
    pow_ne_zero m (standardUnlinkComplementExteriorPowerGauge_ne_zero m q)
  calc
    standardUnlinkRightDisplacementComplex q.1 =
        (g ^ m)⁻¹ * (g ^ m * standardUnlinkRightDisplacementComplex q.1) := by
      rw [← mul_assoc, inv_mul_cancel₀ hg0, one_mul]
    _ = (g ^ m)⁻¹ * standardUnlinkRightDisplacementComplex z.1.1 := by rw [hg]

@[simp]
theorem standardUnlinkPowerPullbackToExterior_base (m : ℕ) [NeZero m]
    (z : StandardUnlinkPowerPullback m) :
    (standardUnlinkPowerPullbackToExterior m z).1.1 =
      standardUnlinkComplementExteriorHomeomorph z.1.1 :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackToExterior_powerCoordinate
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    (standardUnlinkPowerPullbackToExterior m z).1.2.1 =
      standardUnlinkComplementExteriorPowerGauge m z.1.1 * z.1.2.1 :=
  rfl

@[simp]
theorem standardUnlinkExteriorPowerPullbackToComplement_base
    (m : ℕ) [NeZero m]
    (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    (standardUnlinkExteriorPowerPullbackToComplement m z).1.1 =
      standardUnlinkComplementExteriorHomeomorph.symm z.1.1 :=
  rfl

@[simp]
theorem standardUnlinkExteriorPowerPullbackToComplement_powerCoordinate
    (m : ℕ) [NeZero m]
    (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    (standardUnlinkExteriorPowerPullbackToComplement m z).1.2.1 =
      (standardUnlinkComplementExteriorPowerGauge m
        (standardUnlinkComplementExteriorHomeomorph.symm z.1.1))⁻¹ * z.1.2.1 :=
  rfl

theorem continuous_standardUnlinkPowerPullbackToExterior
    (m : ℕ) [NeZero m] :
    Continuous (standardUnlinkPowerPullbackToExterior m) := by
  apply Continuous.subtype_mk
  exact (standardUnlinkComplementExteriorHomeomorph.continuous.comp
    (continuous_fst.comp continuous_subtype_val)).prodMk <|
      ((continuous_standardUnlinkComplementExteriorPowerGauge m).comp
          (continuous_fst.comp continuous_subtype_val) |>.mul
        (continuous_subtype_val.comp
          (continuous_snd.comp continuous_subtype_val))).subtype_mk _

theorem continuous_standardUnlinkExteriorPowerPullbackToComplement
    (m : ℕ) [NeZero m] :
    Continuous (standardUnlinkExteriorPowerPullbackToComplement m) := by
  apply Continuous.subtype_mk
  exact (standardUnlinkComplementExteriorHomeomorph.symm.continuous.comp
    (continuous_fst.comp continuous_subtype_val)).prodMk <|
      (((continuous_standardUnlinkComplementExteriorPowerGauge m).comp
          (standardUnlinkComplementExteriorHomeomorph.symm.continuous.comp
            (continuous_fst.comp continuous_subtype_val))).inv₀
          (fun z ↦ standardUnlinkComplementExteriorPowerGauge_ne_zero m
            (standardUnlinkComplementExteriorHomeomorph.symm z.1.1)) |>.mul
        (continuous_subtype_val.comp
          (continuous_snd.comp continuous_subtype_val))).subtype_mk _

/-- The corrected total-space homeomorphism from the full unlink power cover to the literal
power pullback over the strict tubular exterior. -/
def standardUnlinkPowerPullbackExteriorHomeomorph
    (m : ℕ) [NeZero m] :
    StandardUnlinkPowerPullback m ≃ₜ
      StandardUnlinkClosedTubeExteriorPowerPullback m where
  toFun := standardUnlinkPowerPullbackToExterior m
  invFun := standardUnlinkExteriorPowerPullbackToComplement m
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact standardUnlinkComplementExteriorHomeomorph.symm_apply_apply z.1.1
    · apply Subtype.ext
      rw [standardUnlinkExteriorPowerPullbackToComplement_powerCoordinate,
        standardUnlinkPowerPullbackToExterior_base,
        standardUnlinkComplementExteriorHomeomorph.symm_apply_apply,
        standardUnlinkPowerPullbackToExterior_powerCoordinate,
        inv_mul_cancel_left₀
          (standardUnlinkComplementExteriorPowerGauge_ne_zero m z.1.1)]
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact standardUnlinkComplementExteriorHomeomorph.apply_symm_apply z.1.1
    · apply Subtype.ext
      change standardUnlinkComplementExteriorPowerGauge m
          (standardUnlinkComplementExteriorHomeomorph.symm z.1.1) *
            ((standardUnlinkComplementExteriorPowerGauge m
              (standardUnlinkComplementExteriorHomeomorph.symm z.1.1))⁻¹ * z.1.2.1) =
        z.1.2.1
      rw [← mul_assoc, mul_inv_cancel₀
        (standardUnlinkComplementExteriorPowerGauge_ne_zero m
          (standardUnlinkComplementExteriorHomeomorph.symm z.1.1)), one_mul]
  continuous_toFun := continuous_standardUnlinkPowerPullbackToExterior m
  continuous_invFun := continuous_standardUnlinkExteriorPowerPullbackToComplement m

@[simp]
theorem standardUnlinkPowerPullbackExteriorHomeomorph_proj
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    standardUnlinkClosedTubeExteriorPowerPullbackProj m
        (standardUnlinkPowerPullbackExteriorHomeomorph m z) =
      standardUnlinkComplementExteriorHomeomorph
        (standardUnlinkPowerPullbackProj m z) :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackExteriorHomeomorph_apply_base
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    (standardUnlinkPowerPullbackExteriorHomeomorph m z).1.1 =
      standardUnlinkComplementExteriorHomeomorph z.1.1 :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackExteriorHomeomorph_apply_powerCoordinate
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    (standardUnlinkPowerPullbackExteriorHomeomorph m z).1.2.1 =
      standardUnlinkComplementExteriorPowerGauge m z.1.1 * z.1.2.1 :=
  rfl

@[simp]
theorem standardUnlinkPowerPullbackExteriorHomeomorph_symm_proj
    (m : ℕ) [NeZero m]
    (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    standardUnlinkPowerPullbackProj m
        ((standardUnlinkPowerPullbackExteriorHomeomorph m).symm z) =
      standardUnlinkComplementExteriorHomeomorph.symm
        (standardUnlinkClosedTubeExteriorPowerPullbackProj m z) :=
  rfl

/-! ## Deck equivariance of the corrected transport -/

/-- Roots of unity act on the literal exterior pullback by multiplication in the power
coordinate. -/
def standardUnlinkClosedTubeExteriorPowerDeckMap (m : ℕ)
    (u : rootsOfUnity m ℂ) (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    StandardUnlinkClosedTubeExteriorPowerPullback m :=
  ⟨(z.1.1, ⟨((u.1 : ℂˣ) : ℂ) * z.1.2.1,
    mul_ne_zero (Units.ne_zero u.1) z.1.2.2⟩), by
      apply Subtype.ext
      change (standardUnlinkClosedTubeExteriorRightNormalMap z.1.1 : ℂ) =
        (((u.1 : ℂˣ) : ℂ) * z.1.2.1) ^ m
      rw [mul_pow, (mem_rootsOfUnity' m u.1).mp u.2, one_mul]
      exact congrArg Subtype.val z.2⟩

@[simp]
theorem standardUnlinkClosedTubeExteriorPowerDeckMap_base (m : ℕ)
    (u : rootsOfUnity m ℂ) (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    (standardUnlinkClosedTubeExteriorPowerDeckMap m u z).1.1 = z.1.1 :=
  rfl

@[simp]
theorem standardUnlinkClosedTubeExteriorPowerDeckMap_powerCoordinate (m : ℕ)
    (u : rootsOfUnity m ℂ) (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    (standardUnlinkClosedTubeExteriorPowerDeckMap m u z).1.2.1 =
      ((u.1 : ℂˣ) : ℂ) * z.1.2.1 :=
  rfl

theorem standardUnlinkPowerPullbackExteriorHomeomorph_deck_equivariant
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ)
    (z : StandardUnlinkPowerPullback m) :
    standardUnlinkPowerPullbackExteriorHomeomorph m (u • z) =
      standardUnlinkClosedTubeExteriorPowerDeckMap m u
        (standardUnlinkPowerPullbackExteriorHomeomorph m z) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change standardUnlinkComplementExteriorPowerGauge m z.1.1 *
        (((u.1 : ℂˣ) : ℂ) * z.1.2.1) =
      ((u.1 : ℂˣ) : ℂ) *
        (standardUnlinkComplementExteriorPowerGauge m z.1.1 * z.1.2.1)
    ring

/-! ## Exact transport of the equatorial lifts -/

theorem quarter_lt_norm_standardUnlinkNormalProjection_equator_sub_center
    (i : Fin 2) (x : Sphere 3) :
    1 / 4 <
      ‖standardUnlinkNormalProjection (equatorSphereMap x) -
        standardUnlinkNormalCenter i‖ := by
  have hsq :
      ‖standardUnlinkNormalProjection (equatorSphereMap x) -
          standardUnlinkNormalCenter i‖ ^ 2 =
        (1 / 2 : ℝ) ^ 2 + (x.1 3) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    fin_cases i <;>
      simp [standardUnlinkNormalProjection, standardUnlinkNormalCenter,
        standardUnlinkHeight, equatorSphereMap, equatorAmbientMap,
        Fin.sum_univ_succ]
  nlinarith [sq_nonneg (x.1 3),
    norm_nonneg (standardUnlinkNormalProjection (equatorSphereMap x) -
      standardUnlinkNormalCenter i)]

private theorem equatorSphereMap_not_mem_standardUnlinkClosedTubes_quarter
    (x : Sphere 3) :
    equatorSphereMap x ∉ standardUnlinkClosedTubes (1 / 4 : ℝ) := by
  intro hx
  rcases hx with hx | hx
  · have hle :
        ‖standardUnlinkNormalProjection (equatorSphereMap x) -
          standardUnlinkNormalCenter 0‖ ≤ 1 / 4 := by
      simpa only [standardUnlinkClosedTube, mem_preimage, mem_closedBall,
        dist_eq_norm] using hx
    exact (not_lt_of_ge hle)
      (quarter_lt_norm_standardUnlinkNormalProjection_equator_sub_center 0 x)
  · have hle :
        ‖standardUnlinkNormalProjection (equatorSphereMap x) -
          standardUnlinkNormalCenter 1‖ ≤ 1 / 4 := by
      simpa only [standardUnlinkClosedTube, mem_preimage, mem_closedBall,
        dist_eq_norm] using hx
    exact (not_lt_of_ge hle)
      (quarter_lt_norm_standardUnlinkNormalProjection_equator_sub_center 1 x)

/-- The coordinate equator, regarded as a map to the strict tubular exterior. -/
def equatorUnlinkClosedTubeExteriorMap (x : Sphere 3) :
    StandardUnlinkClosedTubeExterior := by
  refine ⟨equatorSphereMap x, ?_⟩
  rw [mem_standardUnlinkClosedTubeExteriorOpens]
  intro i
  exact lt_trans (by norm_num : (1 / 8 : ℝ) < 1 / 4)
    (quarter_lt_norm_standardUnlinkNormalProjection_equator_sub_center i x)

@[simp]
theorem equatorUnlinkClosedTubeExteriorMap_coe (x : Sphere 3) :
    (equatorUnlinkClosedTubeExteriorMap x : Sphere 4) = equatorSphereMap x :=
  rfl

theorem standardUnlinkComplementExteriorHomeomorph_equator
    (x : Sphere 3) :
    standardUnlinkComplementExteriorHomeomorph (equatorUnlinkComplementMap x) =
      equatorUnlinkClosedTubeExteriorMap x := by
  apply Subtype.ext
  exact standardUnlinkComplementExteriorHomeomorph_eq_self_of_not_mem_closedTubes_quarter
    (equatorUnlinkComplementMap x)
    (equatorSphereMap_not_mem_standardUnlinkClosedTubes_quarter x)

@[simp]
theorem standardUnlinkComplementExteriorPowerGauge_equator
    (m : ℕ) (x : Sphere 3) :
    standardUnlinkComplementExteriorPowerGauge m (equatorUnlinkComplementMap x) = 1 := by
  apply standardUnlinkComplementExteriorPowerGauge_eq_one_of_fixed
  exact congrArg Subtype.val
    (standardUnlinkComplementExteriorHomeomorph_equator x)

/-- The same explicit equatorial lift, now bundled in the literal exterior pullback. -/
def equatorUnlinkClosedTubeExteriorPowerLift
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    StandardUnlinkClosedTubeExteriorPowerPullback m :=
  ⟨(equatorUnlinkClosedTubeExteriorMap x, equatorUnlinkPowerCoordinate m a x), by
    apply Subtype.ext
    change standardUnlinkRightDisplacementComplex (equatorSphereMap x) =
      equatorUnlinkPowerRootTranslate m a x ^ m
    rw [standardUnlinkRightDisplacementComplex_equatorSphereMap,
      equatorUnlinkPowerRootTranslate_pow]⟩

@[simp]
theorem equatorUnlinkClosedTubeExteriorPowerLift_proj
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    standardUnlinkClosedTubeExteriorPowerPullbackProj m
        (equatorUnlinkClosedTubeExteriorPowerLift m a x) =
      equatorUnlinkClosedTubeExteriorMap x :=
  rfl

@[simp]
theorem equatorUnlinkClosedTubeExteriorPowerLift_powerCoordinate
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    (equatorUnlinkClosedTubeExteriorPowerLift m a x).1.2.1 =
      equatorUnlinkPowerRootTranslate m a x :=
  rfl

theorem standardUnlinkPowerPullbackExteriorHomeomorph_equatorUnlinkPowerLift
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    standardUnlinkPowerPullbackExteriorHomeomorph m
        (equatorUnlinkPowerLift m a x) =
      equatorUnlinkClosedTubeExteriorPowerLift m a x := by
  apply Subtype.ext
  apply Prod.ext
  · exact standardUnlinkComplementExteriorHomeomorph_equator x
  · apply Subtype.ext
    change standardUnlinkComplementExteriorPowerGauge m
        (equatorUnlinkComplementMap x) * equatorUnlinkPowerRootTranslate m a x =
      equatorUnlinkPowerRootTranslate m a x
    rw [standardUnlinkComplementExteriorPowerGauge_equator, one_mul]

theorem standardUnlinkPowerPullbackExteriorHomeomorph_equatorUnlinkPowerLift_range
    (m : ℕ) [NeZero m] (a : ZMod m) :
    standardUnlinkPowerPullbackExteriorHomeomorph m ''
        range (equatorUnlinkPowerLift m a) =
      range (equatorUnlinkClosedTubeExteriorPowerLift m a) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x,
      (standardUnlinkPowerPullbackExteriorHomeomorph_equatorUnlinkPowerLift m a x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨equatorUnlinkPowerLift m a x, ⟨x, rfl⟩,
      standardUnlinkPowerPullbackExteriorHomeomorph_equatorUnlinkPowerLift m a x⟩

/-! ## Identification with the strict part of the compact-exterior pullback -/

/-- Include the strict tubular exterior into the closed coordinate exterior. -/
def standardUnlinkClosedTubeExteriorToCoordinateExterior
    (q : StandardUnlinkClosedTubeExterior) :
    ↑(coordinateUnlinkExterior (1 / 8 : ℝ)) :=
  ⟨q.1, standardUnlinkClosedTubeExterior_subset_coordinateUnlinkExterior q.2⟩

@[simp]
theorem standardUnlinkClosedTubeExteriorToCoordinateExterior_coe
    (q : StandardUnlinkClosedTubeExterior) :
    (standardUnlinkClosedTubeExteriorToCoordinateExterior q : Sphere 4) = q.1 :=
  rfl

theorem continuous_standardUnlinkClosedTubeExteriorToCoordinateExterior :
    Continuous standardUnlinkClosedTubeExteriorToCoordinateExterior :=
  continuous_subtype_val.subtype_mk _

theorem injective_standardUnlinkClosedTubeExteriorToCoordinateExterior :
    Injective standardUnlinkClosedTubeExteriorToCoordinateExterior := by
  intro q r h
  apply Subtype.ext
  exact congrArg
    (fun s : ↑(coordinateUnlinkExterior (1 / 8 : ℝ)) ↦ (s : Sphere 4)) h

/-- Include the literal strict-exterior power pullback into the compact-exterior power
pullback. -/
def standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior
    (m : ℕ) (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    CoordinateUnlinkExteriorEighthPowerPullback m := by
  refine ⟨(standardUnlinkClosedTubeExteriorToCoordinateExterior z.1.1, z.1.2), ?_⟩
  apply Subtype.ext
  exact congrArg Subtype.val z.2

@[simp]
theorem standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior_base
    (m : ℕ) (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    (standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior m z).1.1 =
      standardUnlinkClosedTubeExteriorToCoordinateExterior z.1.1 :=
  rfl

@[simp]
theorem standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior_powerCoordinate
    (m : ℕ) (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    (standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior m z).1.2 = z.1.2 :=
  rfl

theorem continuous_standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior
    (m : ℕ) :
    Continuous
      (standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior m) := by
  apply Continuous.subtype_mk
  exact (continuous_standardUnlinkClosedTubeExteriorToCoordinateExterior.comp
    (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)

theorem injective_standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior
    (m : ℕ) :
    Injective
      (standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior m) := by
  intro z w h
  apply Subtype.ext
  apply Prod.ext
  · apply injective_standardUnlinkClosedTubeExteriorToCoordinateExterior
    exact congrArg (fun y : CoordinateUnlinkExteriorEighthPowerPullback m ↦ y.1.1) h
  · exact congrArg (fun y : CoordinateUnlinkExteriorEighthPowerPullback m ↦ y.1.2) h

/-- The exact inverse-image open subset of the compact-exterior power pullback lying over the
strict tubular exterior. -/
def coordinateUnlinkExteriorEighthPowerPullbackStrictOpens (m : ℕ) :
    Opens (CoordinateUnlinkExteriorEighthPowerPullback m) :=
  ⟨{z | z.1.1.1 ∈ standardUnlinkClosedTubeExteriorOpens},
    standardUnlinkClosedTubeExteriorOpens.2.preimage
      (continuous_subtype_val.comp
        (continuous_fst.comp continuous_subtype_val))⟩

abbrev CoordinateUnlinkExteriorEighthPowerPullbackStrict (m : ℕ) :=
  coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m

@[simp]
theorem mem_coordinateUnlinkExteriorEighthPowerPullbackStrictOpens
    (m : ℕ) (z : CoordinateUnlinkExteriorEighthPowerPullback m) :
    z ∈ coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m ↔
      z.1.1.1 ∈ standardUnlinkClosedTubeExteriorOpens :=
  Iff.rfl

/-- The strict-exterior pullback is exactly the inverse-image open subset of the compact
coordinate-exterior pullback. -/
def standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph
    (m : ℕ) :
    StandardUnlinkClosedTubeExteriorPowerPullback m ≃ₜ
      CoordinateUnlinkExteriorEighthPowerPullbackStrict m where
  toFun z := ⟨standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior m z,
    z.1.1.2⟩
  invFun z := by
    refine ⟨(⟨z.1.1.1.1, z.2⟩, z.1.1.2), ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val z.1.2
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> rfl
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> rfl
  continuous_toFun := by
    exact (continuous_standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior m)
      |>.subtype_mk _
  continuous_invFun := by
    fun_prop

theorem range_standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior
    (m : ℕ) :
    range (standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior m) =
      {z | z ∈ coordinateUnlinkExteriorEighthPowerPullbackStrictOpens m} := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact w.1.1.2
  · intro hz
    let w : CoordinateUnlinkExteriorEighthPowerPullbackStrict m := ⟨z, hz⟩
    refine ⟨(standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph m).symm w,
      ?_⟩
    exact congrArg Subtype.val
      ((standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph m)
        |>.apply_symm_apply w)

theorem standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior_deck
    (m : ℕ) (u : rootsOfUnity m ℂ)
    (z : StandardUnlinkClosedTubeExteriorPowerPullback m) :
    standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior m
        (standardUnlinkClosedTubeExteriorPowerDeckMap m u z) =
      coordinateUnlinkExteriorEighthPowerDeckMap m u
        (standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior m z) :=
  rfl

/-- The corrected full-cover transport, included into the exact strict part of the compact
coordinate-exterior pullback. -/
def standardUnlinkPowerPullbackToCoordinateExteriorStrict
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    CoordinateUnlinkExteriorEighthPowerPullback m :=
  standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior m
    (standardUnlinkPowerPullbackExteriorHomeomorph m z)

/-- The full unlink power pullback is homeomorphic to the exact strict-base inverse image in the
compact coordinate-exterior pullback. -/
def standardUnlinkPowerPullbackCoordinateExteriorStrictHomeomorph
    (m : ℕ) [NeZero m] :
    StandardUnlinkPowerPullback m ≃ₜ
      CoordinateUnlinkExteriorEighthPowerPullbackStrict m :=
  (standardUnlinkPowerPullbackExteriorHomeomorph m).trans
    (standardUnlinkClosedTubeExteriorPowerPullbackCoordinateStrictHomeomorph m)

@[simp]
theorem standardUnlinkPowerPullbackCoordinateExteriorStrictHomeomorph_coe
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    (standardUnlinkPowerPullbackCoordinateExteriorStrictHomeomorph m z :
        CoordinateUnlinkExteriorEighthPowerPullback m) =
      standardUnlinkPowerPullbackToCoordinateExteriorStrict m z :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorEighthPowerPullbackProj_fullTransport
    (m : ℕ) [NeZero m] (z : StandardUnlinkPowerPullback m) :
    coordinateUnlinkExteriorEighthPowerPullbackProj m
        (standardUnlinkPowerPullbackToCoordinateExteriorStrict m z) =
      standardUnlinkClosedTubeExteriorToCoordinateExterior
        (standardUnlinkComplementExteriorHomeomorph
          (standardUnlinkPowerPullbackProj m z)) :=
  rfl

theorem standardUnlinkPowerPullbackToCoordinateExteriorStrict_deck_equivariant
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ)
    (z : StandardUnlinkPowerPullback m) :
    standardUnlinkPowerPullbackToCoordinateExteriorStrict m (u • z) =
      u • standardUnlinkPowerPullbackToCoordinateExteriorStrict m z := by
  rw [standardUnlinkPowerPullbackToCoordinateExteriorStrict,
    standardUnlinkPowerPullbackExteriorHomeomorph_deck_equivariant,
    standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior_deck]
  rfl

theorem standardUnlinkPowerPullbackToCoordinateExteriorStrict_equatorUnlinkPowerLift
    (m : ℕ) [NeZero m] (a : ZMod m) (x : Sphere 3) :
    standardUnlinkPowerPullbackToCoordinateExteriorStrict m
        (equatorUnlinkPowerLift m a x) =
      standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior m
        (equatorUnlinkClosedTubeExteriorPowerLift m a x) := by
  rw [standardUnlinkPowerPullbackToCoordinateExteriorStrict,
    standardUnlinkPowerPullbackExteriorHomeomorph_equatorUnlinkPowerLift]

theorem standardUnlinkPowerPullbackToCoordinateExteriorStrict_equatorUnlinkPowerLift_range
    (m : ℕ) [NeZero m] (a : ZMod m) :
    standardUnlinkPowerPullbackToCoordinateExteriorStrict m ''
        range (equatorUnlinkPowerLift m a) =
      range (fun x ↦
        standardUnlinkClosedTubeExteriorPowerPullbackToCoordinateExterior m
          (equatorUnlinkClosedTubeExteriorPowerLift m a x)) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x,
      (standardUnlinkPowerPullbackToCoordinateExteriorStrict_equatorUnlinkPowerLift
        m a x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨equatorUnlinkPowerLift m a x, ⟨x, rfl⟩,
      standardUnlinkPowerPullbackToCoordinateExteriorStrict_equatorUnlinkPowerLift m a x⟩

/-! ## Deck equivariance of the canonical transport -/

/-- Roots of unity act on the transported pullback by multiplying its unchanged power
coordinate. -/
def standardUnlinkExteriorTransportedPowerDeckMap (m : ℕ)
    (u : rootsOfUnity m ℂ)
    (z : StandardUnlinkClosedTubeExteriorTransportedPowerPullback m) :
    StandardUnlinkClosedTubeExteriorTransportedPowerPullback m :=
  ⟨(z.1.1, ⟨((u.1 : ℂˣ) : ℂ) * z.1.2.1,
    mul_ne_zero (Units.ne_zero u.1) z.1.2.2⟩), by
      apply Subtype.ext
      change (standardUnlinkClosedTubeExteriorTransportedRightNormalMap z.1.1 : ℂ) =
        (((u.1 : ℂˣ) : ℂ) * z.1.2.1) ^ m
      rw [mul_pow, (mem_rootsOfUnity' m u.1).mp u.2, one_mul]
      exact congrArg Subtype.val z.2⟩

theorem standardUnlinkPowerPullbackToExteriorTransported_deck_equivariant
    (m : ℕ) (u : rootsOfUnity m ℂ) (z : StandardUnlinkPowerPullback m) :
    standardUnlinkPowerPullbackToExteriorTransported m (u • z) =
      standardUnlinkExteriorTransportedPowerDeckMap m u
        (standardUnlinkPowerPullbackToExteriorTransported m z) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    rfl

end SplittingSpheres
