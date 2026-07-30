/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCTblLibInvariantSafeAmbientValueBridges

/-!
# The corrected five-local degree-twelve ambient block

The degree-twelve part of the first invariant-safe five-local position
orientation used the wrong ordering inside its equal-invariant block.  Exact
class values determine the genuine action:

* alpha-one interchanges ATLAS powers one and two, and powers seven and
  eleven;
* alpha-two interchanges powers one and eleven, and powers two and seven.

Consequently CT positions `20, 21, 22, 23` must carry powers
`2, 7, 11, 1`, respectively, once position `20` is anchored at power two.
This file proves the eight required class-value identities for that corrected
block.  It deliberately makes no assertion about the other twenty positions.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The first audited class permutation is involutive in the certified
class order. -/
theorem alternatingSixAlphaOneConjugacyClassPermutation_symm_eq_vector
    (j : Fin 31) :
    alternatingSixAlphaOneConjugacyClassPermutation.symm j =
      alternatingSixAlphaOneConjugacyClassVector j := by
  apply alternatingSixAlphaOneConjugacyClassPermutation.injective
  rw [alternatingSixAlphaOneConjugacyClassPermutation.apply_symm_apply]
  rw [alternatingSixAlphaOneConjugacyClassPermutation_eq_vector]
  fin_cases j <;>
    rfl

/-- The second audited class permutation is involutive in the certified
class order. -/
theorem alternatingSixAlphaTwoConjugacyClassPermutation_symm_eq_vector
    (j : Fin 31) :
    alternatingSixAlphaTwoConjugacyClassPermutation.symm j =
      alternatingSixAlphaTwoConjugacyClassVector j := by
  apply alternatingSixAlphaTwoConjugacyClassPermutation.injective
  rw [alternatingSixAlphaTwoConjugacyClassPermutation.apply_symm_apply]
  rw [alternatingSixAlphaTwoConjugacyClassPermutation_eq_vector]
  fin_cases j <;>
    rfl

/-- Applying the inverse of the first audited class permutation twice is
the identity. -/
theorem alternatingSixAlphaOneConjugacyClassPermutation_symm_symm
    (j : Fin 31) :
    alternatingSixAlphaOneConjugacyClassPermutation.symm
        (alternatingSixAlphaOneConjugacyClassPermutation.symm j) =
      j := by
  calc
    alternatingSixAlphaOneConjugacyClassPermutation.symm
          (alternatingSixAlphaOneConjugacyClassPermutation.symm j) =
        alternatingSixAlphaOneConjugacyClassVector
          (alternatingSixAlphaOneConjugacyClassPermutation.symm j) :=
      alternatingSixAlphaOneConjugacyClassPermutation_symm_eq_vector _
    _ = alternatingSixAlphaOneConjugacyClassPermutation
          (alternatingSixAlphaOneConjugacyClassPermutation.symm j) :=
      (alternatingSixAlphaOneConjugacyClassPermutation_eq_vector _).symm
    _ = j :=
      alternatingSixAlphaOneConjugacyClassPermutation.apply_symm_apply j

/-- Applying the inverse of the second audited class permutation twice is
the identity. -/
theorem alternatingSixAlphaTwoConjugacyClassPermutation_symm_symm
    (j : Fin 31) :
    alternatingSixAlphaTwoConjugacyClassPermutation.symm
        (alternatingSixAlphaTwoConjugacyClassPermutation.symm j) =
      j := by
  calc
    alternatingSixAlphaTwoConjugacyClassPermutation.symm
          (alternatingSixAlphaTwoConjugacyClassPermutation.symm j) =
        alternatingSixAlphaTwoConjugacyClassVector
          (alternatingSixAlphaTwoConjugacyClassPermutation.symm j) :=
      alternatingSixAlphaTwoConjugacyClassPermutation_symm_eq_vector _
    _ = alternatingSixAlphaTwoConjugacyClassPermutation
          (alternatingSixAlphaTwoConjugacyClassPermutation.symm j) :=
      (alternatingSixAlphaTwoConjugacyClassPermutation_eq_vector _).symm
    _ = j :=
      alternatingSixAlphaTwoConjugacyClassPermutation.apply_symm_apply j

private theorem reciprocal_classValue_transport
    (e : Equiv.Perm (Fin 31))
    (hInvolutive : ∀ j, e.symm (e.symm j) = j)
    (source target : Fin 31 → ℂ)
    (hTransport : ∀ j, target j = source (e.symm j))
    (j : Fin 31) :
    source j = target (e.symm j) := by
  calc
    source j = source (e.symm (e.symm j)) := by
      rw [hInvolutive]
    _ = target (e.symm j) := (hTransport _).symm

private theorem alternatingSixAmbientAtlas12P1Eta_eq_powerTwoCentral_pow_five :
    alternatingSixAmbientAtlas12P1Eta =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 5 := by
  rw [alternatingSixAmbientAtlas12P1Eta,
    ← alternatingSixAmbientAtlasTwelvePowerTwo_root_pow_hundred,
    ← pow_mul]
  change ζ ^ 20 = ζ ^ 500
  rw [show 500 = 120 * 4 + 20 by norm_num, pow_add, pow_mul,
    alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one,
    one_pow, one_mul]

private theorem
    alternatingSixAmbientAtlas12P1Eta_sq_eq_powerTwoCentral_pow_four :
    alternatingSixAmbientAtlas12P1Eta ^ 2 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 4 := by
  rw [alternatingSixAmbientAtlas12P1Eta,
    ← alternatingSixAmbientAtlasTwelvePowerTwo_root_pow_hundred,
    ← pow_mul, ← pow_mul]
  change ζ ^ 40 = ζ ^ 400
  rw [show 400 = 120 * 3 + 40 by norm_num, pow_add, pow_mul,
    alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one,
    one_pow, one_mul]

private theorem
    alternatingSixAmbientAtlas12P1Eta_cube_eq_powerTwoCentral_cube :
    alternatingSixAmbientAtlas12P1Eta ^ 3 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 3 := by
  rw [alternatingSixAmbientAtlas12P1Eta,
    ← alternatingSixAmbientAtlasTwelvePowerTwo_root_pow_hundred,
    ← pow_mul, ← pow_mul]
  change ζ ^ 60 = ζ ^ 300
  rw [show 300 = 120 * 2 + 60 by norm_num, pow_add, pow_mul,
    alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one,
    one_pow, one_mul]

private theorem
    alternatingSixAmbientAtlas12P1Eta_pow_four_eq_powerTwoCentral_sq :
    alternatingSixAmbientAtlas12P1Eta ^ 4 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 2 := by
  rw [alternatingSixAmbientAtlas12P1Eta,
    ← alternatingSixAmbientAtlasTwelvePowerTwo_root_pow_hundred,
    ← pow_mul, ← pow_mul]
  change ζ ^ 80 = ζ ^ 200
  rw [show 200 = 120 + 80 by norm_num, pow_add,
    alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one,
    one_mul]

private theorem
    alternatingSixAmbientAtlas12P1Eta_pow_five_eq_powerTwoCentral :
    alternatingSixAmbientAtlas12P1Eta ^ 5 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral := by
  rw [alternatingSixAmbientAtlas12P1Eta,
    ← alternatingSixAmbientAtlasTwelvePowerTwo_root_pow_hundred,
    ← pow_mul]

private theorem alternatingSixAmbientAtlasPowerTwoCentral_pow_five_sq :
    (alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 5) ^ 2 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 4 := by
  rw [← alternatingSixAmbientAtlas12P1Eta_eq_powerTwoCentral_pow_five]
  exact
    alternatingSixAmbientAtlas12P1Eta_sq_eq_powerTwoCentral_pow_four

private theorem alternatingSixAmbientAtlasPowerTwoCentral_pow_five_cube :
    (alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 5) ^ 3 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 3 := by
  rw [← alternatingSixAmbientAtlas12P1Eta_eq_powerTwoCentral_pow_five]
  exact
    alternatingSixAmbientAtlas12P1Eta_cube_eq_powerTwoCentral_cube

private theorem
    alternatingSixAmbientAtlasPowerTwoCentral_pow_five_pow_four :
    (alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 5) ^ 4 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 2 := by
  rw [← alternatingSixAmbientAtlas12P1Eta_eq_powerTwoCentral_pow_five]
  exact
    alternatingSixAmbientAtlas12P1Eta_pow_four_eq_powerTwoCentral_sq

private theorem
    alternatingSixAmbientAtlasPowerTwoCentral_pow_five_pow_five :
    (alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 5) ^ 5 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral := by
  rw [← alternatingSixAmbientAtlas12P1Eta_eq_powerTwoCentral_pow_five]
  exact
    alternatingSixAmbientAtlas12P1Eta_pow_five_eq_powerTwoCentral

/-- Under alpha-one, the power-two degree-twelve row is transported to the
power-one row. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_alphaOne_classValue :
    ∀ j : Fin 31,
      alternatingSixAmbientAtlas12P1ClassValue j =
        alternatingSixAmbientAtlasTwelvePowerTwoClassValue
          (alternatingSixAlphaOneConjugacyClassPermutation.symm j) := by
  intro j
  rw [alternatingSixAlphaOneConjugacyClassPermutation_symm_eq_vector]
  fin_cases j <;>
    simp [
      alternatingSixAlphaOneConjugacyClassVector,
      alternatingSixAmbientAtlas12P1ClassValue,
      alternatingSixAmbientAtlasTwelvePowerTwoClassValue,
      alternatingSixAmbientAtlas12P1Alpha,
      alternatingSixAmbientAtlas12P1Beta,
      alternatingSixAmbientAtlasTwelvePowerTwoAlpha,
      alternatingSixAmbientAtlasTwelvePowerTwoBeta,
      alternatingSixAmbientAtlas12P1Eta_eq_powerTwoCentral_pow_five,
      alternatingSixAmbientAtlasPowerTwoCentral_pow_five_sq,
      alternatingSixAmbientAtlasPowerTwoCentral_pow_five_cube,
      alternatingSixAmbientAtlasPowerTwoCentral_pow_five_pow_four,
      alternatingSixAmbientAtlasPowerTwoCentral_pow_five_pow_five,
      alternatingSixCyclotomicValue
    ]

/-- The reciprocal alpha-one transport sends the power-one row to the
power-two row. -/
theorem alternatingSixAmbientAtlas12P1_alphaOne_classValue :
    ∀ j : Fin 31,
      alternatingSixAmbientAtlasTwelvePowerTwoClassValue j =
        alternatingSixAmbientAtlas12P1ClassValue
          (alternatingSixAlphaOneConjugacyClassPermutation.symm j) := by
  exact
    reciprocal_classValue_transport
      alternatingSixAlphaOneConjugacyClassPermutation
      alternatingSixAlphaOneConjugacyClassPermutation_symm_symm
      alternatingSixAmbientAtlasTwelvePowerTwoClassValue
      alternatingSixAmbientAtlas12P1ClassValue
      alternatingSixAmbientAtlasTwelvePowerTwo_alphaOne_classValue

private theorem
    alternatingSixAmbientAtlas12P11Central_eq_powerSevenEta_pow_five :
    alternatingSixAmbientAtlas12P11Central =
      alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 5 := by
  change
    alternatingSixAmbientAtlasTwelvePowerTwoCentral =
      alternatingSixAmbientAtlas12P1Eta ^ 5
  exact
    alternatingSixAmbientAtlas12P1Eta_pow_five_eq_powerTwoCentral.symm

private theorem
    alternatingSixAmbientAtlas12P11Central_sq_eq_powerSevenEta_pow_four :
    alternatingSixAmbientAtlas12P11Central ^ 2 =
      alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 4 := by
  change
    alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 2 =
      alternatingSixAmbientAtlas12P1Eta ^ 4
  exact
    alternatingSixAmbientAtlas12P1Eta_pow_four_eq_powerTwoCentral_sq.symm

private theorem
    alternatingSixAmbientAtlas12P11Central_cube_eq_powerSevenEta_cube :
    alternatingSixAmbientAtlas12P11Central ^ 3 =
      alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 3 := by
  change
    alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 3 =
      alternatingSixAmbientAtlas12P1Eta ^ 3
  exact
    alternatingSixAmbientAtlas12P1Eta_cube_eq_powerTwoCentral_cube.symm

private theorem
    alternatingSixAmbientAtlas12P11Central_pow_four_eq_powerSevenEta_sq :
    alternatingSixAmbientAtlas12P11Central ^ 4 =
      alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 2 := by
  change
    alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 4 =
      alternatingSixAmbientAtlas12P1Eta ^ 2
  exact
    alternatingSixAmbientAtlas12P1Eta_sq_eq_powerTwoCentral_pow_four.symm

private theorem
    alternatingSixAmbientAtlas12P11Central_pow_five_eq_powerSevenEta :
    alternatingSixAmbientAtlas12P11Central ^ 5 =
      alternatingSixAmbientAtlasTwelvePowerSevenEta := by
  change
    alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 5 =
      alternatingSixAmbientAtlas12P1Eta
  exact
    alternatingSixAmbientAtlas12P1Eta_eq_powerTwoCentral_pow_five.symm

private theorem alternatingSixAmbientAtlasPowerSevenEta_pow_five_sq :
    (alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 5) ^ 2 =
      alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 4 := by
  rw [←
    alternatingSixAmbientAtlas12P11Central_eq_powerSevenEta_pow_five]
  exact
    alternatingSixAmbientAtlas12P11Central_sq_eq_powerSevenEta_pow_four

private theorem alternatingSixAmbientAtlasPowerSevenEta_pow_five_cube :
    (alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 5) ^ 3 =
      alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 3 := by
  rw [←
    alternatingSixAmbientAtlas12P11Central_eq_powerSevenEta_pow_five]
  exact
    alternatingSixAmbientAtlas12P11Central_cube_eq_powerSevenEta_cube

private theorem
    alternatingSixAmbientAtlasPowerSevenEta_pow_five_pow_four :
    (alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 5) ^ 4 =
      alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 2 := by
  rw [←
    alternatingSixAmbientAtlas12P11Central_eq_powerSevenEta_pow_five]
  exact
    alternatingSixAmbientAtlas12P11Central_pow_four_eq_powerSevenEta_sq

private theorem
    alternatingSixAmbientAtlasPowerSevenEta_pow_five_pow_five :
    (alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 5) ^ 5 =
      alternatingSixAmbientAtlasTwelvePowerSevenEta := by
  rw [←
    alternatingSixAmbientAtlas12P11Central_eq_powerSevenEta_pow_five]
  exact
    alternatingSixAmbientAtlas12P11Central_pow_five_eq_powerSevenEta

/-- Under alpha-one, the power-seven degree-twelve row is transported to
the power-eleven row. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_alphaOne_classValue :
    ∀ j : Fin 31,
      alternatingSixAmbientAtlas12P11ClassValue j =
        alternatingSixAmbientAtlasTwelvePowerSevenClassValue
          (alternatingSixAlphaOneConjugacyClassPermutation.symm j) := by
  intro j
  rw [alternatingSixAlphaOneConjugacyClassPermutation_symm_eq_vector]
  fin_cases j <;>
    simp [
      alternatingSixAlphaOneConjugacyClassVector,
      alternatingSixAmbientAtlasTwelvePowerSevenClassValue,
      alternatingSixAmbientAtlas12P11ClassValue,
      alternatingSixAmbientAtlasTwelvePowerSevenAlpha,
      alternatingSixAmbientAtlasTwelvePowerSevenBeta,
      alternatingSixAmbientAtlas12P11Alpha,
      alternatingSixAmbientAtlas12P11Beta,
      alternatingSixAmbientAtlas12P11Central_eq_powerSevenEta_pow_five,
      alternatingSixAmbientAtlasPowerSevenEta_pow_five_sq,
      alternatingSixAmbientAtlasPowerSevenEta_pow_five_cube,
      alternatingSixAmbientAtlasPowerSevenEta_pow_five_pow_four,
      alternatingSixAmbientAtlasPowerSevenEta_pow_five_pow_five,
      alternatingSixCyclotomicValue
    ]

/-- The reciprocal alpha-one transport sends the power-eleven row to the
power-seven row. -/
theorem alternatingSixAmbientAtlas12P11_alphaOne_classValue :
    ∀ j : Fin 31,
      alternatingSixAmbientAtlasTwelvePowerSevenClassValue j =
        alternatingSixAmbientAtlas12P11ClassValue
          (alternatingSixAlphaOneConjugacyClassPermutation.symm j) := by
  exact
    reciprocal_classValue_transport
      alternatingSixAlphaOneConjugacyClassPermutation
      alternatingSixAlphaOneConjugacyClassPermutation_symm_symm
      alternatingSixAmbientAtlasTwelvePowerSevenClassValue
      alternatingSixAmbientAtlas12P11ClassValue
      alternatingSixAmbientAtlasTwelvePowerSeven_alphaOne_classValue

private theorem alternatingSixAmbientAtlas12P1Eta_eq_p11Central_pow_five :
    alternatingSixAmbientAtlas12P1Eta =
      alternatingSixAmbientAtlas12P11Central ^ 5 := by
  change
    alternatingSixAmbientAtlas12P1Eta =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 5
  exact alternatingSixAmbientAtlas12P1Eta_eq_powerTwoCentral_pow_five

private theorem alternatingSixAmbientAtlasP11Central_pow_five_sq :
    (alternatingSixAmbientAtlas12P11Central ^ 5) ^ 2 =
      alternatingSixAmbientAtlas12P11Central ^ 4 := by
  change
    (alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 5) ^ 2 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 4
  exact alternatingSixAmbientAtlasPowerTwoCentral_pow_five_sq

private theorem alternatingSixAmbientAtlasP11Central_pow_five_cube :
    (alternatingSixAmbientAtlas12P11Central ^ 5) ^ 3 =
      alternatingSixAmbientAtlas12P11Central ^ 3 := by
  change
    (alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 5) ^ 3 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 3
  exact alternatingSixAmbientAtlasPowerTwoCentral_pow_five_cube

private theorem
    alternatingSixAmbientAtlasP11Central_pow_five_pow_four :
    (alternatingSixAmbientAtlas12P11Central ^ 5) ^ 4 =
      alternatingSixAmbientAtlas12P11Central ^ 2 := by
  change
    (alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 5) ^ 4 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 2
  exact alternatingSixAmbientAtlasPowerTwoCentral_pow_five_pow_four

private theorem
    alternatingSixAmbientAtlasP11Central_pow_five_pow_five :
    (alternatingSixAmbientAtlas12P11Central ^ 5) ^ 5 =
      alternatingSixAmbientAtlas12P11Central := by
  change
    (alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 5) ^ 5 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral
  exact alternatingSixAmbientAtlasPowerTwoCentral_pow_five_pow_five

private theorem alternatingSixAmbientAtlas12P1Alpha_eq_p11Central_mul :
    alternatingSixAmbientAtlas12P1Alpha =
      alternatingSixAmbientAtlas12P11Central ^ 4 *
        alternatingSixAmbientAtlas12P11Alpha := by
  rw [alternatingSixAmbientAtlas12P11Central_pow_four_mul_alpha]
  rfl

private theorem alternatingSixAmbientAtlas12P1Beta_eq_p11Central_mul :
    alternatingSixAmbientAtlas12P1Beta =
      alternatingSixAmbientAtlas12P11Central ^ 2 *
        alternatingSixAmbientAtlas12P11Beta := by
  rw [alternatingSixAmbientAtlas12P11Central_pow_two_mul_beta]
  rfl

private theorem alternatingSixAmbientAtlas12P11Central_pow_seven :
    alternatingSixAmbientAtlas12P11Central ^ 7 =
      alternatingSixAmbientAtlas12P11Central := by
  rw [show 7 = 6 + 1 by norm_num, pow_add,
    alternatingSixAmbientAtlas12P11Central_pow_six, one_mul, pow_one]

private theorem alternatingSixAmbientAtlas12P11Central_pow_nine :
    alternatingSixAmbientAtlas12P11Central ^ 9 =
      alternatingSixAmbientAtlas12P11Central ^ 3 := by
  rw [show 9 = 6 + 3 by norm_num, pow_add,
    alternatingSixAmbientAtlas12P11Central_pow_six, one_mul]

/-- Under alpha-two, the power-one degree-twelve row is transported to the
power-eleven row. -/
theorem alternatingSixAmbientAtlas12P1_alphaTwo_classValue :
    ∀ j : Fin 31,
      alternatingSixAmbientAtlas12P11ClassValue j =
        alternatingSixAmbientAtlas12P1ClassValue
          (alternatingSixAlphaTwoConjugacyClassPermutation.symm j) := by
  intro j
  rw [alternatingSixAlphaTwoConjugacyClassPermutation_symm_eq_vector]
  fin_cases j <;>
    simp [
      alternatingSixAlphaTwoConjugacyClassVector,
      alternatingSixAmbientAtlas12P1ClassValue,
      alternatingSixAmbientAtlas12P11ClassValue,
      alternatingSixAmbientAtlas12P1Eta_eq_p11Central_pow_five,
      alternatingSixAmbientAtlasP11Central_pow_five_sq,
      alternatingSixAmbientAtlasP11Central_pow_five_cube,
      alternatingSixAmbientAtlasP11Central_pow_five_pow_four,
      alternatingSixAmbientAtlasP11Central_pow_five_pow_five,
      alternatingSixAmbientAtlas12P1Alpha_eq_p11Central_mul,
      alternatingSixAmbientAtlas12P1Beta_eq_p11Central_mul
    ] <;>
    ring_nf <;>
    simp [
      alternatingSixAmbientAtlas12P11Central_pow_six,
      alternatingSixAmbientAtlas12P11Central_pow_seven,
      alternatingSixAmbientAtlas12P11Central_pow_eight,
      alternatingSixAmbientAtlas12P11Central_pow_nine
    ]

/-- The reciprocal alpha-two transport sends the power-eleven row to the
power-one row. -/
theorem alternatingSixAmbientAtlas12P11_alphaTwo_classValue :
    ∀ j : Fin 31,
      alternatingSixAmbientAtlas12P1ClassValue j =
        alternatingSixAmbientAtlas12P11ClassValue
          (alternatingSixAlphaTwoConjugacyClassPermutation.symm j) := by
  exact
    reciprocal_classValue_transport
      alternatingSixAlphaTwoConjugacyClassPermutation
      alternatingSixAlphaTwoConjugacyClassPermutation_symm_symm
      alternatingSixAmbientAtlas12P1ClassValue
      alternatingSixAmbientAtlas12P11ClassValue
      alternatingSixAmbientAtlas12P1_alphaTwo_classValue

private theorem
    alternatingSixAmbientAtlasPowerSevenEta_eq_powerTwoCentral_pow_five :
    alternatingSixAmbientAtlasTwelvePowerSevenEta =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 5 := by
  change
    alternatingSixAmbientAtlas12P1Eta =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 5
  exact alternatingSixAmbientAtlas12P1Eta_eq_powerTwoCentral_pow_five

private theorem
    alternatingSixAmbientAtlasPowerSevenAlpha_eq_powerTwoCentral_mul :
    alternatingSixAmbientAtlasTwelvePowerSevenAlpha =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 4 *
        alternatingSixAmbientAtlasTwelvePowerTwoAlpha := by
  rw [
    alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_four_mul_alpha
  ]
  rfl

private theorem
    alternatingSixAmbientAtlasPowerSevenBeta_eq_powerTwoCentral_mul :
    alternatingSixAmbientAtlasTwelvePowerSevenBeta =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 2 *
        alternatingSixAmbientAtlasTwelvePowerTwoBeta := by
  rw [
    alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_two_mul_beta
  ]
  rfl

private theorem alternatingSixAmbientAtlasPowerTwoCentral_pow_seven :
    alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 7 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral := by
  rw [show 7 = 6 + 1 by norm_num, pow_add,
    alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_six,
    one_mul, pow_one]

private theorem alternatingSixAmbientAtlasPowerTwoCentral_pow_nine :
    alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 9 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 3 := by
  rw [show 9 = 6 + 3 by norm_num, pow_add,
    alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_six, one_mul]

/-- Under alpha-two, the power-two degree-twelve row is transported to the
power-seven row. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_alphaTwo_classValue :
    ∀ j : Fin 31,
      alternatingSixAmbientAtlasTwelvePowerSevenClassValue j =
        alternatingSixAmbientAtlasTwelvePowerTwoClassValue
          (alternatingSixAlphaTwoConjugacyClassPermutation.symm j) := by
  intro j
  rw [alternatingSixAlphaTwoConjugacyClassPermutation_symm_eq_vector]
  fin_cases j <;>
    simp [
      alternatingSixAlphaTwoConjugacyClassVector,
      alternatingSixAmbientAtlasTwelvePowerTwoClassValue,
      alternatingSixAmbientAtlasTwelvePowerSevenClassValue,
      alternatingSixAmbientAtlasPowerSevenEta_eq_powerTwoCentral_pow_five,
      alternatingSixAmbientAtlasPowerTwoCentral_pow_five_sq,
      alternatingSixAmbientAtlasPowerTwoCentral_pow_five_cube,
      alternatingSixAmbientAtlasPowerTwoCentral_pow_five_pow_four,
      alternatingSixAmbientAtlasPowerTwoCentral_pow_five_pow_five,
      alternatingSixAmbientAtlasPowerSevenAlpha_eq_powerTwoCentral_mul,
      alternatingSixAmbientAtlasPowerSevenBeta_eq_powerTwoCentral_mul
    ] <;>
    ring_nf <;>
    simp [
      alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_six,
      alternatingSixAmbientAtlasPowerTwoCentral_pow_seven,
      alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_eight,
      alternatingSixAmbientAtlasPowerTwoCentral_pow_nine
    ]

/-- The reciprocal alpha-two transport sends the power-seven row to the
power-two row. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_alphaTwo_classValue :
    ∀ j : Fin 31,
      alternatingSixAmbientAtlasTwelvePowerTwoClassValue j =
        alternatingSixAmbientAtlasTwelvePowerSevenClassValue
          (alternatingSixAlphaTwoConjugacyClassPermutation.symm j) := by
  exact
    reciprocal_classValue_transport
      alternatingSixAlphaTwoConjugacyClassPermutation
      alternatingSixAlphaTwoConjugacyClassPermutation_symm_symm
      alternatingSixAmbientAtlasTwelvePowerTwoClassValue
      alternatingSixAmbientAtlasTwelvePowerSevenClassValue
      alternatingSixAmbientAtlasTwelvePowerTwo_alphaTwo_classValue

end InductiveMcKay
end McKayConjecture
