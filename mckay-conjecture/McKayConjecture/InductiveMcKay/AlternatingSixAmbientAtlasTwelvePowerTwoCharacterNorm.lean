/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientInverseClassTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoClassValues

/-!
# Character norm for the ATLAS degree-twelve power-2 row

The shared inverse-class table reduces the norm to the identity, `ab`, and
`ab²` class families.  We separately identify the inverse-class values of the
two nontrivial families and prove that their combined pairing is three.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private abbrev atlasTwelvePowerTwoCertificate :=
  alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate

/-- The central scalar has order dividing six. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_six :
    alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 6 = 1 := by
  rw [← alternatingSixAmbientAtlasTwelvePowerTwo_root_pow_hundred,
    ← pow_mul]
  rw [show 100 * 6 = 120 * 5 by norm_num, pow_mul,
    alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one, one_pow]

/-- Reduction of the eighth power of the central scalar. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_eight :
    alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 8 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 2 := by
  rw [show 8 = 6 + 2 by norm_num, pow_add,
    alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_six, one_mul]

/-- Reduction of the tenth power of the central scalar. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_ten :
    alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 10 =
      alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 4 := by
  rw [show 10 = 6 + 4 by norm_num, pow_add,
    alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_six, one_mul]

/-- The independently audited inverse-class value paired with `ab`. -/
def alternatingSixAmbientAtlasTwelvePowerTwoAlphaInverse : ℂ :=
  alternatingSixCyclotomicValue
    [(1, 0), (1, 4), (-1, 8), (-1, 12), (-1, 16),
      (-1, 20), (1, 28)]

/-- The independently audited inverse-class value paired with `ab²`. -/
def alternatingSixAmbientAtlasTwelvePowerTwoBetaInverse : ℂ :=
  alternatingSixCyclotomicValue [(1, 4), (-1, 16)]

/-- Multiplying the `ab` value by the fourth central power gives its
inverse-class value. -/
theorem
    alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_four_mul_alpha :
    alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 4 *
        alternatingSixAmbientAtlasTwelvePowerTwoAlpha =
      alternatingSixAmbientAtlasTwelvePowerTwoAlphaInverse := by
  simp [alternatingSixAmbientAtlasTwelvePowerTwoCentral,
    alternatingSixAmbientAtlasTwelvePowerTwoEta,
    alternatingSixAmbientAtlasTwelvePowerTwoAlpha,
    alternatingSixAmbientAtlasTwelvePowerTwoAlphaInverse,
    alternatingSixCyclotomicValue]
  linear_combination
    (-(2 : ℂ) + ζ ^ 8 - 2 * ζ ^ 12 + 2 * ζ ^ 16 +
        3 * ζ ^ 20 + 2 * ζ ^ 28 + 3 * ζ ^ 32 -
        3 * ζ ^ 36 - ζ ^ 40 - 3 * ζ ^ 48 - ζ ^ 52 +
        ζ ^ 56 + ζ ^ 68) *
      alternatingSixComplexCyclotomicRoot_relation

/-- Multiplying the `ab²` value by the second central power gives its
inverse-class value. -/
theorem
    alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_two_mul_beta :
    alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 2 *
        alternatingSixAmbientAtlasTwelvePowerTwoBeta =
      alternatingSixAmbientAtlasTwelvePowerTwoBetaInverse := by
  simp [alternatingSixAmbientAtlasTwelvePowerTwoCentral,
    alternatingSixAmbientAtlasTwelvePowerTwoEta,
    alternatingSixAmbientAtlasTwelvePowerTwoBeta,
    alternatingSixAmbientAtlasTwelvePowerTwoBetaInverse,
    alternatingSixCyclotomicValue]
  linear_combination
    (-(1 : ℂ) - ζ ^ 4 + 2 * ζ ^ 8 - 2 * ζ ^ 12 +
        2 * ζ ^ 16 + ζ ^ 24 - ζ ^ 28 + ζ ^ 32 - ζ ^ 36) *
      alternatingSixComplexCyclotomicRoot_relation

/-- The two independently audited inverse-class pairings sum to three. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_inversePairings :
    alternatingSixAmbientAtlasTwelvePowerTwoAlpha *
          alternatingSixAmbientAtlasTwelvePowerTwoAlphaInverse +
        alternatingSixAmbientAtlasTwelvePowerTwoBeta *
          alternatingSixAmbientAtlasTwelvePowerTwoBetaInverse =
      3 := by
  simp [alternatingSixAmbientAtlasTwelvePowerTwoAlpha,
    alternatingSixAmbientAtlasTwelvePowerTwoAlphaInverse,
    alternatingSixAmbientAtlasTwelvePowerTwoBeta,
    alternatingSixAmbientAtlasTwelvePowerTwoBetaInverse,
    alternatingSixCyclotomicValue]
  linear_combination
    (-(4 : ℂ) + ζ ^ 4 - 2 * ζ ^ 8 + ζ ^ 12 + ζ ^ 16) *
      alternatingSixComplexCyclotomicRoot_relation

/-- The two nontrivial inverse-class pairings have combined value three. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_centralPairings :
    alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 4 *
          alternatingSixAmbientAtlasTwelvePowerTwoAlpha ^ 2 +
        alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 2 *
          alternatingSixAmbientAtlasTwelvePowerTwoBeta ^ 2 =
      3 := by
  calc
    _ =
        alternatingSixAmbientAtlasTwelvePowerTwoAlpha *
            (alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 4 *
              alternatingSixAmbientAtlasTwelvePowerTwoAlpha) +
          alternatingSixAmbientAtlasTwelvePowerTwoBeta *
            (alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 2 *
              alternatingSixAmbientAtlasTwelvePowerTwoBeta) := by ring
    _ =
        alternatingSixAmbientAtlasTwelvePowerTwoAlpha *
            alternatingSixAmbientAtlasTwelvePowerTwoAlphaInverse +
          alternatingSixAmbientAtlasTwelvePowerTwoBeta *
            alternatingSixAmbientAtlasTwelvePowerTwoBetaInverse := by
      rw [
        alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_four_mul_alpha,
        alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_two_mul_beta
      ]
    _ = 3 :=
      alternatingSixAmbientAtlasTwelvePowerTwo_inversePairings

/-- Collapse of the 31 summands to the two nonzero word families. -/
theorem
    alternatingSixAmbientAtlasTwelvePowerTwo_weightedSelfPairing_collapsed :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientAtlasTwelvePowerTwoClassValue i *
            alternatingSixAmbientAtlasTwelvePowerTwoClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      864 +
        432 *
          (alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 4 *
              alternatingSixAmbientAtlasTwelvePowerTwoAlpha ^ 2 +
            alternatingSixAmbientAtlasTwelvePowerTwoCentral ^ 2 *
              alternatingSixAmbientAtlasTwelvePowerTwoBeta ^ 2) := by
  simp_rw [alternatingSixSchurInverseClassIndex_eq_table]
  simp [Fin.sum_univ_succ,
    alternatingSixAmbientAtlasTwelvePowerTwoClassValue,
    alternatingSixAmbientInverseClassIndexTable,
    alternatingSixSchurClassSize]
  ring_nf
  rw [alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_six,
    alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_eight,
    alternatingSixAmbientAtlasTwelvePowerTwoCentral_pow_ten]
  ring

/-- Exact class-size weighted self-pairing of the power-2 row. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_weightedSelfPairing :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientAtlasTwelvePowerTwoClassValue i *
            alternatingSixAmbientAtlasTwelvePowerTwoClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      2160 := by
  rw [
    alternatingSixAmbientAtlasTwelvePowerTwo_weightedSelfPairing_collapsed,
    alternatingSixAmbientAtlasTwelvePowerTwo_centralPairings
  ]
  norm_num

/-- Complete class-value certificate for the ATLAS power-2 representation. -/
def alternatingSixAmbientAtlasTwelvePowerTwoClassCharacterCertificate :
    AlternatingSixAmbientClassCharacterCertificate
      (FDRep.of
        atlasTwelvePowerTwoCertificate.universalCoverRepresentation) where
  value := alternatingSixAmbientAtlasTwelvePowerTwoClassValue
  character_representative :=
    alternatingSixAmbientAtlasTwelvePowerTwo_character_classRepresentative
  weightedSelfPairing :=
    alternatingSixAmbientAtlasTwelvePowerTwo_weightedSelfPairing

/-- The class calculation proves the unnormalized self-pairing is the group
order. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_characterSelfPairing :
    characterSelfPairingSum
        (FDRep.of
          atlasTwelvePowerTwoCertificate.universalCoverRepresentation) =
      (Nat.card AlternatingSixUniversalCover : ℂ) :=
  alternatingSixAmbientAtlasTwelvePowerTwoClassCharacterCertificate
    |>.characterSelfPairing

/-- A normalized irreducible character-row certificate. -/
def alternatingSixAmbientAtlasTwelvePowerTwoCharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientAtlasTwelvePowerTwoClassCharacterCertificate
    |>.characterRowCertificate

end InductiveMcKay
end McKayConjecture
