/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientInverseClassTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenClassValues

/-!
# Character norm for the ATLAS degree-12 power-seven row

The shared inverse-class table reduces the nonzero terms to the identity,
`ab`, and `ab²` class families. The two nontrivial cyclotomic pairings have
combined value three, giving the exact weighted sum 2160.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private abbrev atlasTwelvePowerSevenCertificate :=
  alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate

/-- The central scalar `η = ζ²⁰` has order dividing six. -/
theorem alternatingSixAmbientAtlasTwelvePowerSevenEta_pow_six :
    alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 6 = 1 := by
  simpa [alternatingSixAmbientAtlasTwelvePowerSevenEta, ← pow_mul] using
    alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one

/-- Reduction of the eighth power of the central scalar. -/
theorem alternatingSixAmbientAtlasTwelvePowerSevenEta_pow_eight :
    alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 8 =
      alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 2 := by
  rw [show 8 = 6 + 2 by norm_num, pow_add,
    alternatingSixAmbientAtlasTwelvePowerSevenEta_pow_six, one_mul]

/-- Reduction of the tenth power of the central scalar. -/
theorem alternatingSixAmbientAtlasTwelvePowerSevenEta_pow_ten :
    alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 10 =
      alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 4 := by
  rw [show 10 = 6 + 4 by norm_num, pow_add,
    alternatingSixAmbientAtlasTwelvePowerSevenEta_pow_six, one_mul]

/-- The two nontrivial inverse-class pairings have combined value three. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_centralPairings :
    alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 4 *
          alternatingSixAmbientAtlasTwelvePowerSevenAlpha ^ 2 +
        alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 2 *
          alternatingSixAmbientAtlasTwelvePowerSevenBeta ^ 2 =
      3 := by
  simp [alternatingSixAmbientAtlasTwelvePowerSevenEta,
    alternatingSixAmbientAtlasTwelvePowerSevenAlpha,
    alternatingSixAmbientAtlasTwelvePowerSevenBeta,
    alternatingSixCyclotomicValue]
  linear_combination
    (
      -(3 : ℂ)
        + (3 : ℂ) * ζ ^ 4
        - (3 : ℂ) * ζ ^ 8
        - (3 : ℂ) * ζ ^ 20
        + (3 : ℂ) * ζ ^ 24
        - (3 : ℂ) * ζ ^ 28
        + ζ ^ 48
        - ζ ^ 52
        + ζ ^ 56
        + ζ ^ 60
        - ζ ^ 64
        + (2 : ℂ) * ζ ^ 68
        + (3 : ℂ) * ζ ^ 80
        - ζ ^ 88
        - ζ ^ 96
        - ζ ^ 100
        + ζ ^ 104
    ) * alternatingSixComplexCyclotomicRoot_relation

/-- Collapse of the 31 summands to the two nonzero word families. -/
theorem
    alternatingSixAmbientAtlasTwelvePowerSeven_weightedSelfPairing_collapsed :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientAtlasTwelvePowerSevenClassValue i *
            alternatingSixAmbientAtlasTwelvePowerSevenClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      864 +
        432 *
          (alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 4 *
              alternatingSixAmbientAtlasTwelvePowerSevenAlpha ^ 2 +
            alternatingSixAmbientAtlasTwelvePowerSevenEta ^ 2 *
              alternatingSixAmbientAtlasTwelvePowerSevenBeta ^ 2) := by
  simp_rw [alternatingSixSchurInverseClassIndex_eq_table]
  simp [Fin.sum_univ_succ,
    alternatingSixAmbientAtlasTwelvePowerSevenClassValue,
    alternatingSixAmbientInverseClassIndexTable,
    alternatingSixSchurClassSize]
  ring_nf
  rw [alternatingSixAmbientAtlasTwelvePowerSevenEta_pow_six,
    alternatingSixAmbientAtlasTwelvePowerSevenEta_pow_eight,
    alternatingSixAmbientAtlasTwelvePowerSevenEta_pow_ten]
  ring

/-- Exact class-size weighted self-pairing of the power-seven row. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_weightedSelfPairing :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientAtlasTwelvePowerSevenClassValue i *
            alternatingSixAmbientAtlasTwelvePowerSevenClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      2160 := by
  rw [
    alternatingSixAmbientAtlasTwelvePowerSeven_weightedSelfPairing_collapsed,
    alternatingSixAmbientAtlasTwelvePowerSeven_centralPairings
  ]
  norm_num

/-- Complete class-value certificate for the power-seven representation. -/
def alternatingSixAmbientAtlasTwelvePowerSevenClassCharacterCertificate :
    AlternatingSixAmbientClassCharacterCertificate
      (FDRep.of
        atlasTwelvePowerSevenCertificate.universalCoverRepresentation) where
  value := alternatingSixAmbientAtlasTwelvePowerSevenClassValue
  character_representative :=
    alternatingSixAmbientAtlasTwelvePowerSeven_character_classRepresentative
  weightedSelfPairing :=
    alternatingSixAmbientAtlasTwelvePowerSeven_weightedSelfPairing

/-- The class calculation proves that the self-pairing is the group order. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_characterSelfPairing :
    characterSelfPairingSum
        (FDRep.of
          atlasTwelvePowerSevenCertificate.universalCoverRepresentation) =
      (Nat.card AlternatingSixUniversalCover : ℂ) :=
  alternatingSixAmbientAtlasTwelvePowerSevenClassCharacterCertificate
    |>.characterSelfPairing

/-- A normalized irreducible character-row certificate. -/
def alternatingSixAmbientAtlasTwelvePowerSevenCharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientAtlasTwelvePowerSevenClassCharacterCertificate
    |>.characterRowCertificate

end InductiveMcKay
end McKayConjecture
