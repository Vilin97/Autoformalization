/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientInverseClassTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P1ClassValues

/-!
# Character norm for ATLAS degree 12, power 1

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

private abbrev atlas12P1Certificate :=
  alternatingSixAmbientAtlas12P1ClassMatrixCertificate

/-- The central scalar `η = ζ²⁰` has order dividing six. -/
theorem alternatingSixAmbientAtlas12P1Eta_pow_six :
    alternatingSixAmbientAtlas12P1Eta ^ 6 = 1 := by
  simpa [alternatingSixAmbientAtlas12P1Eta, ← pow_mul] using
    alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one

/-- Reduction of the eighth power of the central scalar. -/
theorem alternatingSixAmbientAtlas12P1Eta_pow_eight :
    alternatingSixAmbientAtlas12P1Eta ^ 8 =
      alternatingSixAmbientAtlas12P1Eta ^ 2 := by
  rw [show 8 = 6 + 2 by norm_num, pow_add,
    alternatingSixAmbientAtlas12P1Eta_pow_six, one_mul]

/-- Reduction of the tenth power of the central scalar. -/
theorem alternatingSixAmbientAtlas12P1Eta_pow_ten :
    alternatingSixAmbientAtlas12P1Eta ^ 10 =
      alternatingSixAmbientAtlas12P1Eta ^ 4 := by
  rw [show 10 = 6 + 4 by norm_num, pow_add,
    alternatingSixAmbientAtlas12P1Eta_pow_six, one_mul]

/-- The two nontrivial inverse-class pairings have combined value three. -/
theorem alternatingSixAmbientAtlas12P1_centralPairings :
    alternatingSixAmbientAtlas12P1Eta ^ 4 *
          alternatingSixAmbientAtlas12P1Alpha ^ 2 +
        alternatingSixAmbientAtlas12P1Eta ^ 2 *
          alternatingSixAmbientAtlas12P1Beta ^ 2 =
      3 := by
  simp [alternatingSixAmbientAtlas12P1Eta,
    alternatingSixAmbientAtlas12P1Alpha,
    alternatingSixAmbientAtlas12P1Beta,
    alternatingSixCyclotomicValue]
  linear_combination
    (-(3 : ℂ) + 3 * ζ ^ 4 - 3 * ζ ^ 8 -
        3 * ζ ^ 20 + 3 * ζ ^ 24 - 3 * ζ ^ 28 +
        ζ ^ 40 + ζ ^ 44 + ζ ^ 52 - ζ ^ 56 +
        2 * ζ ^ 60 - 2 * ζ ^ 64 + ζ ^ 68 +
        2 * ζ ^ 80 - ζ ^ 84 - 2 * ζ ^ 92 +
        ζ ^ 96 - ζ ^ 100 + ζ ^ 104) *
      alternatingSixComplexCyclotomicRoot_relation

/-- Collapse of the 31 summands to the two nonzero word families. -/
theorem alternatingSixAmbientAtlas12P1_weightedSelfPairing_collapsed :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientAtlas12P1ClassValue i *
            alternatingSixAmbientAtlas12P1ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      864 +
        432 *
          (alternatingSixAmbientAtlas12P1Eta ^ 4 *
              alternatingSixAmbientAtlas12P1Alpha ^ 2 +
            alternatingSixAmbientAtlas12P1Eta ^ 2 *
              alternatingSixAmbientAtlas12P1Beta ^ 2) := by
  simp_rw [alternatingSixSchurInverseClassIndex_eq_table]
  simp [Fin.sum_univ_succ,
    alternatingSixAmbientAtlas12P1ClassValue,
    alternatingSixAmbientInverseClassIndexTable,
    alternatingSixSchurClassSize]
  ring_nf
  rw [alternatingSixAmbientAtlas12P1Eta_pow_six,
    alternatingSixAmbientAtlas12P1Eta_pow_eight,
    alternatingSixAmbientAtlas12P1Eta_pow_ten]
  ring

/-- Exact class-size weighted self-pairing of the power-one row. -/
theorem alternatingSixAmbientAtlas12P1_weightedSelfPairing :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientAtlas12P1ClassValue i *
            alternatingSixAmbientAtlas12P1ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      2160 := by
  rw [alternatingSixAmbientAtlas12P1_weightedSelfPairing_collapsed,
    alternatingSixAmbientAtlas12P1_centralPairings]
  norm_num

/-- Complete class-value certificate for the power-one representation. -/
def alternatingSixAmbientAtlas12P1ClassCharacterCertificate :
    AlternatingSixAmbientClassCharacterCertificate
      (FDRep.of atlas12P1Certificate.universalCoverRepresentation) where
  value := alternatingSixAmbientAtlas12P1ClassValue
  character_representative :=
    alternatingSixAmbientAtlas12P1_character_classRepresentative
  weightedSelfPairing :=
    alternatingSixAmbientAtlas12P1_weightedSelfPairing

/-- The class calculation proves the unnormalized self-pairing is the group
order. -/
theorem alternatingSixAmbientAtlas12P1_characterSelfPairing :
    characterSelfPairingSum
        (FDRep.of atlas12P1Certificate.universalCoverRepresentation) =
      (Nat.card AlternatingSixUniversalCover : ℂ) :=
  alternatingSixAmbientAtlas12P1ClassCharacterCertificate
    |>.characterSelfPairing

/-- A normalized irreducible character-row certificate. -/
def alternatingSixAmbientAtlas12P1CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientAtlas12P1ClassCharacterCertificate
    |>.characterRowCertificate

end InductiveMcKay
end McKayConjecture
