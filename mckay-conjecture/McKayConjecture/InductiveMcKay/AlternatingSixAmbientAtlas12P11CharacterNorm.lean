/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientInverseClassTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P11ClassValues

/-!
# Character norm for ATLAS degree 12, power 11

The shared inverse-class table reduces the norm to the identity, `ab`, and
`ab²` class families. Independently audited inverse traces identify the two
nontrivial pairings, whose sum is three.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private abbrev atlas12P11Certificate :=
  alternatingSixAmbientAtlas12P11ClassMatrixCertificate

/-- The central scalar has order dividing six. -/
theorem alternatingSixAmbientAtlas12P11Central_pow_six :
    alternatingSixAmbientAtlas12P11Central ^ 6 = 1 := by
  rw [← alternatingSixAmbientAtlas12P11_root_pow_hundred, ← pow_mul]
  rw [show 100 * 6 = 120 * 5 by norm_num, pow_mul,
    alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one, one_pow]

/-- Reduction of the eighth power of the central scalar. -/
theorem alternatingSixAmbientAtlas12P11Central_pow_eight :
    alternatingSixAmbientAtlas12P11Central ^ 8 =
      alternatingSixAmbientAtlas12P11Central ^ 2 := by
  rw [show 8 = 6 + 2 by norm_num, pow_add,
    alternatingSixAmbientAtlas12P11Central_pow_six, one_mul]

/-- Reduction of the tenth power of the central scalar. -/
theorem alternatingSixAmbientAtlas12P11Central_pow_ten :
    alternatingSixAmbientAtlas12P11Central ^ 10 =
      alternatingSixAmbientAtlas12P11Central ^ 4 := by
  rw [show 10 = 6 + 4 by norm_num, pow_add,
    alternatingSixAmbientAtlas12P11Central_pow_six, one_mul]

/-- The independently audited inverse-class value paired with `ab`. -/
def alternatingSixAmbientAtlas12P11AlphaInverse : ℂ :=
  alternatingSixCyclotomicValue
    [(-1, 0), (-1, 4), (1, 8), (1, 12),
      (1, 16), (-1, 28)]

/-- The independently audited inverse-class value paired with `ab²`. -/
def alternatingSixAmbientAtlas12P11BetaInverse : ℂ :=
  alternatingSixCyclotomicValue
    [(-1, 0), (-1, 4), (1, 16), (1, 20)]

/-- The fourth central power sends the `ab` trace to its inverse trace. -/
theorem alternatingSixAmbientAtlas12P11Central_pow_four_mul_alpha :
    alternatingSixAmbientAtlas12P11Central ^ 4 *
        alternatingSixAmbientAtlas12P11Alpha =
      alternatingSixAmbientAtlas12P11AlphaInverse := by
  simp [alternatingSixAmbientAtlas12P11Central,
    alternatingSixAmbientAtlas12P11Eta,
    alternatingSixAmbientAtlas12P11Alpha,
    alternatingSixAmbientAtlas12P11AlphaInverse,
    alternatingSixCyclotomicValue]
  linear_combination
    ((1 : ℂ) + ζ ^ 4 - 2 * ζ ^ 8 + 2 * ζ ^ 12 -
        2 * ζ ^ 16 + 2 * ζ ^ 20 - 5 * ζ ^ 24 +
        3 * ζ ^ 28 - 3 * ζ ^ 32 + 3 * ζ ^ 36 -
        3 * ζ ^ 40 + 4 * ζ ^ 44 - ζ ^ 48 +
        ζ ^ 52 - ζ ^ 56 + ζ ^ 60 - ζ ^ 64) *
      alternatingSixComplexCyclotomicRoot_relation

/-- The second central power sends the `ab²` trace to its inverse trace. -/
theorem alternatingSixAmbientAtlas12P11Central_pow_two_mul_beta :
    alternatingSixAmbientAtlas12P11Central ^ 2 *
        alternatingSixAmbientAtlas12P11Beta =
      alternatingSixAmbientAtlas12P11BetaInverse := by
  simp [alternatingSixAmbientAtlas12P11Central,
    alternatingSixAmbientAtlas12P11Eta,
    alternatingSixAmbientAtlas12P11Beta,
    alternatingSixAmbientAtlas12P11BetaInverse,
    alternatingSixCyclotomicValue]
  linear_combination
    ((2 : ℂ) - ζ ^ 8 + 2 * ζ ^ 12 - 2 * ζ ^ 16 -
        ζ ^ 20 - ζ ^ 32 + ζ ^ 36) *
      alternatingSixComplexCyclotomicRoot_relation

/-- The two independently audited inverse-class pairings sum to three. -/
theorem alternatingSixAmbientAtlas12P11_inversePairings :
    alternatingSixAmbientAtlas12P11Alpha *
          alternatingSixAmbientAtlas12P11AlphaInverse +
        alternatingSixAmbientAtlas12P11Beta *
          alternatingSixAmbientAtlas12P11BetaInverse =
      3 := by
  simp [alternatingSixAmbientAtlas12P11Alpha,
    alternatingSixAmbientAtlas12P11AlphaInverse,
    alternatingSixAmbientAtlas12P11Beta,
    alternatingSixAmbientAtlas12P11BetaInverse,
    alternatingSixCyclotomicValue]
  linear_combination
    (-(4 : ℂ) + ζ ^ 4 - 2 * ζ ^ 8 + ζ ^ 12 + ζ ^ 16) *
      alternatingSixComplexCyclotomicRoot_relation

/-- The two nontrivial inverse-class pairings have combined value three. -/
theorem alternatingSixAmbientAtlas12P11_centralPairings :
    alternatingSixAmbientAtlas12P11Central ^ 4 *
          alternatingSixAmbientAtlas12P11Alpha ^ 2 +
        alternatingSixAmbientAtlas12P11Central ^ 2 *
          alternatingSixAmbientAtlas12P11Beta ^ 2 =
      3 := by
  calc
    _ =
        alternatingSixAmbientAtlas12P11Alpha *
            (alternatingSixAmbientAtlas12P11Central ^ 4 *
              alternatingSixAmbientAtlas12P11Alpha) +
          alternatingSixAmbientAtlas12P11Beta *
            (alternatingSixAmbientAtlas12P11Central ^ 2 *
              alternatingSixAmbientAtlas12P11Beta) := by ring
    _ =
        alternatingSixAmbientAtlas12P11Alpha *
            alternatingSixAmbientAtlas12P11AlphaInverse +
          alternatingSixAmbientAtlas12P11Beta *
            alternatingSixAmbientAtlas12P11BetaInverse := by
      rw [alternatingSixAmbientAtlas12P11Central_pow_four_mul_alpha,
        alternatingSixAmbientAtlas12P11Central_pow_two_mul_beta]
    _ = 3 := alternatingSixAmbientAtlas12P11_inversePairings

/-- Collapse of the 31 summands to the two nonzero word families. -/
theorem alternatingSixAmbientAtlas12P11_weightedSelfPairing_collapsed :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientAtlas12P11ClassValue i *
            alternatingSixAmbientAtlas12P11ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      864 +
        432 *
          (alternatingSixAmbientAtlas12P11Central ^ 4 *
              alternatingSixAmbientAtlas12P11Alpha ^ 2 +
            alternatingSixAmbientAtlas12P11Central ^ 2 *
              alternatingSixAmbientAtlas12P11Beta ^ 2) := by
  simp_rw [alternatingSixSchurInverseClassIndex_eq_table]
  simp [Fin.sum_univ_succ,
    alternatingSixAmbientAtlas12P11ClassValue,
    alternatingSixAmbientInverseClassIndexTable,
    alternatingSixSchurClassSize]
  ring_nf
  rw [alternatingSixAmbientAtlas12P11Central_pow_six,
    alternatingSixAmbientAtlas12P11Central_pow_eight,
    alternatingSixAmbientAtlas12P11Central_pow_ten]
  ring

/-- Exact class-size weighted self-pairing of the power-eleven row. -/
theorem alternatingSixAmbientAtlas12P11_weightedSelfPairing :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientAtlas12P11ClassValue i *
            alternatingSixAmbientAtlas12P11ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      2160 := by
  rw [alternatingSixAmbientAtlas12P11_weightedSelfPairing_collapsed,
    alternatingSixAmbientAtlas12P11_centralPairings]
  norm_num

/-- Complete class-value certificate for the power-eleven representation. -/
def alternatingSixAmbientAtlas12P11ClassCharacterCertificate :
    AlternatingSixAmbientClassCharacterCertificate
      (FDRep.of atlas12P11Certificate.universalCoverRepresentation) where
  value := alternatingSixAmbientAtlas12P11ClassValue
  character_representative :=
    alternatingSixAmbientAtlas12P11_character_classRepresentative
  weightedSelfPairing :=
    alternatingSixAmbientAtlas12P11_weightedSelfPairing

/-- The class calculation proves the unnormalized self-pairing is the group
order. -/
theorem alternatingSixAmbientAtlas12P11_characterSelfPairing :
    characterSelfPairingSum
        (FDRep.of atlas12P11Certificate.universalCoverRepresentation) =
      (Nat.card AlternatingSixUniversalCover : ℂ) :=
  alternatingSixAmbientAtlas12P11ClassCharacterCertificate
    |>.characterSelfPairing

/-- A normalized irreducible character-row certificate. -/
def alternatingSixAmbientAtlas12P11CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientAtlas12P11ClassCharacterCertificate
    |>.characterRowCertificate

end InductiveMcKay
end McKayConjecture
