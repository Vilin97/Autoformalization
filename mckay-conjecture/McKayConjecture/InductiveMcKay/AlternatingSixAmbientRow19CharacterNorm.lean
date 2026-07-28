/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassCharacterCertificate
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19ClassValues

/-!
# The class-value norm certificate for ambient row 19

The inverse-class permutation and the class-size weighted sum are both
checked exactly.  The 31 summands first collapse to the two cyclotomic
quantities `α²` and `β²`; their sum is then reduced using the degree-32
cyclotomic relation for the fixed primitive 120th root.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row19Certificate :=
  alternatingSixAmbientRow19ClassMatrixCertificate

/-- Explicit inverse permutation on the thirty-one checked class labels. -/
def alternatingSixAmbientRow19InverseClassIndex : Fin 31 → Fin 31 :=
  ![0, 5, 4, 3, 2, 1, 8, 7, 6, 9, 14, 13, 12, 11, 10, 19,
    18, 17, 16, 15, 20, 23, 22, 21, 26, 25, 24, 27, 28, 29, 30]

/-- The checked coordinate inverse has the displayed class label. -/
theorem alternatingSixSchurInverseClassIndex_eq_row19Table
    (i : Fin 31) :
    alternatingSixSchurInverseClassIndex i =
      alternatingSixAmbientRow19InverseClassIndex i := by
  fin_cases i <;> decide

/-- The two nonintegral-looking base values have combined square norm three. -/
theorem alternatingSixAmbientRow19_alpha_sq_add_beta_sq :
    alternatingSixAmbientRow19Alpha ^ 2 +
        alternatingSixAmbientRow19Beta ^ 2 =
      3 := by
  simp [alternatingSixAmbientRow19Alpha,
    alternatingSixAmbientRow19Beta,
    alternatingSixCyclotomicValue]
  linear_combination
    (-(2 : ℂ) +
          (2 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 4 -
        (4 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 8 +
        (2 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 16 -
        (2 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 20 +
        (2 : ℂ) * alternatingSixComplexCyclotomicRoot ^ 24) *
      alternatingSixComplexCyclotomicRoot_relation

/-- Expansion of the 31-term weighted norm into the two nonzero cyclotomic
base values. -/
theorem alternatingSixAmbientRow19_weightedSelfPairing_collapsed :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientRow19ClassValue i *
            alternatingSixAmbientRow19ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      384 +
        432 * alternatingSixAmbientRow19Alpha ^ 2 +
        432 * alternatingSixAmbientRow19Beta ^ 2 +
        480 := by
  simp_rw [alternatingSixSchurInverseClassIndex_eq_row19Table]
  simp [Fin.sum_univ_succ,
    alternatingSixAmbientRow19ClassValue,
    alternatingSixAmbientRow19InverseClassIndex,
    alternatingSixSchurClassSize]
  ring

/-- Exact class-size weighted self-pairing of row 19. -/
theorem alternatingSixAmbientRow19_weightedSelfPairing :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientRow19ClassValue i *
            alternatingSixAmbientRow19ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      2160 := by
  rw [alternatingSixAmbientRow19_weightedSelfPairing_collapsed]
  calc
    384 +
          432 * alternatingSixAmbientRow19Alpha ^ 2 +
          432 * alternatingSixAmbientRow19Beta ^ 2 +
          480 =
        384 +
          432 *
            (alternatingSixAmbientRow19Alpha ^ 2 +
              alternatingSixAmbientRow19Beta ^ 2) +
          480 := by
      ring
    _ = 2160 := by
      rw [alternatingSixAmbientRow19_alpha_sq_add_beta_sq]
      norm_num

/-- Complete class-value certificate for the isolated row-19
representation. -/
def alternatingSixAmbientRow19ClassCharacterCertificate :
    AlternatingSixAmbientClassCharacterCertificate
      (FDRep.of row19Certificate.universalCoverRepresentation) where
  value := alternatingSixAmbientRow19ClassValue
  character_representative :=
    alternatingSixAmbientRow19_character_classRepresentative
  weightedSelfPairing :=
    alternatingSixAmbientRow19_weightedSelfPairing

/-- The row-19 class calculation proves its unnormalized character
self-pairing is the order of the universal cover. -/
theorem alternatingSixAmbientRow19_characterSelfPairing :
    characterSelfPairingSum
        (FDRep.of row19Certificate.universalCoverRepresentation) =
      (Nat.card AlternatingSixUniversalCover : ℂ) :=
  alternatingSixAmbientRow19ClassCharacterCertificate.characterSelfPairing

/-- Row 19 as a normalized irreducible character-row certificate. -/
def alternatingSixAmbientRow19CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow19ClassCharacterCertificate
    |>.characterRowCertificate

end InductiveMcKay
end McKayConjecture
