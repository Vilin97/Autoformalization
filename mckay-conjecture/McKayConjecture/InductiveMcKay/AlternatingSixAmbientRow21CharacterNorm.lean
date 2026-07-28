/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassCharacterCertificate
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow21ClassValues

/-!
# The class-value norm certificate for ambient row 21

The checked inverse-class permutation reduces the character self-pairing to
thirty-one exact cyclotomic terms.  Their class-size weighted sum is 2160,
using only the quadratic order-six relation for `ζ²⁰`.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row21Certificate :=
  alternatingSixAmbientRow21ClassMatrixCertificate

/-- Explicit inverse permutation on the checked class labels. -/
def alternatingSixAmbientRow21InverseClassIndex : Fin 31 → Fin 31 :=
  ![0, 5, 4, 3, 2, 1, 8, 7, 6, 9, 14, 13, 12, 11, 10, 19,
    18, 17, 16, 15, 20, 23, 22, 21, 26, 25, 24, 27, 28, 29, 30]

/-- The coordinate inverse has the displayed row-21 inverse-class label. -/
theorem alternatingSixSchurInverseClassIndex_eq_row21Table
    (i : Fin 31) :
    alternatingSixSchurInverseClassIndex i =
      alternatingSixAmbientRow21InverseClassIndex i := by
  fin_cases i <;> decide

/-- Quadratic relation for the primitive sixth root used by row 21. -/
theorem alternatingSixAmbientRow21Eta_relation :
    alternatingSixAmbientRow21Eta ^ 2 -
          alternatingSixAmbientRow21Eta +
        1 = 0 := by
  have h :=
    alternatingSixAmbientRow21_orderSixRelation
  rw [show 40 = 20 * 2 by norm_num, pow_mul] at h
  simpa only [alternatingSixAmbientRow21Eta] using h

/-- Exact class-size weighted self-pairing of row 21. -/
theorem alternatingSixAmbientRow21_weightedSelfPairing :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientRow21ClassValue i *
            alternatingSixAmbientRow21ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      2160 := by
  simp_rw [alternatingSixSchurInverseClassIndex_eq_row21Table]
  simp [Fin.sum_univ_succ,
    alternatingSixAmbientRow21ClassValue,
    alternatingSixAmbientRow21InverseClassIndex,
    alternatingSixSchurClassSize]
  linear_combination
    (-1989 - 1989 * alternatingSixAmbientRow21Eta +
        486 * alternatingSixAmbientRow21Eta ^ 2 +
        1503 * alternatingSixAmbientRow21Eta ^ 3 +
        1503 * alternatingSixAmbientRow21Eta ^ 4 -
        288 * alternatingSixAmbientRow21Eta ^ 6 -
        288 * alternatingSixAmbientRow21Eta ^ 7 +
        216 * alternatingSixAmbientRow21Eta ^ 8 +
        72 * alternatingSixAmbientRow21Eta ^ 9 +
        72 * alternatingSixAmbientRow21Eta ^ 10) *
      alternatingSixAmbientRow21Eta_relation

/-- Complete class-value certificate for the isolated row-21
representation. -/
def alternatingSixAmbientRow21ClassCharacterCertificate :
    AlternatingSixAmbientClassCharacterCertificate
      (FDRep.of row21Certificate.universalCoverRepresentation) where
  value := alternatingSixAmbientRow21ClassValue
  character_representative :=
    alternatingSixAmbientRow21_character_classRepresentative
  weightedSelfPairing :=
    alternatingSixAmbientRow21_weightedSelfPairing

/-- The row-21 class calculation proves its unnormalized character
self-pairing is the order of the universal cover. -/
theorem alternatingSixAmbientRow21_characterSelfPairing :
    characterSelfPairingSum
        (FDRep.of row21Certificate.universalCoverRepresentation) =
      (Nat.card AlternatingSixUniversalCover : ℂ) :=
  alternatingSixAmbientRow21ClassCharacterCertificate.characterSelfPairing

/-- Row 21 as a normalized irreducible character-row certificate. -/
def alternatingSixAmbientRow21CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow21ClassCharacterCertificate
    |>.characterRowCertificate

end InductiveMcKay
end McKayConjecture
