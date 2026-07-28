/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientInverseClassTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow22ClassValues

/-!
# The class-value norm certificate for ambient row 22

The shared inverse-class permutation reduces the character self-pairing to
thirty-one exact cyclotomic terms.  Their class-size weighted sum is 2160,
using only the quadratic order-six relation for `ζ²⁰`.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row22Certificate :=
  alternatingSixAmbientRow22ClassMatrixCertificate

/-- Quadratic relation for the primitive sixth root used by row 22. -/
theorem alternatingSixAmbientRow22Eta_relation :
    alternatingSixAmbientRow22Eta ^ 2 -
          alternatingSixAmbientRow22Eta +
        1 = 0 := by
  have h :=
    alternatingSixAmbientRow22_orderSixRelation
  rw [show 40 = 20 * 2 by norm_num, pow_mul] at h
  simpa only [alternatingSixAmbientRow22Eta] using h

/-- Exact class-size weighted self-pairing of row 22. -/
theorem alternatingSixAmbientRow22_weightedSelfPairing :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientRow22ClassValue i *
            alternatingSixAmbientRow22ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      2160 := by
  simp_rw [alternatingSixSchurInverseClassIndex_eq_table]
  simp [Fin.sum_univ_succ,
    alternatingSixAmbientRow22ClassValue,
    alternatingSixAmbientInverseClassIndexTable,
    alternatingSixSchurClassSize]
  linear_combination
    (-702 - 8856 * alternatingSixAmbientRow22Eta +
        15525 * alternatingSixAmbientRow22Eta ^ 2 -
        18459 * alternatingSixAmbientRow22Eta ^ 3 +
        26415 * alternatingSixAmbientRow22Eta ^ 4 -
        31536 * alternatingSixAmbientRow22Eta ^ 5 +
        24912 * alternatingSixAmbientRow22Eta ^ 6 -
        12672 * alternatingSixAmbientRow22Eta ^ 7 +
        4104 * alternatingSixAmbientRow22Eta ^ 8 -
        792 * alternatingSixAmbientRow22Eta ^ 9 +
        72 * alternatingSixAmbientRow22Eta ^ 10) *
      alternatingSixAmbientRow22Eta_relation

/-- Complete class-value certificate for the isolated row-22
representation. -/
def alternatingSixAmbientRow22ClassCharacterCertificate :
    AlternatingSixAmbientClassCharacterCertificate
      (FDRep.of row22Certificate.universalCoverRepresentation) where
  value := alternatingSixAmbientRow22ClassValue
  character_representative :=
    alternatingSixAmbientRow22_character_classRepresentative
  weightedSelfPairing :=
    alternatingSixAmbientRow22_weightedSelfPairing

/-- The row-22 class calculation proves its unnormalized character
self-pairing is the order of the universal cover. -/
theorem alternatingSixAmbientRow22_characterSelfPairing :
    characterSelfPairingSum
        (FDRep.of row22Certificate.universalCoverRepresentation) =
      (Nat.card AlternatingSixUniversalCover : ℂ) :=
  alternatingSixAmbientRow22ClassCharacterCertificate.characterSelfPairing

/-- Row 22 as a normalized irreducible character-row certificate. -/
def alternatingSixAmbientRow22CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow22ClassCharacterCertificate
    |>.characterRowCertificate

end InductiveMcKay
end McKayConjecture
