/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientInverseClassTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow31ClassValues

/-!
# The class-value norm certificate for ambient row 31

The shared inverse-class permutation reduces the character self-pairing to
thirty-one exact cyclotomic terms. Their class-size weighted sum is 2160,
using only the quadratic order-six relation for `ζ²⁰`.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row31Certificate :=
  alternatingSixAmbientRow31ClassMatrixCertificate

/-- Quadratic relation for the primitive sixth root used by row 31. -/
theorem alternatingSixAmbientRow31Eta_relation :
    alternatingSixAmbientRow31Eta ^ 2 -
          alternatingSixAmbientRow31Eta +
        1 = 0 := by
  have h :=
    alternatingSixAmbientRow31_orderSixRelation
  rw [show 40 = 20 * 2 by norm_num, pow_mul] at h
  simpa only [alternatingSixAmbientRow31Eta] using h

/-- Exact class-size weighted self-pairing of row 31. -/
theorem alternatingSixAmbientRow31_weightedSelfPairing :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientRow31ClassValue i *
            alternatingSixAmbientRow31ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      2160 := by
  simp_rw [alternatingSixSchurInverseClassIndex_eq_table]
  simp [Fin.sum_univ_succ,
    alternatingSixAmbientRow31ClassValue,
    alternatingSixAmbientInverseClassIndexTable,
    alternatingSixSchurClassSize]
  linear_combination
    (-270 - 9720 * alternatingSixAmbientRow31Eta +
        14445 * alternatingSixAmbientRow31Eta ^ 2 -
        7875 * alternatingSixAmbientRow31Eta ^ 3 +
        1575 * alternatingSixAmbientRow31Eta ^ 4) *
      alternatingSixAmbientRow31Eta_relation

/-- Complete class-value certificate for the isolated row-31
representation. -/
def alternatingSixAmbientRow31ClassCharacterCertificate :
    AlternatingSixAmbientClassCharacterCertificate
      (FDRep.of row31Certificate.universalCoverRepresentation) where
  value := alternatingSixAmbientRow31ClassValue
  character_representative :=
    alternatingSixAmbientRow31_character_classRepresentative
  weightedSelfPairing :=
    alternatingSixAmbientRow31_weightedSelfPairing

/-- The row-31 class calculation proves its unnormalized character
self-pairing is the order of the universal cover. -/
theorem alternatingSixAmbientRow31_characterSelfPairing :
    characterSelfPairingSum
        (FDRep.of row31Certificate.universalCoverRepresentation) =
      (Nat.card AlternatingSixUniversalCover : ℂ) :=
  alternatingSixAmbientRow31ClassCharacterCertificate.characterSelfPairing

/-- Row 31 as a normalized irreducible character-row certificate. -/
def alternatingSixAmbientRow31CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow31ClassCharacterCertificate
    |>.characterRowCertificate

end InductiveMcKay
end McKayConjecture
