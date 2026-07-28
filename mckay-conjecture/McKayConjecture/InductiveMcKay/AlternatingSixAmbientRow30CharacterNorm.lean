/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientInverseClassTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow30ClassValues

/-!
# The class-value norm certificate for ambient row 30

The shared inverse-class permutation reduces the character self-pairing to
thirty-one exact cyclotomic terms.  Their class-size weighted sum is 2160,
using only the quadratic order-six relation for `ζ²⁰`.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row30Certificate :=
  alternatingSixAmbientRow30ClassMatrixCertificate

/-- Quadratic relation for the primitive sixth root used by row 30. -/
theorem alternatingSixAmbientRow30Eta_relation :
    alternatingSixAmbientRow30Eta ^ 2 -
          alternatingSixAmbientRow30Eta +
        1 = 0 := by
  have h :=
    alternatingSixAmbientRow30_orderSixRelation
  rw [show 40 = 20 * 2 by norm_num, pow_mul] at h
  simpa only [alternatingSixAmbientRow30Eta] using h

/-- Exact class-size weighted self-pairing of row 30. -/
theorem alternatingSixAmbientRow30_weightedSelfPairing :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientRow30ClassValue i *
            alternatingSixAmbientRow30ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      2160 := by
  simp_rw [alternatingSixSchurInverseClassIndex_eq_table]
  simp [Fin.sum_univ_succ,
    alternatingSixAmbientRow30ClassValue,
    alternatingSixAmbientInverseClassIndexTable,
    alternatingSixSchurClassSize]
  linear_combination
    (-1845 - 1845 * alternatingSixAmbientRow30Eta +
        270 * alternatingSixAmbientRow30Eta ^ 2 +
        1575 * alternatingSixAmbientRow30Eta ^ 3 +
        1575 * alternatingSixAmbientRow30Eta ^ 4) *
      alternatingSixAmbientRow30Eta_relation

/-- Complete class-value certificate for the isolated row-30
representation. -/
def alternatingSixAmbientRow30ClassCharacterCertificate :
    AlternatingSixAmbientClassCharacterCertificate
      (FDRep.of row30Certificate.universalCoverRepresentation) where
  value := alternatingSixAmbientRow30ClassValue
  character_representative :=
    alternatingSixAmbientRow30_character_classRepresentative
  weightedSelfPairing :=
    alternatingSixAmbientRow30_weightedSelfPairing

/-- The row-30 class calculation proves its unnormalized character
self-pairing is the order of the universal cover. -/
theorem alternatingSixAmbientRow30_characterSelfPairing :
    characterSelfPairingSum
        (FDRep.of row30Certificate.universalCoverRepresentation) =
      (Nat.card AlternatingSixUniversalCover : ℂ) :=
  alternatingSixAmbientRow30ClassCharacterCertificate.characterSelfPairing

/-- Row 30 as a normalized irreducible character-row certificate. -/
def alternatingSixAmbientRow30CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow30ClassCharacterCertificate
    |>.characterRowCertificate

end InductiveMcKay
end McKayConjecture
