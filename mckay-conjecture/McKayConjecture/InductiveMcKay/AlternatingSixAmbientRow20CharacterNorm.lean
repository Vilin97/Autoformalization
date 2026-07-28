/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientInverseClassTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow20ClassValues

/-!
# The class-value norm certificate for ambient row 20

All row-20 values are rational integers. The exact weighted norm therefore
reduces directly to the checked inverse-class and class-size tables.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row20Certificate :=
  alternatingSixAmbientRow20ClassMatrixCertificate

/-- Exact class-size weighted self-pairing of row 20. -/
theorem alternatingSixAmbientRow20_weightedSelfPairing :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientRow20ClassValue i *
            alternatingSixAmbientRow20ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      2160 := by
  simp_rw [alternatingSixSchurInverseClassIndex_eq_table]
  simp [Fin.sum_univ_succ,
    alternatingSixAmbientRow20ClassValue,
    alternatingSixAmbientInverseClassIndexTable,
    alternatingSixSchurClassSize]
  ring

/-- Complete class-value certificate for the isolated row-20
representation. -/
def alternatingSixAmbientRow20ClassCharacterCertificate :
    AlternatingSixAmbientClassCharacterCertificate
      (FDRep.of row20Certificate.universalCoverRepresentation) where
  value := alternatingSixAmbientRow20ClassValue
  character_representative :=
    alternatingSixAmbientRow20_character_classRepresentative
  weightedSelfPairing :=
    alternatingSixAmbientRow20_weightedSelfPairing

/-- The row-20 class calculation proves its unnormalized character
self-pairing is the order of the universal cover. -/
theorem alternatingSixAmbientRow20_characterSelfPairing :
    characterSelfPairingSum
        (FDRep.of row20Certificate.universalCoverRepresentation) =
      (Nat.card AlternatingSixUniversalCover : ℂ) :=
  alternatingSixAmbientRow20ClassCharacterCertificate.characterSelfPairing

/-- Row 20 as a normalized irreducible character-row certificate. -/
def alternatingSixAmbientRow20CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow20ClassCharacterCertificate
    |>.characterRowCertificate

end InductiveMcKay
end McKayConjecture
