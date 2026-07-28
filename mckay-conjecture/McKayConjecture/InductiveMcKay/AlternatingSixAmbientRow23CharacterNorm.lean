/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientInverseClassTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow23ClassValues

/-!
# The class-value norm certificate for ambient row 23

All row-23 values are rational integers. The exact weighted norm therefore
reduces directly to the shared inverse-class and class-size tables.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row23Certificate :=
  alternatingSixAmbientRow23ClassMatrixCertificate

/-- Exact class-size weighted self-pairing of row 23. -/
theorem alternatingSixAmbientRow23_weightedSelfPairing :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (alternatingSixAmbientRow23ClassValue i *
            alternatingSixAmbientRow23ClassValue
              (alternatingSixSchurInverseClassIndex i))) =
      2160 := by
  simp_rw [alternatingSixSchurInverseClassIndex_eq_table]
  simp [Fin.sum_univ_succ,
    alternatingSixAmbientRow23ClassValue,
    alternatingSixAmbientInverseClassIndexTable,
    alternatingSixSchurClassSize]
  ring

/-- Complete class-value certificate for the isolated row-23
representation. -/
def alternatingSixAmbientRow23ClassCharacterCertificate :
    AlternatingSixAmbientClassCharacterCertificate
      (FDRep.of row23Certificate.universalCoverRepresentation) where
  value := alternatingSixAmbientRow23ClassValue
  character_representative :=
    alternatingSixAmbientRow23_character_classRepresentative
  weightedSelfPairing :=
    alternatingSixAmbientRow23_weightedSelfPairing

/-- The row-23 class calculation proves its unnormalized character
self-pairing is the order of the universal cover. -/
theorem alternatingSixAmbientRow23_characterSelfPairing :
    characterSelfPairingSum
        (FDRep.of row23Certificate.universalCoverRepresentation) =
      (Nat.card AlternatingSixUniversalCover : ℂ) :=
  alternatingSixAmbientRow23ClassCharacterCertificate.characterSelfPairing

/-- Row 23 as a normalized irreducible character-row certificate. -/
def alternatingSixAmbientRow23CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow23ClassCharacterCertificate
    |>.characterRowCertificate

end InductiveMcKay
end McKayConjecture
