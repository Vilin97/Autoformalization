/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientCharacterNormByClasses

/-!
# Ordinary ambient character certificates from class values

An exact matrix row already supplies an honest representation of the
canonical sixfold cover.  To certify irreducibility it is enough to give its
thirty-one values at the checked class representatives and verify the
class-size weighted norm.  This interface is substantially smaller than a
full symbolic commutant calculation for the larger matrix rows.
-/

noncomputable section

open scoped BigOperators
open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The class label of the inverse of a checked representative. -/
def alternatingSixSchurInverseClassIndex (i : Fin 31) : Fin 31 :=
  alternatingSixSchurClassIndex
    (alternatingSixSchurClassRepresentative i)⁻¹

/-- Exact values and the weighted norm certificate for one representation
of the canonical cover. -/
structure AlternatingSixAmbientClassCharacterCertificate
    (V : FDRep ℂ AlternatingSixUniversalCover) where
  /-- Advertised character value at each checked class representative. -/
  value : Fin 31 → ℂ
  /-- The advertised values are the actual representation traces. -/
  character_representative :
    ∀ i : Fin 31,
      V.character
          (alternatingSixSchurCoordinatesEquivUniversalCover
            (alternatingSixSchurClassRepresentative i)) =
        value i
  /-- The class-size weighted self-pairing is the group order. -/
  weightedSelfPairing :
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (value i * value (alternatingSixSchurInverseClassIndex i))) =
      2160

namespace AlternatingSixAmbientClassCharacterCertificate

variable {V : FDRep ℂ AlternatingSixUniversalCover}

/-- The actual character value at the inverse of a checked representative is
the advertised value on the inverse class. -/
theorem character_inverseRepresentative
    (C : AlternatingSixAmbientClassCharacterCertificate V)
    (i : Fin 31) :
    V.character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative i))⁻¹ =
      C.value (alternatingSixSchurInverseClassIndex i) := by
  rw [← map_inv]
  rw [
    alternatingSixAmbient_character_coordinate_eq_representative,
    C.character_representative
  ]
  rfl

/-- The finite class-value data proves the exact unnormalized character norm. -/
theorem characterSelfPairing
    (C : AlternatingSixAmbientClassCharacterCertificate V) :
    characterSelfPairingSum V =
      (Nat.card AlternatingSixUniversalCover : ℂ) := by
  rw [alternatingSixAmbient_characterSelfPairingSum_eq_classSum]
  calc
    (∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (V.character
              (alternatingSixSchurCoordinatesEquivUniversalCover
                (alternatingSixSchurClassRepresentative i)) *
            V.character
              (alternatingSixSchurCoordinatesEquivUniversalCover
                (alternatingSixSchurClassRepresentative i))⁻¹)) =
        ∑ i : Fin 31,
          (alternatingSixSchurClassSize i : ℂ) *
            (C.value i *
              C.value (alternatingSixSchurInverseClassIndex i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [C.character_representative i,
        C.character_inverseRepresentative i]
    _ = 2160 := C.weightedSelfPairing
    _ = (Nat.card AlternatingSixUniversalCover : ℂ) := by
      have hcard :
        Nat.card AlternatingSixUniversalCover =
            2160 := by
        calc
          Nat.card AlternatingSixUniversalCover =
              Nat.card AlternatingSixSchurCoordinates :=
            Nat.card_congr
              alternatingSixSchurCoordinatesEquivUniversalCover.toEquiv.symm
          _ = Nat.card (Fin 36 × (Fin 10 × Fin 6)) :=
            Nat.card_congr
              alternatingSixSchurClassCountCoordinatesEquiv
          _ = 2160 := by simp
      simpa using
        congrArg (fun n : Nat ↦ (n : ℂ)) hcard.symm

/-- Package the class-value norm as a normalized irreducible-character row. -/
def characterRowCertificate
    (C : AlternatingSixAmbientClassCharacterCertificate V) :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  CharacterRowCertificate.ofCharacterSum V C.characterSelfPairing

@[simp]
theorem characterRowCertificate_representation
    (C : AlternatingSixAmbientClassCharacterCertificate V) :
    C.characterRowCertificate.representation = V :=
  rfl

end AlternatingSixAmbientClassCharacterCertificate
end InductiveMcKay
end McKayConjecture
