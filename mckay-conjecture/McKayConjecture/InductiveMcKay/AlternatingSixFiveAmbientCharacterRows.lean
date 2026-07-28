/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.NormalizedCharacterCertificate
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientRows

/-!
# Character certificates for the ambient five-local `A₆` rows

Presentation relations turn a generator-matrix calculation into an honest
representation, but do not by themselves prove irreducibility.  This file
states the remaining row interface precisely: a generated normal-form sum
must show that the representation's character has normalized self-pairing
one.

After that check, every row canonically gives a `5'`-degree irreducible
character.  A complete ambient table consists of all twenty-four row
certificates together with a bijectivity proof onto the intrinsic
`PPrimeIrreducibleCharacter` type.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- A relation-checked ambient matrix row together with its kernel-checked
character norm calculation. -/
structure AlternatingSixFiveAmbientCharacterRowCertificate
    (r : AlternatingSixFiveAmbientRow) where
  /-- Exact generator matrices and all presentation relations. -/
  matrixRow : AlternatingSixFiveAmbientMatrixRowCertificate r
  /-- Unnormalized character self-pairing, evaluated on the exact finite
  normal-form enumeration of the canonical cover. -/
  characterSelfPairing :
    characterSelfPairingSum
        (FDRep.of matrixRow.universalCoverRepresentation) =
      (Nat.card AlternatingSixUniversalCover : ℂ)

namespace AlternatingSixFiveAmbientCharacterRowCertificate

variable {r : AlternatingSixFiveAmbientRow}

variable (C : AlternatingSixFiveAmbientCharacterRowCertificate r)

/-- The normalized character-row certificate supplied by an exact ambient
matrix row and its self-pairing calculation. -/
def characterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  CharacterRowCertificate.ofRepresentationCharacterSum
    C.matrixRow.universalCoverRepresentation
    C.characterSelfPairing

@[simp]
theorem characterRowCertificate_representation :
    C.characterRowCertificate.representation =
      FDRep.of C.matrixRow.universalCoverRepresentation :=
  rfl

/-- The coordinate-space dimension of an ambient row is its advertised
table degree. -/
theorem representation_finrank :
    Module.finrank ℂ
        (FDRep.of C.matrixRow.universalCoverRepresentation) =
      r.dimension := by
  simp

/-- Every certified ambient row has degree prime to five. -/
theorem five_not_dvd_representation_finrank :
    ¬5 ∣ Module.finrank ℂ
      (FDRep.of C.matrixRow.universalCoverRepresentation) := by
  rw [C.representation_finrank]
  exact r.five_not_dvd_dimension

/-- The intrinsic `5'`-degree irreducible character afforded by a certified
ambient row. -/
def pPrimeIrreducibleCharacter :
    PPrimeIrreducibleCharacter AlternatingSixUniversalCover 5 :=
  C.characterRowCertificate.pPrimeIrreducibleCharacter
    5 C.five_not_dvd_representation_finrank

@[simp]
theorem pPrimeIrreducibleCharacter_degree :
    C.pPrimeIrreducibleCharacter.1.degree = r.dimension := by
  change C.characterRowCertificate.irreducibleCharacter.degree =
    r.dimension
  rw [CharacterRowCertificate.irreducibleCharacter_degree,
    C.characterRowCertificate_representation,
    C.representation_finrank]

end AlternatingSixFiveAmbientCharacterRowCertificate

/-- Complete, kernel-checked enumeration of the ambient `5'`-character
table.  Bijectivity is separated from the rowwise relation and norm checks so
generated certificates can be audited independently. -/
structure AlternatingSixFiveAmbientPPrimeTableCertificate where
  /-- Certified representation at each of the twenty-four row indices. -/
  row :
    ∀ r : AlternatingSixFiveAmbientRow,
      AlternatingSixFiveAmbientCharacterRowCertificate r
  /-- Distinct row indices afford distinct intrinsic characters. -/
  row_injective :
    Function.Injective
      (fun r ↦ (row r).pPrimeIrreducibleCharacter)
  /-- Every intrinsic `5'`-degree irreducible character occurs in the
  indexed list. -/
  row_surjective :
    Function.Surjective
      (fun r ↦ (row r).pPrimeIrreducibleCharacter)

namespace AlternatingSixFiveAmbientPPrimeTableCertificate

variable (T : AlternatingSixFiveAmbientPPrimeTableCertificate)

/-- The exact ambient `5'`-character enumeration furnished by a completed
table certificate. -/
def pPrimeIrreducibleCharacterEquiv :
    AlternatingSixFiveAmbientRow ≃
      PPrimeIrreducibleCharacter AlternatingSixUniversalCover 5 :=
  Equiv.ofBijective
    (fun r ↦ (T.row r).pPrimeIrreducibleCharacter)
    ⟨T.row_injective, T.row_surjective⟩

@[simp]
theorem pPrimeIrreducibleCharacterEquiv_apply
    (r : AlternatingSixFiveAmbientRow) :
    T.pPrimeIrreducibleCharacterEquiv r =
      (T.row r).pPrimeIrreducibleCharacter :=
  rfl

end AlternatingSixFiveAmbientPPrimeTableCertificate
end InductiveMcKay
end McKayConjecture
