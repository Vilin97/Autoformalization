/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FiniteCharacterTableCertificate
import McKayConjecture.Character.SimpleCharacterRowCertificate
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryRows

/-!
# Kernel-checked ordinary character-table interface for the sixfold `A₆` cover

Presentation relations produce honest representations.  Each row additionally
needs an exact normalized self-pairing calculation.  Pairwise distinction and
the independently checked number of conjugacy classes then give a complete
ordinary table, whose `p'` rows may be filtered for any prime.
-/

noncomputable section

open scoped BigOperators
open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- One ordinary ambient matrix row together with its exact character norm. -/
structure AlternatingSixAmbientOrdinaryCharacterRowCertificate
    (row : AlternatingSixAmbientOrdinaryRow) where
  /-- Exact matrices and all presentation relations. -/
  matrixRow : AlternatingSixAmbientOrdinaryMatrixRowCertificate row
  /-- The unnormalized self-pairing over all 2160 canonical-cover elements. -/
  characterSelfPairing :
    characterSelfPairingSum
        (FDRep.of matrixRow.universalCoverRepresentation) =
      (Nat.card AlternatingSixUniversalCover : ℂ)

namespace AlternatingSixAmbientOrdinaryCharacterRowCertificate

variable {row : AlternatingSixAmbientOrdinaryRow}
variable (C : AlternatingSixAmbientOrdinaryCharacterRowCertificate row)

/-- Package a relation-checked matrix row whose transported representation is
already known to be simple. -/
def ofSimple
    (matrixRow : AlternatingSixAmbientOrdinaryMatrixRowCertificate row)
    [Simple (FDRep.of matrixRow.universalCoverRepresentation)] :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate row where
  matrixRow := matrixRow
  characterSelfPairing := by
    letI : Fintype AlternatingSixUniversalCover := Fintype.ofFinite _
    change
      (∑ g : AlternatingSixUniversalCover,
          (FDRep.of matrixRow.universalCoverRepresentation).character g *
            (FDRep.of matrixRow.universalCoverRepresentation).character g⁻¹) =
        (Nat.card AlternatingSixUniversalCover : ℂ)
    exact
      (FDRep.simple_iff_char_is_norm_one
        (FDRep.of matrixRow.universalCoverRepresentation)).mp inferInstance

/-- The normalized irreducible-character row supplied by the exact norm. -/
def characterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  CharacterRowCertificate.ofRepresentationCharacterSum
    C.matrixRow.universalCoverRepresentation
    C.characterSelfPairing

@[simp]
theorem representation_finrank :
    Module.finrank ℂ C.characterRowCertificate.representation =
      row.dimension := by
  change Module.finrank ℂ (Fin row.dimension → ℂ) = row.dimension
  simp

end AlternatingSixAmbientOrdinaryCharacterRowCertificate

/-- A complete kernel-checked ordinary character table for the canonical
sixfold cover. -/
structure AlternatingSixAmbientOrdinaryCharacterTableCertificate where
  /-- The normalized irreducible-character certificate at every row. -/
  row :
    ∀ row : AlternatingSixAmbientOrdinaryRow,
      AlternatingSixAmbientOrdinaryCharacterRowCertificate row
  /-- Distinct generated rows afford distinct irreducible characters. -/
  row_injective :
    Function.Injective
      (fun index ↦
        (row index).characterRowCertificate.irreducibleCharacter)
  /-- The canonical cover has exactly thirty-one conjugacy classes. -/
  conjugacyClassCount :
    Nat.card (ConjClasses AlternatingSixUniversalCover) = 31

namespace AlternatingSixAmbientOrdinaryCharacterTableCertificate

variable (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)

/-- Forget the generated presentation and retain the generic complete-table
certificate. -/
def toFiniteCharacterTableCertificate :
    FiniteCharacterTableCertificate
      AlternatingSixUniversalCover
      AlternatingSixAmbientOrdinaryRow where
  row row := (T.row row).characterRowCertificate
  row_injective := T.row_injective
  row_count := by
    rw [AlternatingSixAmbientOrdinaryRow.natCard,
      T.conjugacyClassCount]

/-- Complete ambient `p'`-row enumeration obtained non-circularly by filtering
the thirty-one-row ordinary table. -/
def pPrimeIrreducibleCharacterEquiv
    (p : ℕ) :
    (T.toFiniteCharacterTableCertificate.PPrimeRow p) ≃
      PPrimeIrreducibleCharacter AlternatingSixUniversalCover p :=
  T.toFiniteCharacterTableCertificate.pPrimeIrreducibleCharacterEquiv p

end AlternatingSixAmbientOrdinaryCharacterTableCertificate
end InductiveMcKay
end McKayConjecture
