/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CharacterRowSeparation
import McKayConjecture.Character.FiniteCharacterTableCertificate
import McKayConjecture.Character.SimpleCharacterRowCertificate
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryRows
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientTwoGeneratorCharacterRow

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
  /-- The four central relator scalars agree with the advertised scalar
  pattern of this named ordinary row. -/
  relatorScalar_eq_scalarPattern :
    ∀ i : Fin 4,
      matrixRow.relatorScalar i =
        alternatingSixComplexCyclotomicRoot ^
          row.scalarPattern.exponent i
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
    (relatorScalar_eq_scalarPattern :
      ∀ i : Fin 4,
        matrixRow.relatorScalar i =
          alternatingSixComplexCyclotomicRoot ^
            row.scalarPattern.exponent i)
    [Simple (FDRep.of matrixRow.universalCoverRepresentation)] :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate row where
  matrixRow := matrixRow
  relatorScalar_eq_scalarPattern :=
    relatorScalar_eq_scalarPattern
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

/-- The irreducible character attached to a named row has the advertised
value at the canonical central generator. -/
theorem irreducibleCharacter_values_centralGenerator :
    C.characterRowCertificate.irreducibleCharacter.values
        alternatingSixAmbientCanonicalCentralGenerator =
      (row.dimension : ℂ) *
        alternatingSixComplexCyclotomicRoot ^
          row.scalarPattern.exponent 0 := by
  letI : Nonempty (Fin row.dimension) :=
    Fin.pos_iff_nonempty.mp row.dimension_pos
  rw [C.characterRowCertificate.irreducibleCharacter_values_apply]
  change
    (FDRep.of C.matrixRow.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalCentralGenerator =
      _
  rw [
    C.matrixRow.universalCoverRepresentation_character_centralGenerator_eq,
    C.relatorScalar_eq_scalarPattern
  ]
  simp

/-- Equal packaged characters have equal matrix dimensions. -/
theorem dimension_eq_of_irreducibleCharacter_eq
    {row' : AlternatingSixAmbientOrdinaryRow}
    (D : AlternatingSixAmbientOrdinaryCharacterRowCertificate row')
    (h :
      C.characterRowCertificate.irreducibleCharacter =
        D.characterRowCertificate.irreducibleCharacter) :
    row.dimension = row'.dimension := by
  calc
    row.dimension =
        C.characterRowCertificate.irreducibleCharacter.degree := by
      rw [C.characterRowCertificate.irreducibleCharacter_degree,
        C.representation_finrank]
    _ = D.characterRowCertificate.irreducibleCharacter.degree :=
      congrArg IrreducibleCharacter.degree h
    _ = row'.dimension := by
      rw [D.characterRowCertificate.irreducibleCharacter_degree,
        D.representation_finrank]

/-- Equal packaged characters have the same advertised central-scalar
pattern. -/
theorem scalarPattern_eq_of_irreducibleCharacter_eq
    {row' : AlternatingSixAmbientOrdinaryRow}
    (D : AlternatingSixAmbientOrdinaryCharacterRowCertificate row')
    (h :
      C.characterRowCertificate.irreducibleCharacter =
        D.characterRowCertificate.irreducibleCharacter) :
    row.scalarPattern = row'.scalarPattern := by
  have hdimension := C.dimension_eq_of_irreducibleCharacter_eq D h
  have hcentral :=
    congrArg
      (fun χ : IrreducibleCharacter AlternatingSixUniversalCover ↦
        χ.values alternatingSixAmbientCanonicalCentralGenerator)
      h
  rw [C.irreducibleCharacter_values_centralGenerator,
    D.irreducibleCharacter_values_centralGenerator,
    hdimension] at hcentral
  apply AlternatingSixAmbientScalarPattern.firstScalar_injective
  exact
    mul_left_cancel₀
      (Nat.cast_ne_zero.mpr row'.dimension_pos.ne')
      hcentral

/-- Different traces of the second presentation generator separate two
normalized ordinary rows. -/
theorem irreducibleCharacter_ne_of_matrixB_trace_ne
    {row' : AlternatingSixAmbientOrdinaryRow}
    (D : AlternatingSixAmbientOrdinaryCharacterRowCertificate row')
    (htrace : C.matrixRow.matrixB.trace ≠ D.matrixRow.matrixB.trace) :
    C.characterRowCertificate.irreducibleCharacter ≠
      D.characterRowCertificate.irreducibleCharacter := by
  letI : Nonempty (Fin row.dimension) :=
    Fin.pos_iff_nonempty.mp row.dimension_pos
  letI : Nonempty (Fin row'.dimension) :=
    Fin.pos_iff_nonempty.mp row'.dimension_pos
  apply
    CharacterRowCertificate.irreducibleCharacter_ne_of_character_apply_ne
      C.characterRowCertificate D.characterRowCertificate
      alternatingSixAmbientCanonicalGeneratorB
  change
    (FDRep.of C.matrixRow.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalGeneratorB ≠
      (FDRep.of D.matrixRow.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalGeneratorB
  rw [C.matrixRow.universalCoverRepresentation_character_generatorB,
    D.matrixRow.universalCoverRepresentation_character_generatorB]
  exact htrace

/-- Different traces of the product of the two presentation generators
separate two normalized ordinary rows. -/
theorem irreducibleCharacter_ne_of_matrixAB_trace_ne
    {row' : AlternatingSixAmbientOrdinaryRow}
    (D : AlternatingSixAmbientOrdinaryCharacterRowCertificate row')
    (htrace :
      (C.matrixRow.matrixA * C.matrixRow.matrixB).trace ≠
        (D.matrixRow.matrixA * D.matrixRow.matrixB).trace) :
    C.characterRowCertificate.irreducibleCharacter ≠
      D.characterRowCertificate.irreducibleCharacter := by
  letI : Nonempty (Fin row.dimension) :=
    Fin.pos_iff_nonempty.mp row.dimension_pos
  letI : Nonempty (Fin row'.dimension) :=
    Fin.pos_iff_nonempty.mp row'.dimension_pos
  apply
    CharacterRowCertificate.irreducibleCharacter_ne_of_character_apply_ne
      C.characterRowCertificate D.characterRowCertificate
      alternatingSixAmbientCanonicalGeneratorAB
  change
    (FDRep.of C.matrixRow.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalGeneratorAB ≠
      (FDRep.of D.matrixRow.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalGeneratorAB
  rw [C.matrixRow.universalCoverRepresentation_character_generatorAB,
    D.matrixRow.universalCoverRepresentation_character_generatorAB]
  exact htrace

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

/-- Every character enumerated by the completed table has the central value
advertised by its named row. -/
theorem character_values_centralGenerator
    (row : AlternatingSixAmbientOrdinaryRow) :
    (T.toFiniteCharacterTableCertificate.character row).values
        alternatingSixAmbientCanonicalCentralGenerator =
      (row.dimension : ℂ) *
        alternatingSixComplexCyclotomicRoot ^
          row.scalarPattern.exponent 0 :=
  (T.row row).irreducibleCharacter_values_centralGenerator

end AlternatingSixAmbientOrdinaryCharacterTableCertificate
end InductiveMcKay
end McKayConjecture
