/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.FinCases
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeThreeScalarCommutants
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTableDegreeOneThree
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientTwoGeneratorCharacterRow
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientRow02ScalarCommutant

/-!
# Character certificates for the degree-one and degree-three ambient rows

The exact relation certificates for ordinary rows 01 through 05 are combined
with their scalar common-commutant proofs.  Each row is exposed both as a
simple canonical-cover representation and as a normalized
`CharacterRowCertificate`.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance row01CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row01.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance row02CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row02.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance row03CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row03.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance row04CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row04.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance row05CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row05.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

/-- Every endomorphism of the one-dimensional row 01 coordinate space is
scalar. -/
theorem alternatingSixAmbientRow01_scalar_commutant
    (X : Matrix (Fin 1) (Fin 1) ℂ)
    (_commutesA :
      X * alternatingSixFiveAmbient_row01_matrixA =
        alternatingSixFiveAmbient_row01_matrixA * X)
    (_commutesB :
      X * alternatingSixFiveAmbient_row01_matrixB =
        alternatingSixFiveAmbient_row01_matrixB * X) :
    ∃ c : ℂ, X = c • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  refine ⟨X 0 0, ?_⟩
  ext i j
  fin_cases i
  fin_cases j
  simp

/-- The row 01 canonical-cover representation is simple. -/
theorem alternatingSixAmbientRow01Representation_simple :
    Simple
      (FDRep.of
        alternatingSixAmbientRow01MatrixCertificate.universalCoverRepresentation) := by
  apply
    alternatingSixAmbientRow01MatrixCertificate.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow01_scalar_commutant X hA hB

/-- Normalized character-row certificate for ordinary row 01. -/
def alternatingSixAmbientRow01CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow01MatrixCertificate.characterRowCertificateOfScalarCommutant
    alternatingSixAmbientRow01_scalar_commutant

/-- The row 02 canonical-cover representation is simple. -/
theorem alternatingSixAmbientRow02Representation_simple :
    Simple
      (FDRep.of
        alternatingSixAmbientRow02MatrixCertificate.universalCoverRepresentation) := by
  apply
    alternatingSixAmbientRow02MatrixCertificate.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixFiveAmbientRow02_scalar_commutant X hA hB

/-- Normalized character-row certificate for ordinary row 02. -/
def alternatingSixAmbientRow02CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow02MatrixCertificate.characterRowCertificateOfScalarCommutant
    alternatingSixFiveAmbientRow02_scalar_commutant

/-- The row 03 canonical-cover representation is simple. -/
theorem alternatingSixAmbientRow03Representation_simple :
    Simple
      (FDRep.of
        alternatingSixAmbientRow03MatrixCertificate.universalCoverRepresentation) := by
  apply
    alternatingSixAmbientRow03MatrixCertificate.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow03_scalar_commutant X hA hB

/-- Normalized character-row certificate for ordinary row 03. -/
def alternatingSixAmbientRow03CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow03MatrixCertificate.characterRowCertificateOfScalarCommutant
    alternatingSixAmbientRow03_scalar_commutant

/-- The row 04 canonical-cover representation is simple. -/
theorem alternatingSixAmbientRow04Representation_simple :
    Simple
      (FDRep.of
        alternatingSixAmbientRow04MatrixCertificate.universalCoverRepresentation) := by
  apply
    alternatingSixAmbientRow04MatrixCertificate.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow04_scalar_commutant X hA hB

/-- Normalized character-row certificate for ordinary row 04. -/
def alternatingSixAmbientRow04CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow04MatrixCertificate.characterRowCertificateOfScalarCommutant
    alternatingSixAmbientRow04_scalar_commutant

/-- The row 05 canonical-cover representation is simple. -/
theorem alternatingSixAmbientRow05Representation_simple :
    Simple
      (FDRep.of
        alternatingSixAmbientRow05MatrixCertificate.universalCoverRepresentation) := by
  apply
    alternatingSixAmbientRow05MatrixCertificate.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow05_scalar_commutant X hA hB

/-- Normalized character-row certificate for ordinary row 05. -/
def alternatingSixAmbientRow05CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow05MatrixCertificate.characterRowCertificateOfScalarCommutant
    alternatingSixAmbientRow05_scalar_commutant

@[simp]
theorem alternatingSixAmbientRow01CharacterRowCertificate_representation :
    alternatingSixAmbientRow01CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow01MatrixCertificate.universalCoverRepresentation :=
  rfl

@[simp]
theorem alternatingSixAmbientRow02CharacterRowCertificate_representation :
    alternatingSixAmbientRow02CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow02MatrixCertificate.universalCoverRepresentation :=
  rfl

@[simp]
theorem alternatingSixAmbientRow03CharacterRowCertificate_representation :
    alternatingSixAmbientRow03CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow03MatrixCertificate.universalCoverRepresentation :=
  rfl

@[simp]
theorem alternatingSixAmbientRow04CharacterRowCertificate_representation :
    alternatingSixAmbientRow04CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow04MatrixCertificate.universalCoverRepresentation :=
  rfl

@[simp]
theorem alternatingSixAmbientRow05CharacterRowCertificate_representation :
    alternatingSixAmbientRow05CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow05MatrixCertificate.universalCoverRepresentation :=
  rfl

end InductiveMcKay
end McKayConjecture
