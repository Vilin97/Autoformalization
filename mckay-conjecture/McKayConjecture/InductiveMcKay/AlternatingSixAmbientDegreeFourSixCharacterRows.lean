/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTableDegreeFourSix
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientTwoGeneratorCharacterRow
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow06DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow07DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow10DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow11DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow12DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow13DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow14DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow15DiagonalCommutant

/-!
# Character certificates for the degree-four and degree-six ambient rows

The exact relation certificates for ordinary rows `06`, `07`, and `10`
through `15` are combined with their scalar common-commutant proofs.  Each
row is exposed as a simple canonical-cover representation and as a normalized
`CharacterRowCertificate`.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance row06CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row06.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance row07CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row07.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance row10CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row10.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance row11CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row11.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance row12CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row12.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance row13CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row13.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance row14CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row14.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance row15CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row15.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

/-- The row 06 canonical-cover representation is simple. -/
instance alternatingSixAmbientRow06RepresentationSimple :
    Simple
      (FDRep.of
        alternatingSixAmbientRow06MatrixCertificate.universalCoverRepresentation) := by
  apply
    alternatingSixAmbientRow06MatrixCertificate.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow06_scalar_commutant X hA hB

/-- Normalized character-row certificate for ordinary row 06. -/
def alternatingSixAmbientRow06CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow06MatrixCertificate.characterRowCertificateOfScalarCommutant
    alternatingSixAmbientRow06_scalar_commutant

/-- The row 07 canonical-cover representation is simple. -/
instance alternatingSixAmbientRow07RepresentationSimple :
    Simple
      (FDRep.of
        alternatingSixAmbientRow07MatrixCertificate.universalCoverRepresentation) := by
  apply
    alternatingSixAmbientRow07MatrixCertificate.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow07_scalar_commutant X hA hB

/-- Normalized character-row certificate for ordinary row 07. -/
def alternatingSixAmbientRow07CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow07MatrixCertificate.characterRowCertificateOfScalarCommutant
    alternatingSixAmbientRow07_scalar_commutant

/-- The row 10 canonical-cover representation is simple. -/
instance alternatingSixAmbientRow10RepresentationSimple :
    Simple
      (FDRep.of
        alternatingSixAmbientRow10MatrixCertificate.universalCoverRepresentation) := by
  apply
    alternatingSixAmbientRow10MatrixCertificate.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow10_scalar_commutant X hA hB

/-- Normalized character-row certificate for ordinary row 10. -/
def alternatingSixAmbientRow10CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow10MatrixCertificate.characterRowCertificateOfScalarCommutant
    alternatingSixAmbientRow10_scalar_commutant

/-- The row 11 canonical-cover representation is simple. -/
instance alternatingSixAmbientRow11RepresentationSimple :
    Simple
      (FDRep.of
        alternatingSixAmbientRow11MatrixCertificate.universalCoverRepresentation) := by
  apply
    alternatingSixAmbientRow11MatrixCertificate.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow11_scalar_commutant X hA hB

/-- Normalized character-row certificate for ordinary row 11. -/
def alternatingSixAmbientRow11CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow11MatrixCertificate.characterRowCertificateOfScalarCommutant
    alternatingSixAmbientRow11_scalar_commutant

/-- The row 12 canonical-cover representation is simple. -/
instance alternatingSixAmbientRow12RepresentationSimple :
    Simple
      (FDRep.of
        alternatingSixAmbientRow12MatrixCertificate.universalCoverRepresentation) := by
  apply
    alternatingSixAmbientRow12MatrixCertificate.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow12_scalar_commutant X hA hB

/-- Normalized character-row certificate for ordinary row 12. -/
def alternatingSixAmbientRow12CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow12MatrixCertificate.characterRowCertificateOfScalarCommutant
    alternatingSixAmbientRow12_scalar_commutant

/-- The row 13 canonical-cover representation is simple. -/
instance alternatingSixAmbientRow13RepresentationSimple :
    Simple
      (FDRep.of
        alternatingSixAmbientRow13MatrixCertificate.universalCoverRepresentation) := by
  apply
    alternatingSixAmbientRow13MatrixCertificate.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow13_scalar_commutant X hA hB

/-- Normalized character-row certificate for ordinary row 13. -/
def alternatingSixAmbientRow13CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow13MatrixCertificate.characterRowCertificateOfScalarCommutant
    alternatingSixAmbientRow13_scalar_commutant

/-- The row 14 canonical-cover representation is simple. -/
instance alternatingSixAmbientRow14RepresentationSimple :
    Simple
      (FDRep.of
        alternatingSixAmbientRow14MatrixCertificate.universalCoverRepresentation) := by
  apply
    alternatingSixAmbientRow14MatrixCertificate.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow14_scalar_commutant X hA hB

/-- Normalized character-row certificate for ordinary row 14. -/
def alternatingSixAmbientRow14CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow14MatrixCertificate.characterRowCertificateOfScalarCommutant
    alternatingSixAmbientRow14_scalar_commutant

/-- The row 15 canonical-cover representation is simple. -/
instance alternatingSixAmbientRow15RepresentationSimple :
    Simple
      (FDRep.of
        alternatingSixAmbientRow15MatrixCertificate.universalCoverRepresentation) := by
  apply
    alternatingSixAmbientRow15MatrixCertificate.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow15_scalar_commutant X hA hB

/-- Normalized character-row certificate for ordinary row 15. -/
def alternatingSixAmbientRow15CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow15MatrixCertificate.characterRowCertificateOfScalarCommutant
    alternatingSixAmbientRow15_scalar_commutant

@[simp]
theorem alternatingSixAmbientRow06CharacterRowCertificate_representation :
    alternatingSixAmbientRow06CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow06MatrixCertificate.universalCoverRepresentation :=
  rfl

@[simp]
theorem alternatingSixAmbientRow07CharacterRowCertificate_representation :
    alternatingSixAmbientRow07CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow07MatrixCertificate.universalCoverRepresentation :=
  rfl

@[simp]
theorem alternatingSixAmbientRow10CharacterRowCertificate_representation :
    alternatingSixAmbientRow10CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow10MatrixCertificate.universalCoverRepresentation :=
  rfl

@[simp]
theorem alternatingSixAmbientRow11CharacterRowCertificate_representation :
    alternatingSixAmbientRow11CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow11MatrixCertificate.universalCoverRepresentation :=
  rfl

@[simp]
theorem alternatingSixAmbientRow12CharacterRowCertificate_representation :
    alternatingSixAmbientRow12CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow12MatrixCertificate.universalCoverRepresentation :=
  rfl

@[simp]
theorem alternatingSixAmbientRow13CharacterRowCertificate_representation :
    alternatingSixAmbientRow13CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow13MatrixCertificate.universalCoverRepresentation :=
  rfl

@[simp]
theorem alternatingSixAmbientRow14CharacterRowCertificate_representation :
    alternatingSixAmbientRow14CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow14MatrixCertificate.universalCoverRepresentation :=
  rfl

@[simp]
theorem alternatingSixAmbientRow15CharacterRowCertificate_representation :
    alternatingSixAmbientRow15CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow15MatrixCertificate.universalCoverRepresentation :=
  rfl

end InductiveMcKay
end McKayConjecture
