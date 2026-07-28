/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CharacterRowSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeEightCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18OrdinaryCharacter
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19OrdinaryCharacter

/-!
# Separation of ambient ordinary rows 18 and 19

Rows 18 and 19 have the same dimension and central-scalar pattern.  Their
already-checked `AB` traces distinguish the two normalized ordinary
characters.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev row18OrdinaryCertificate :=
  alternatingSixAmbientRow18OrdinaryCharacterRowCertificate

private abbrev row19OrdinaryCertificate :=
  alternatingSixAmbientRow19OrdinaryCharacterRowCertificate

local instance row18Row19SeparationRow18CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row18.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance row18Row19SeparationRow19CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row19.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

theorem alternatingSixAmbientRow18OrdinaryCharacter_generatorAB :
    (row18OrdinaryCertificate.characterRowCertificate.representation.character)
        alternatingSixAmbientCanonicalGeneratorAB =
      (alternatingSixFiveAmbient_row18_matrixA *
        alternatingSixFiveAmbient_row18_matrixB).trace := by
  change
    (FDRep.of
      alternatingSixAmbientRow18MatrixCertificate.universalCoverRepresentation).character
      alternatingSixAmbientCanonicalGeneratorAB =
      _
  exact
    alternatingSixAmbientRow18MatrixCertificate
      |>.universalCoverRepresentation_character_generatorAB

theorem alternatingSixAmbientRow19OrdinaryCharacter_generatorAB :
    (row19OrdinaryCertificate.characterRowCertificate.representation.character)
        alternatingSixAmbientCanonicalGeneratorAB =
      (alternatingSixFiveAmbient_row19_matrixA *
        alternatingSixFiveAmbient_row19_matrixB).trace := by
  change
    (FDRep.of
      alternatingSixAmbientRow19MatrixCertificate.universalCoverRepresentation).character
      alternatingSixAmbientCanonicalGeneratorAB =
      _
  exact
    alternatingSixAmbientRow19MatrixCertificate
      |>.universalCoverRepresentation_character_generatorAB

/-- The normalized ordinary characters at rows 18 and 19 are distinct. -/
theorem
    alternatingSixAmbientRow18OrdinaryCharacter_ne_row19OrdinaryCharacter :
    row18OrdinaryCertificate.characterRowCertificate.irreducibleCharacter ≠
      row19OrdinaryCertificate.characterRowCertificate.irreducibleCharacter := by
  apply
    CharacterRowCertificate.irreducibleCharacter_ne_of_character_apply_ne
      row18OrdinaryCertificate.characterRowCertificate
      row19OrdinaryCertificate.characterRowCertificate
      alternatingSixAmbientCanonicalGeneratorAB
  rw [alternatingSixAmbientRow18OrdinaryCharacter_generatorAB,
    alternatingSixAmbientRow19OrdinaryCharacter_generatorAB]
  exact
    alternatingSixAmbientRow18_matrixAB_trace_ne_row19_matrixAB_trace

end InductiveMcKay
end McKayConjecture
