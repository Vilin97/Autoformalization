/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeEightCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeFourCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeSixCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeThreeCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientInitialOrdinaryCharacters
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryRowSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18Row19CharacterSeparation

/-!
# Separation of the first nineteen ordinary `6.A₆` rows

Earlier commutant calculations package rows 1 through 18 as normalized
characters, while row 19 uses an exact class-value norm.  This module
transports the eight previously checked same-signature inequalities to that
uniform ordinary-table packaging.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev ordinaryRowThroughNineteen
    (row : AlternatingSixAmbientOrdinaryRow)
    (hrow : row.index.val < 19) :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateThroughNineteen
    row hrow

private abbrev ordinaryCharacterThroughNineteen
    (row : AlternatingSixAmbientOrdinaryRow)
    (hrow : row.index.val < 19) :
    IrreducibleCharacter AlternatingSixUniversalCover :=
  (ordinaryRowThroughNineteen row hrow)
    |>.characterRowCertificate.irreducibleCharacter

private abbrev ordinaryRepresentation
    (row : AlternatingSixAmbientOrdinaryRow) :
    FDRep ℂ AlternatingSixUniversalCover :=
  FDRep.of
    (alternatingSixAmbientOrdinaryRelationTable.row row).universalCoverRepresentation

private theorem ordinaryRowThroughNineteen_representation
    (row : AlternatingSixAmbientOrdinaryRow)
    (hrow : row.index.val < 19) :
    ((ordinaryRowThroughNineteen row hrow).characterRowCertificate).representation =
      ordinaryRepresentation row := by
  cases row <;> first
    | rfl
    | norm_num [AlternatingSixAmbientOrdinaryRow.index] at hrow

private theorem ordinaryRowThroughNineteen_character_eq
    (row : AlternatingSixAmbientOrdinaryRow)
    (hrow : row.index.val < 19)
    (C : CharacterRowCertificate AlternatingSixUniversalCover)
    (hrepresentation :
      C.representation = ordinaryRepresentation row) :
    ordinaryCharacterThroughNineteen row hrow =
      C.irreducibleCharacter := by
  apply
    CharacterRowCertificate.irreducibleCharacter_eq_of_representation_eq
  rw [ordinaryRowThroughNineteen_representation]
  exact hrepresentation.symm

private theorem ordinaryRow02_character_eq :
    ordinaryCharacterThroughNineteen .row02 (by decide) =
      alternatingSixAmbientRow02CharacterRowCertificate.irreducibleCharacter :=
  ordinaryRowThroughNineteen_character_eq
    .row02 (by decide)
    alternatingSixAmbientRow02CharacterRowCertificate rfl

private theorem ordinaryRow03_character_eq :
    ordinaryCharacterThroughNineteen .row03 (by decide) =
      alternatingSixAmbientRow03CharacterRowCertificate.irreducibleCharacter :=
  ordinaryRowThroughNineteen_character_eq
    .row03 (by decide)
    alternatingSixAmbientRow03CharacterRowCertificate rfl

private theorem ordinaryRow04_character_eq :
    ordinaryCharacterThroughNineteen .row04 (by decide) =
      alternatingSixAmbientRow04CharacterRowCertificate.irreducibleCharacter :=
  ordinaryRowThroughNineteen_character_eq
    .row04 (by decide)
    alternatingSixAmbientRow04CharacterRowCertificate rfl

private theorem ordinaryRow05_character_eq :
    ordinaryCharacterThroughNineteen .row05 (by decide) =
      alternatingSixAmbientRow05CharacterRowCertificate.irreducibleCharacter :=
  ordinaryRowThroughNineteen_character_eq
    .row05 (by decide)
    alternatingSixAmbientRow05CharacterRowCertificate rfl

private theorem ordinaryRow06_character_eq :
    ordinaryCharacterThroughNineteen .row06 (by decide) =
      alternatingSixAmbientRow06CharacterRowCertificate.irreducibleCharacter :=
  ordinaryRowThroughNineteen_character_eq
    .row06 (by decide)
    alternatingSixAmbientRow06CharacterRowCertificate rfl

private theorem ordinaryRow07_character_eq :
    ordinaryCharacterThroughNineteen .row07 (by decide) =
      alternatingSixAmbientRow07CharacterRowCertificate.irreducibleCharacter :=
  ordinaryRowThroughNineteen_character_eq
    .row07 (by decide)
    alternatingSixAmbientRow07CharacterRowCertificate rfl

private theorem ordinaryRow08_character_eq :
    ordinaryCharacterThroughNineteen .row08 (by decide) =
      alternatingSixAmbientRow08CharacterRowCertificate.irreducibleCharacter :=
  ordinaryRowThroughNineteen_character_eq
    .row08 (by decide)
    alternatingSixAmbientRow08CharacterRowCertificate rfl

private theorem ordinaryRow09_character_eq :
    ordinaryCharacterThroughNineteen .row09 (by decide) =
      alternatingSixAmbientRow09CharacterRowCertificate.irreducibleCharacter :=
  ordinaryRowThroughNineteen_character_eq
    .row09 (by decide)
    alternatingSixAmbientRow09CharacterRowCertificate rfl

private theorem ordinaryRow12_character_eq :
    ordinaryCharacterThroughNineteen .row12 (by decide) =
      alternatingSixAmbientRow12CharacterRowCertificate.irreducibleCharacter :=
  ordinaryRowThroughNineteen_character_eq
    .row12 (by decide)
    alternatingSixAmbientRow12CharacterRowCertificate rfl

private theorem ordinaryRow13_character_eq :
    ordinaryCharacterThroughNineteen .row13 (by decide) =
      alternatingSixAmbientRow13CharacterRowCertificate.irreducibleCharacter :=
  ordinaryRowThroughNineteen_character_eq
    .row13 (by decide)
    alternatingSixAmbientRow13CharacterRowCertificate rfl

private theorem ordinaryRow14_character_eq :
    ordinaryCharacterThroughNineteen .row14 (by decide) =
      alternatingSixAmbientRow14CharacterRowCertificate.irreducibleCharacter :=
  ordinaryRowThroughNineteen_character_eq
    .row14 (by decide)
    alternatingSixAmbientRow14CharacterRowCertificate rfl

private theorem ordinaryRow15_character_eq :
    ordinaryCharacterThroughNineteen .row15 (by decide) =
      alternatingSixAmbientRow15CharacterRowCertificate.irreducibleCharacter :=
  ordinaryRowThroughNineteen_character_eq
    .row15 (by decide)
    alternatingSixAmbientRow15CharacterRowCertificate rfl

private theorem ordinaryRow16_character_eq :
    ordinaryCharacterThroughNineteen .row16 (by decide) =
      alternatingSixAmbientRow16CharacterRowCertificate.irreducibleCharacter :=
  ordinaryRowThroughNineteen_character_eq
    .row16 (by decide)
    alternatingSixAmbientRow16CharacterRowCertificate rfl

private theorem ordinaryRow17_character_eq :
    ordinaryCharacterThroughNineteen .row17 (by decide) =
      alternatingSixAmbientRow17CharacterRowCertificate.irreducibleCharacter :=
  ordinaryRowThroughNineteen_character_eq
    .row17 (by decide)
    alternatingSixAmbientRow17CharacterRowCertificate rfl

/-- The packaged ordinary characters at rows 2 and 3 are distinct. -/
theorem alternatingSixAmbientOrdinaryRow02_ne_row03 :
    ordinaryCharacterThroughNineteen .row02 (by decide) ≠
      ordinaryCharacterThroughNineteen .row03 (by decide) := by
  rw [ordinaryRow02_character_eq, ordinaryRow03_character_eq]
  exact alternatingSixAmbientRow02_character_ne_row03_character

/-- The packaged ordinary characters at rows 4 and 5 are distinct. -/
theorem alternatingSixAmbientOrdinaryRow04_ne_row05 :
    ordinaryCharacterThroughNineteen .row04 (by decide) ≠
      ordinaryCharacterThroughNineteen .row05 (by decide) := by
  rw [ordinaryRow04_character_eq, ordinaryRow05_character_eq]
  exact alternatingSixAmbientRow04_character_ne_row05_character

/-- The packaged ordinary characters at rows 6 and 7 are distinct. -/
theorem alternatingSixAmbientOrdinaryRow06_ne_row07 :
    ordinaryCharacterThroughNineteen .row06 (by decide) ≠
      ordinaryCharacterThroughNineteen .row07 (by decide) := by
  rw [ordinaryRow06_character_eq, ordinaryRow07_character_eq]
  exact alternatingSixAmbientRow06_character_ne_row07_character

/-- The packaged ordinary characters at rows 8 and 9 are distinct. -/
theorem alternatingSixAmbientOrdinaryRow08_ne_row09 :
    ordinaryCharacterThroughNineteen .row08 (by decide) ≠
      ordinaryCharacterThroughNineteen .row09 (by decide) := by
  rw [ordinaryRow08_character_eq, ordinaryRow09_character_eq]
  exact alternatingSixAmbientRow08_character_ne_row09_character

/-- The packaged ordinary characters at rows 12 and 13 are distinct. -/
theorem alternatingSixAmbientOrdinaryRow12_ne_row13 :
    ordinaryCharacterThroughNineteen .row12 (by decide) ≠
      ordinaryCharacterThroughNineteen .row13 (by decide) := by
  rw [ordinaryRow12_character_eq, ordinaryRow13_character_eq]
  exact alternatingSixAmbientRow12_character_ne_row13_character

/-- The packaged ordinary characters at rows 14 and 15 are distinct. -/
theorem alternatingSixAmbientOrdinaryRow14_ne_row15 :
    ordinaryCharacterThroughNineteen .row14 (by decide) ≠
      ordinaryCharacterThroughNineteen .row15 (by decide) := by
  rw [ordinaryRow14_character_eq, ordinaryRow15_character_eq]
  exact alternatingSixAmbientRow14_character_ne_row15_character

/-- The packaged ordinary characters at rows 16 and 17 are distinct. -/
theorem alternatingSixAmbientOrdinaryRow16_ne_row17 :
    ordinaryCharacterThroughNineteen .row16 (by decide) ≠
      ordinaryCharacterThroughNineteen .row17 (by decide) := by
  rw [ordinaryRow16_character_eq, ordinaryRow17_character_eq]
  exact alternatingSixAmbientRow16_character_ne_row17_character

/-- The packaged ordinary characters at rows 18 and 19 are distinct. -/
theorem alternatingSixAmbientOrdinaryRow18_ne_row19 :
    ordinaryCharacterThroughNineteen .row18 (by decide) ≠
      ordinaryCharacterThroughNineteen .row19 (by decide) := by
  exact
    alternatingSixAmbientRow18OrdinaryCharacter_ne_row19OrdinaryCharacter

/-- The subtype of named ordinary rows already normalized through row 19. -/
abbrev AlternatingSixAmbientOrdinaryRowThroughNineteen :=
  { row : AlternatingSixAmbientOrdinaryRow // row.index.val < 19 }

/-- The uniform normalized certificate indexed by the first nineteen rows. -/
def alternatingSixAmbientOrdinaryRowThroughNineteenCertificate
    (row : AlternatingSixAmbientOrdinaryRowThroughNineteen) :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate row.1 :=
  ordinaryRowThroughNineteen row.1 row.2

/-- The irreducible character indexed by a normalized row through row 19. -/
def alternatingSixAmbientOrdinaryCharacterThroughNineteen
    (row : AlternatingSixAmbientOrdinaryRowThroughNineteen) :
    IrreducibleCharacter AlternatingSixUniversalCover :=
  (alternatingSixAmbientOrdinaryRowThroughNineteenCertificate row)
    |>.characterRowCertificate.irreducibleCharacter

/-- The first nineteen normalized ordinary characters are pairwise distinct. -/
theorem
    alternatingSixAmbientOrdinaryRowThroughNineteen_character_injective :
    Function.Injective
      alternatingSixAmbientOrdinaryCharacterThroughNineteen := by
  rintro ⟨row, hrow⟩ ⟨row', hrow'⟩ hcharacter
  let C :=
    alternatingSixAmbientOrdinaryRowThroughNineteenCertificate
      ⟨row, hrow⟩
  let D :=
    alternatingSixAmbientOrdinaryRowThroughNineteenCertificate
      ⟨row', hrow'⟩
  change
    C.characterRowCertificate.irreducibleCharacter =
      D.characterRowCertificate.irreducibleCharacter at hcharacter
  have hdimension :=
    C.dimension_eq_of_irreducibleCharacter_eq D hcharacter
  have hpattern :=
    C.scalarPattern_eq_of_irreducibleCharacter_eq D hcharacter
  rcases
      alternatingSixAmbientOrdinaryRow_eq_or_collision_of_signature_eq
        hdimension hpattern with
    hrow | hcollision
  · exact Subtype.ext hrow
  · cases hcollision with
    | row02_row03 =>
        exact (alternatingSixAmbientOrdinaryRow02_ne_row03 hcharacter).elim
    | row03_row02 =>
        exact (alternatingSixAmbientOrdinaryRow02_ne_row03 hcharacter.symm).elim
    | row04_row05 =>
        exact (alternatingSixAmbientOrdinaryRow04_ne_row05 hcharacter).elim
    | row05_row04 =>
        exact (alternatingSixAmbientOrdinaryRow04_ne_row05 hcharacter.symm).elim
    | row06_row07 =>
        exact (alternatingSixAmbientOrdinaryRow06_ne_row07 hcharacter).elim
    | row07_row06 =>
        exact (alternatingSixAmbientOrdinaryRow06_ne_row07 hcharacter.symm).elim
    | row08_row09 =>
        exact (alternatingSixAmbientOrdinaryRow08_ne_row09 hcharacter).elim
    | row09_row08 =>
        exact (alternatingSixAmbientOrdinaryRow08_ne_row09 hcharacter.symm).elim
    | row12_row13 =>
        exact (alternatingSixAmbientOrdinaryRow12_ne_row13 hcharacter).elim
    | row13_row12 =>
        exact (alternatingSixAmbientOrdinaryRow12_ne_row13 hcharacter.symm).elim
    | row14_row15 =>
        exact (alternatingSixAmbientOrdinaryRow14_ne_row15 hcharacter).elim
    | row15_row14 =>
        exact (alternatingSixAmbientOrdinaryRow14_ne_row15 hcharacter.symm).elim
    | row16_row17 =>
        exact (alternatingSixAmbientOrdinaryRow16_ne_row17 hcharacter).elim
    | row17_row16 =>
        exact (alternatingSixAmbientOrdinaryRow16_ne_row17 hcharacter.symm).elim
    | row18_row19 =>
        exact (alternatingSixAmbientOrdinaryRow18_ne_row19 hcharacter).elim
    | row19_row18 =>
        exact (alternatingSixAmbientOrdinaryRow18_ne_row19 hcharacter.symm).elim
    | row24_row25 | row25_row24
    | atlasOne_atlasSeven | atlasSeven_atlasOne
    | atlasTwo_atlasEleven | atlasEleven_atlasTwo =>
        norm_num [AlternatingSixAmbientOrdinaryRow.index] at hrow

end InductiveMcKay
end McKayConjecture
