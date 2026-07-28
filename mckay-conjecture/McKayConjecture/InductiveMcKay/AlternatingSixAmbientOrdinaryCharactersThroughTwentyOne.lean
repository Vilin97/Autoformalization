/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientInitialOrdinaryCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow20OrdinaryCharacter
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow21OrdinaryCharacter

/-!
# Normalized ordinary characters through row 21 of `6.A₆`

Rows 20 and 21 have exact 31-class character norms.  Their signatures are
new among the earlier rows, so adjoining them to the injective first-nineteen
family requires no additional same-signature character-value comparison.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The subtype of named ordinary rows normalized through row 21. -/
abbrev AlternatingSixAmbientOrdinaryRowThroughTwentyOne :=
  { row : AlternatingSixAmbientOrdinaryRow // row.index.val < 21 }

/-- The uniform normalized certificate for a named row through row 21. -/
def alternatingSixAmbientOrdinaryCharacterRowCertificateThroughTwentyOne
    (row : AlternatingSixAmbientOrdinaryRow)
    (hrow : row.index.val < 21) :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate row := by
  cases row with
  | row01 | row02 | row03 | row04 | row05 | row06 | row07
  | row08 | row09 | row10 | row11 | row12 | row13 | row14
  | row15 | row16 | row17 | row18 | row19 =>
      exact
        alternatingSixAmbientOrdinaryCharacterRowCertificateThroughNineteen
          _ (by decide)
  | row20 =>
      exact alternatingSixAmbientRow20OrdinaryCharacterRowCertificate
  | row21 =>
      exact alternatingSixAmbientRow21OrdinaryCharacterRowCertificate
  | row22 | row23 | row24 | row25 | row30 | row31
  | atlasTwelvePowerOne | atlasTwelvePowerTwo
  | atlasTwelvePowerSeven | atlasTwelvePowerEleven =>
      norm_num [AlternatingSixAmbientOrdinaryRow.index] at hrow

/-- Subtype-indexed form of the normalized certificates through row 21. -/
def alternatingSixAmbientOrdinaryRowThroughTwentyOneCertificate
    (indexedRow : AlternatingSixAmbientOrdinaryRowThroughTwentyOne) :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate indexedRow.1 :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateThroughTwentyOne
    indexedRow.1 indexedRow.2

/-- The irreducible character indexed by a normalized row through row 21. -/
def alternatingSixAmbientOrdinaryCharacterThroughTwentyOne
    (row : AlternatingSixAmbientOrdinaryRowThroughTwentyOne) :
    IrreducibleCharacter AlternatingSixUniversalCover :=
  (alternatingSixAmbientOrdinaryRowThroughTwentyOneCertificate row)
    |>.characterRowCertificate.irreducibleCharacter

/-- The first twenty-one normalized ordinary characters are pairwise
distinct. -/
theorem
    alternatingSixAmbientOrdinaryRowThroughTwentyOne_character_injective :
    Function.Injective
      alternatingSixAmbientOrdinaryCharacterThroughTwentyOne := by
  rintro ⟨row, hrow⟩ ⟨row', hrow'⟩ hcharacter
  let C :=
    alternatingSixAmbientOrdinaryRowThroughTwentyOneCertificate
      ⟨row, hrow⟩
  let D :=
    alternatingSixAmbientOrdinaryRowThroughTwentyOneCertificate
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
    hrowEq | hcollision
  · exact Subtype.ext hrowEq
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
