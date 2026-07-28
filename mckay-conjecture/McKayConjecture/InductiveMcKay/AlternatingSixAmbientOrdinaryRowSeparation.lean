/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterTable
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyClasses

/-!
# Finite separation interface for the ordinary `6.A₆` rows

Character degree and the scalar at the canonical central generator distinguish
all named rows except eleven explicit pairs.  This file proves that finite
reduction once.  A complete ordinary table can therefore be assembled from
normalized row certificates and inequalities for only those eleven pairs.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- The ordered pairs of distinct ordinary rows that have both the same
dimension and the same central-scalar pattern. -/
inductive AlternatingSixAmbientOrdinaryRowCollision :
    AlternatingSixAmbientOrdinaryRow →
      AlternatingSixAmbientOrdinaryRow → Prop
  | row02_row03 : AlternatingSixAmbientOrdinaryRowCollision .row02 .row03
  | row03_row02 : AlternatingSixAmbientOrdinaryRowCollision .row03 .row02
  | row04_row05 : AlternatingSixAmbientOrdinaryRowCollision .row04 .row05
  | row05_row04 : AlternatingSixAmbientOrdinaryRowCollision .row05 .row04
  | row06_row07 : AlternatingSixAmbientOrdinaryRowCollision .row06 .row07
  | row07_row06 : AlternatingSixAmbientOrdinaryRowCollision .row07 .row06
  | row08_row09 : AlternatingSixAmbientOrdinaryRowCollision .row08 .row09
  | row09_row08 : AlternatingSixAmbientOrdinaryRowCollision .row09 .row08
  | row12_row13 : AlternatingSixAmbientOrdinaryRowCollision .row12 .row13
  | row13_row12 : AlternatingSixAmbientOrdinaryRowCollision .row13 .row12
  | row14_row15 : AlternatingSixAmbientOrdinaryRowCollision .row14 .row15
  | row15_row14 : AlternatingSixAmbientOrdinaryRowCollision .row15 .row14
  | row16_row17 : AlternatingSixAmbientOrdinaryRowCollision .row16 .row17
  | row17_row16 : AlternatingSixAmbientOrdinaryRowCollision .row17 .row16
  | row18_row19 : AlternatingSixAmbientOrdinaryRowCollision .row18 .row19
  | row19_row18 : AlternatingSixAmbientOrdinaryRowCollision .row19 .row18
  | row24_row25 : AlternatingSixAmbientOrdinaryRowCollision .row24 .row25
  | row25_row24 : AlternatingSixAmbientOrdinaryRowCollision .row25 .row24
  | atlasOne_atlasSeven :
      AlternatingSixAmbientOrdinaryRowCollision
        .atlasTwelvePowerOne .atlasTwelvePowerSeven
  | atlasSeven_atlasOne :
      AlternatingSixAmbientOrdinaryRowCollision
        .atlasTwelvePowerSeven .atlasTwelvePowerOne
  | atlasTwo_atlasEleven :
      AlternatingSixAmbientOrdinaryRowCollision
        .atlasTwelvePowerTwo .atlasTwelvePowerEleven
  | atlasEleven_atlasTwo :
      AlternatingSixAmbientOrdinaryRowCollision
        .atlasTwelvePowerEleven .atlasTwelvePowerTwo

-- This theorem is an intentional exhaustive reduction of a 31-by-31 table.
set_option linter.flexible false in
/-- Equal dimension and central pattern force equality or one of the eleven
explicit collision pairs. -/
theorem
    alternatingSixAmbientOrdinaryRow_eq_or_collision_of_signature_eq
    {row row' : AlternatingSixAmbientOrdinaryRow}
    (hdimension : row.dimension = row'.dimension)
    (hpattern : row.scalarPattern = row'.scalarPattern) :
    row = row' ∨
      AlternatingSixAmbientOrdinaryRowCollision row row' := by
  cases row <;> cases row' <;>
    simp_all [AlternatingSixAmbientOrdinaryRow.dimension,
      AlternatingSixAmbientOrdinaryRow.scalarPattern] <;>
    first
    | exact AlternatingSixAmbientOrdinaryRowCollision.row02_row03
    | exact AlternatingSixAmbientOrdinaryRowCollision.row03_row02
    | exact AlternatingSixAmbientOrdinaryRowCollision.row04_row05
    | exact AlternatingSixAmbientOrdinaryRowCollision.row05_row04
    | exact AlternatingSixAmbientOrdinaryRowCollision.row06_row07
    | exact AlternatingSixAmbientOrdinaryRowCollision.row07_row06
    | exact AlternatingSixAmbientOrdinaryRowCollision.row08_row09
    | exact AlternatingSixAmbientOrdinaryRowCollision.row09_row08
    | exact AlternatingSixAmbientOrdinaryRowCollision.row12_row13
    | exact AlternatingSixAmbientOrdinaryRowCollision.row13_row12
    | exact AlternatingSixAmbientOrdinaryRowCollision.row14_row15
    | exact AlternatingSixAmbientOrdinaryRowCollision.row15_row14
    | exact AlternatingSixAmbientOrdinaryRowCollision.row16_row17
    | exact AlternatingSixAmbientOrdinaryRowCollision.row17_row16
    | exact AlternatingSixAmbientOrdinaryRowCollision.row18_row19
    | exact AlternatingSixAmbientOrdinaryRowCollision.row19_row18
    | exact AlternatingSixAmbientOrdinaryRowCollision.row24_row25
    | exact AlternatingSixAmbientOrdinaryRowCollision.row25_row24
    | exact AlternatingSixAmbientOrdinaryRowCollision.atlasOne_atlasSeven
    | exact AlternatingSixAmbientOrdinaryRowCollision.atlasSeven_atlasOne
    | exact AlternatingSixAmbientOrdinaryRowCollision.atlasTwo_atlasEleven
    | exact AlternatingSixAmbientOrdinaryRowCollision.atlasEleven_atlasTwo

/-- Normalized certificates for all rows, with separation required only for
the eleven equal-signature pairs. -/
structure AlternatingSixAmbientSeparatedOrdinaryRowFamily where
  row :
    ∀ index : AlternatingSixAmbientOrdinaryRow,
      AlternatingSixAmbientOrdinaryCharacterRowCertificate index
  row02_ne_row03 :
    (row .row02).characterRowCertificate.irreducibleCharacter ≠
      (row .row03).characterRowCertificate.irreducibleCharacter
  row04_ne_row05 :
    (row .row04).characterRowCertificate.irreducibleCharacter ≠
      (row .row05).characterRowCertificate.irreducibleCharacter
  row06_ne_row07 :
    (row .row06).characterRowCertificate.irreducibleCharacter ≠
      (row .row07).characterRowCertificate.irreducibleCharacter
  row08_ne_row09 :
    (row .row08).characterRowCertificate.irreducibleCharacter ≠
      (row .row09).characterRowCertificate.irreducibleCharacter
  row12_ne_row13 :
    (row .row12).characterRowCertificate.irreducibleCharacter ≠
      (row .row13).characterRowCertificate.irreducibleCharacter
  row14_ne_row15 :
    (row .row14).characterRowCertificate.irreducibleCharacter ≠
      (row .row15).characterRowCertificate.irreducibleCharacter
  row16_ne_row17 :
    (row .row16).characterRowCertificate.irreducibleCharacter ≠
      (row .row17).characterRowCertificate.irreducibleCharacter
  row18_ne_row19 :
    (row .row18).characterRowCertificate.irreducibleCharacter ≠
      (row .row19).characterRowCertificate.irreducibleCharacter
  row24_ne_row25 :
    (row .row24).characterRowCertificate.irreducibleCharacter ≠
      (row .row25).characterRowCertificate.irreducibleCharacter
  atlasOne_ne_atlasSeven :
    (row .atlasTwelvePowerOne).characterRowCertificate.irreducibleCharacter ≠
      (row .atlasTwelvePowerSeven).characterRowCertificate.irreducibleCharacter
  atlasTwo_ne_atlasEleven :
    (row .atlasTwelvePowerTwo).characterRowCertificate.irreducibleCharacter ≠
      (row .atlasTwelvePowerEleven).characterRowCertificate.irreducibleCharacter

namespace AlternatingSixAmbientSeparatedOrdinaryRowFamily

variable (T : AlternatingSixAmbientSeparatedOrdinaryRowFamily)

/-- The eleven checked inequalities and the finite signature reduction prove
global row injectivity. -/
theorem row_injective :
    Function.Injective
      (fun index ↦
        (T.row index).characterRowCertificate.irreducibleCharacter) := by
  intro row row' hcharacter
  have hdimension :=
    (T.row row).dimension_eq_of_irreducibleCharacter_eq
      (T.row row') hcharacter
  have hpattern :=
    (T.row row).scalarPattern_eq_of_irreducibleCharacter_eq
      (T.row row') hcharacter
  rcases
      alternatingSixAmbientOrdinaryRow_eq_or_collision_of_signature_eq
        hdimension hpattern with
    hrow | hcollision
  · exact hrow
  · cases hcollision with
    | row02_row03 => exact (T.row02_ne_row03 hcharacter).elim
    | row03_row02 => exact (T.row02_ne_row03 hcharacter.symm).elim
    | row04_row05 => exact (T.row04_ne_row05 hcharacter).elim
    | row05_row04 => exact (T.row04_ne_row05 hcharacter.symm).elim
    | row06_row07 => exact (T.row06_ne_row07 hcharacter).elim
    | row07_row06 => exact (T.row06_ne_row07 hcharacter.symm).elim
    | row08_row09 => exact (T.row08_ne_row09 hcharacter).elim
    | row09_row08 => exact (T.row08_ne_row09 hcharacter.symm).elim
    | row12_row13 => exact (T.row12_ne_row13 hcharacter).elim
    | row13_row12 => exact (T.row12_ne_row13 hcharacter.symm).elim
    | row14_row15 => exact (T.row14_ne_row15 hcharacter).elim
    | row15_row14 => exact (T.row14_ne_row15 hcharacter.symm).elim
    | row16_row17 => exact (T.row16_ne_row17 hcharacter).elim
    | row17_row16 => exact (T.row16_ne_row17 hcharacter.symm).elim
    | row18_row19 => exact (T.row18_ne_row19 hcharacter).elim
    | row19_row18 => exact (T.row18_ne_row19 hcharacter.symm).elim
    | row24_row25 => exact (T.row24_ne_row25 hcharacter).elim
    | row25_row24 => exact (T.row24_ne_row25 hcharacter.symm).elim
    | atlasOne_atlasSeven =>
        exact (T.atlasOne_ne_atlasSeven hcharacter).elim
    | atlasSeven_atlasOne =>
        exact (T.atlasOne_ne_atlasSeven hcharacter.symm).elim
    | atlasTwo_atlasEleven =>
        exact (T.atlasTwo_ne_atlasEleven hcharacter).elim
    | atlasEleven_atlasTwo =>
        exact (T.atlasTwo_ne_atlasEleven hcharacter.symm).elim

/-- A separated normalized row family is the complete ordinary character
table of the canonical sixfold cover. -/
def toOrdinaryCharacterTableCertificate :
    AlternatingSixAmbientOrdinaryCharacterTableCertificate where
  row := T.row
  row_injective := T.row_injective
  conjugacyClassCount :=
    GroupTheory.natCard_conjClasses_alternatingSixUniversalCover

end AlternatingSixAmbientSeparatedOrdinaryRowFamily
end InductiveMcKay
end McKayConjecture
