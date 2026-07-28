/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeEightInitialSimpleInstances
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeFiveCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeFourSixCharacterRows
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeOneThreeCharacterRows
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryClassTableAssembly
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18OrdinaryCharacter
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19OrdinaryCharacter

/-!
# Normalized ordinary certificates for ambient rows 1 through 18

The small commutant calculations and the split row-18 calculation establish
simplicity of the first eighteen relation-table rows.  This module packages
those results uniformly for later complete-table assembly.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

/-- Every relation-table representation among rows 1 through 18 is simple. -/
theorem alternatingSixAmbientInitialRepresentation_simple
    (row : AlternatingSixAmbientOrdinaryRow)
    (hrow : row.index.val < 18) :
    Simple
      (AlternatingSixAmbientOrdinaryRelationRepresentation row) := by
  cases row with
  | row01 =>
      change Simple alternatingSixAmbientRow01CharacterRowCertificate.representation
      exact alternatingSixAmbientRow01CharacterRowCertificate.simple
  | row02 =>
      change Simple alternatingSixAmbientRow02CharacterRowCertificate.representation
      exact alternatingSixAmbientRow02CharacterRowCertificate.simple
  | row03 =>
      change Simple alternatingSixAmbientRow03CharacterRowCertificate.representation
      exact alternatingSixAmbientRow03CharacterRowCertificate.simple
  | row04 =>
      change Simple alternatingSixAmbientRow04CharacterRowCertificate.representation
      exact alternatingSixAmbientRow04CharacterRowCertificate.simple
  | row05 =>
      change Simple alternatingSixAmbientRow05CharacterRowCertificate.representation
      exact alternatingSixAmbientRow05CharacterRowCertificate.simple
  | row06 =>
      change Simple alternatingSixAmbientRow06CharacterRowCertificate.representation
      exact alternatingSixAmbientRow06CharacterRowCertificate.simple
  | row07 =>
      change Simple alternatingSixAmbientRow07CharacterRowCertificate.representation
      exact alternatingSixAmbientRow07CharacterRowCertificate.simple
  | row08 =>
      change Simple alternatingSixAmbientRow08CharacterRowCertificate.representation
      exact alternatingSixAmbientRow08CharacterRowCertificate.simple
  | row09 =>
      change Simple alternatingSixAmbientRow09CharacterRowCertificate.representation
      exact alternatingSixAmbientRow09CharacterRowCertificate.simple
  | row10 =>
      change Simple alternatingSixAmbientRow10CharacterRowCertificate.representation
      exact alternatingSixAmbientRow10CharacterRowCertificate.simple
  | row11 =>
      change Simple alternatingSixAmbientRow11CharacterRowCertificate.representation
      exact alternatingSixAmbientRow11CharacterRowCertificate.simple
  | row12 =>
      change Simple alternatingSixAmbientRow12CharacterRowCertificate.representation
      exact alternatingSixAmbientRow12CharacterRowCertificate.simple
  | row13 =>
      change Simple alternatingSixAmbientRow13CharacterRowCertificate.representation
      exact alternatingSixAmbientRow13CharacterRowCertificate.simple
  | row14 =>
      change Simple alternatingSixAmbientRow14CharacterRowCertificate.representation
      exact alternatingSixAmbientRow14CharacterRowCertificate.simple
  | row15 =>
      change Simple alternatingSixAmbientRow15CharacterRowCertificate.representation
      exact alternatingSixAmbientRow15CharacterRowCertificate.simple
  | row16 | row17 | row18 => infer_instance
  | row19 | row20 | row21 | row22 | row23 | row24 | row25
  | row30 | row31 | atlasTwelvePowerOne | atlasTwelvePowerTwo
  | atlasTwelvePowerSeven | atlasTwelvePowerEleven =>
      norm_num [AlternatingSixAmbientOrdinaryRow.index] at hrow

/-- A normalized ordinary row certificate for every named row whose numeric
index is below 18. -/
def alternatingSixAmbientInitialOrdinaryCharacterRowCertificate
    (row : AlternatingSixAmbientOrdinaryRow)
    (hrow : row.index.val < 18) :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate row := by
  letI : Simple
      (AlternatingSixAmbientOrdinaryRelationRepresentation row) :=
    alternatingSixAmbientInitialRepresentation_simple row hrow
  exact alternatingSixAmbientOrdinaryCharacterRowCertificateOfSimple row

/-- The first nineteen ordinary rows, including the class-value certificate
for row 19. -/
def alternatingSixAmbientOrdinaryCharacterRowCertificateThroughNineteen
    (row : AlternatingSixAmbientOrdinaryRow)
    (hrow : row.index.val < 19) :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate row := by
  cases row with
  | row01 | row02 | row03 | row04 | row05 | row06 | row07
  | row08 | row09 | row10 | row11 | row12 | row13 | row14
  | row15 | row16 | row17 | row18 =>
      exact
        alternatingSixAmbientInitialOrdinaryCharacterRowCertificate
          _ (by decide)
  | row19 =>
      exact alternatingSixAmbientRow19OrdinaryCharacterRowCertificate
  | row20 | row21 | row22 | row23 | row24 | row25 | row30 | row31
  | atlasTwelvePowerOne | atlasTwelvePowerTwo
  | atlasTwelvePowerSeven | atlasTwelvePowerEleven =>
      norm_num [AlternatingSixAmbientOrdinaryRow.index] at hrow

end InductiveMcKay
end McKayConjecture
