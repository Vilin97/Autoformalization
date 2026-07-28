/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassCharacterCertificate
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTableScalarPatterns

/-!
# Assembly of simple ordinary rows for `6.A₆`

The exact relation table and its central-scalar metadata are common to all
thirty-one ordinary rows.  Once a row representation has independently been
proved simple, this module packages it as a normalized irreducible-character
certificate without repeating the scalar bookkeeping.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

/-- Package one row of the complete relation table after its transported
canonical-cover representation has been proved simple. -/
def alternatingSixAmbientOrdinaryCharacterRowCertificateOfSimple
    (row : AlternatingSixAmbientOrdinaryRow)
    [Simple
      (FDRep.of
        (alternatingSixAmbientOrdinaryRelationTable.row row).universalCoverRepresentation)] :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate row :=
  AlternatingSixAmbientOrdinaryCharacterRowCertificate.ofSimple
    (alternatingSixAmbientOrdinaryRelationTable.row row)
    (alternatingSixAmbientOrdinaryRelationTable_relatorScalar_eq_scalarPattern
      row)

/-- Package one relation-table row from exact values on the thirty-one
checked conjugacy-class representatives and their weighted character norm. -/
def alternatingSixAmbientOrdinaryCharacterRowCertificateOfClassValues
    (row : AlternatingSixAmbientOrdinaryRow)
    (C :
      AlternatingSixAmbientClassCharacterCertificate
        (FDRep.of
          ((alternatingSixAmbientOrdinaryRelationTable.row row).universalCoverRepresentation))) :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate row where
  matrixRow := alternatingSixAmbientOrdinaryRelationTable.row row
  relatorScalar_eq_scalarPattern :=
    alternatingSixAmbientOrdinaryRelationTable_relatorScalar_eq_scalarPattern
      row
  characterSelfPairing :=
    AlternatingSixAmbientClassCharacterCertificate.characterSelfPairing C

end InductiveMcKay
end McKayConjecture
