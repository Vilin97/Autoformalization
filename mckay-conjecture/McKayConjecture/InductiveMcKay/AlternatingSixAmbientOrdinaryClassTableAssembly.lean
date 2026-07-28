/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterRowAssembly

/-!
# Assembly of the ordinary `6.A₆` table from class values

The thirty-one relation-table rows are already honest representations of the
canonical sixfold cover.  This file isolates the remaining finite
calculation: exact values on the thirty-one checked conjugacy classes, their
weighted norms, and injectivity of the resulting value vectors.

Once those data are supplied, the complete ordinary character-table
certificate follows without separate commutant or pairwise-separation proofs.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The canonical-cover representation carried by one row of the completed
ambient relation table. -/
abbrev AlternatingSixAmbientOrdinaryRelationRepresentation
    (row : AlternatingSixAmbientOrdinaryRow) :
    FDRep ℂ AlternatingSixUniversalCover :=
  FDRep.of
    ((alternatingSixAmbientOrdinaryRelationTable.row row)
      |>.universalCoverRepresentation)

/-- Exact class-value certificates for every relation-table row, together
with the finite check that their value vectors are pairwise distinct. -/
structure AlternatingSixAmbientOrdinaryClassTableCertificate where
  /-- Exact values and weighted norm for each of the thirty-one rows. -/
  classRow :
    ∀ row : AlternatingSixAmbientOrdinaryRow,
      AlternatingSixAmbientClassCharacterCertificate
        (AlternatingSixAmbientOrdinaryRelationRepresentation row)
  /-- The checked class-value vectors distinguish the named rows. -/
  value_injective :
    Function.Injective (fun row ↦ (classRow row).value)

namespace AlternatingSixAmbientOrdinaryClassTableCertificate

variable (T : AlternatingSixAmbientOrdinaryClassTableCertificate)

/-- The ordinary row certificate obtained from the checked class values. -/
def ordinaryRow
    (row : AlternatingSixAmbientOrdinaryRow) :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate row :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateOfClassValues
    row (T.classRow row)

/-- Equality of the packaged irreducible characters forces equality of their
checked class-value vectors. -/
theorem value_eq_of_irreducibleCharacter_eq
    {row row' : AlternatingSixAmbientOrdinaryRow}
    (h :
      (T.ordinaryRow row).characterRowCertificate.irreducibleCharacter =
        (T.ordinaryRow row').characterRowCertificate.irreducibleCharacter) :
    (T.classRow row).value = (T.classRow row').value := by
  funext i
  let g : AlternatingSixUniversalCover :=
    alternatingSixSchurCoordinatesEquivUniversalCover
      (alternatingSixSchurClassRepresentative i)
  calc
    (T.classRow row).value i =
        (AlternatingSixAmbientOrdinaryRelationRepresentation row).character
          g :=
      (T.classRow row).character_representative i |>.symm
    _ =
        ((T.ordinaryRow row).characterRowCertificate
          |>.irreducibleCharacter).values g := by
      symm
      exact
        (T.ordinaryRow row).characterRowCertificate
          |>.irreducibleCharacter_values_apply g
    _ =
        ((T.ordinaryRow row').characterRowCertificate
          |>.irreducibleCharacter).values g := by
      rw [h]
    _ =
        (AlternatingSixAmbientOrdinaryRelationRepresentation row').character
          g :=
      (T.ordinaryRow row').characterRowCertificate
        |>.irreducibleCharacter_values_apply g
    _ = (T.classRow row').value i :=
      (T.classRow row').character_representative i

/-- A complete exact class-value table supplies the complete ordinary
character table of the canonical sixfold cover. -/
def toOrdinaryCharacterTableCertificate :
    AlternatingSixAmbientOrdinaryCharacterTableCertificate where
  row := T.ordinaryRow
  row_injective := by
    intro row row' h
    apply T.value_injective
    exact T.value_eq_of_irreducibleCharacter_eq h
  conjugacyClassCount :=
    natCard_conjClasses_alternatingSixUniversalCover

end AlternatingSixAmbientOrdinaryClassTableCertificate
end InductiveMcKay
end McKayConjecture
