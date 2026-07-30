/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientCompletedOrdinaryCharacterTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterClassValueTransport

/-!
# Values of the completed ambient ordinary characters

This file exposes the uniform bridge from a named character in the completed
ordinary table to the character of the corresponding relation-table
representation.  Outer-action proofs can therefore reuse the existing exact
matrix trace certificates without unfolding the table assembly repeatedly.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private abbrev completedTable :=
  alternatingSixAmbientOrdinaryCharacterTableCertificate

/-- A completed-table character has the values of its named relation-table
representation. -/
theorem alternatingSixAmbientCompletedCharacter_values
    (row : AlternatingSixAmbientOrdinaryRow)
    (g : AlternatingSixUniversalCover) :
    (completedTable.toFiniteCharacterTableCertificate.character row).values g =
      (AlternatingSixAmbientOrdinaryRelationRepresentation row).character g := by
  change
    ((alternatingSixAmbientCompletedOrdinaryRow row).characterRowCertificate
      |>.irreducibleCharacter).values g =
      _
  rw [
    (alternatingSixAmbientCompletedOrdinaryRow row).characterRowCertificate
      |>.irreducibleCharacter_values_apply
  ]
  cases row <;> rfl

end InductiveMcKay
end McKayConjecture
