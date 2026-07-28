/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterRowAssembly
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19CharacterNorm

/-!
# The normalized ordinary character certificate for ambient row 19

The isolated low-footprint row-19 relation certificate is definitionally the
row-19 entry of the complete ambient relation table.  Consequently its
31-class norm certificate packages directly as the ordinary row certificate
used by the ambient table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Ambient ordinary row 19, certified by its exact class values and norm. -/
def alternatingSixAmbientRow19OrdinaryCharacterRowCertificate :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate .row19 :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateOfClassValues
    .row19 alternatingSixAmbientRow19ClassCharacterCertificate

/-- The packaged ordinary certificate uses the row-19 relation-table
representation. -/
@[simp]
theorem alternatingSixAmbientRow19OrdinaryCharacterRowCertificate_matrixRow :
    alternatingSixAmbientRow19OrdinaryCharacterRowCertificate.matrixRow =
      alternatingSixAmbientOrdinaryRelationTable.row .row19 :=
  rfl

end InductiveMcKay
end McKayConjecture
