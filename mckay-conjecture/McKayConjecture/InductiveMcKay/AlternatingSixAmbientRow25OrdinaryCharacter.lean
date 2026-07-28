/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterRowAssembly
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25CharacterNorm

/-!
# The normalized ordinary character certificate for ambient row 25

The isolated low-footprint row-25 relation certificate is definitionally the
row-25 entry of the complete ambient relation table. Consequently its
31-class norm certificate packages directly as the ordinary row certificate
used by the ambient table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Ambient ordinary row 25, certified by its exact class values and norm. -/
def alternatingSixAmbientRow25OrdinaryCharacterRowCertificate :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate .row25 :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateOfClassValues
    .row25 alternatingSixAmbientRow25ClassCharacterCertificate

/-- The packaged ordinary certificate uses the row-25 relation-table
representation. -/
@[simp]
theorem alternatingSixAmbientRow25OrdinaryCharacterRowCertificate_matrixRow :
    alternatingSixAmbientRow25OrdinaryCharacterRowCertificate.matrixRow =
      alternatingSixAmbientOrdinaryRelationTable.row .row25 :=
  rfl

end InductiveMcKay
end McKayConjecture
