/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterRowAssembly
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow31CharacterNorm

/-!
# The normalized ordinary character certificate for ambient row 31

The isolated low-footprint row-31 relation certificate is definitionally the
row-31 entry of the complete ambient relation table. Consequently its
31-class norm certificate packages directly as the ordinary row certificate
used by the ambient table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Ambient ordinary row 31, certified by its exact class values and norm. -/
def alternatingSixAmbientRow31OrdinaryCharacterRowCertificate :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate .row31 :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateOfClassValues
    .row31 alternatingSixAmbientRow31ClassCharacterCertificate

/-- The packaged ordinary certificate uses the row-31 relation-table
representation. -/
@[simp]
theorem alternatingSixAmbientRow31OrdinaryCharacterRowCertificate_matrixRow :
    alternatingSixAmbientRow31OrdinaryCharacterRowCertificate.matrixRow =
      alternatingSixAmbientOrdinaryRelationTable.row .row31 :=
  rfl

end InductiveMcKay
end McKayConjecture
