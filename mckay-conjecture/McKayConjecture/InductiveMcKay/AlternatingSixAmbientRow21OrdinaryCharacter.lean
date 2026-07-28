/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterRowAssembly
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow21CharacterNorm

/-!
# The normalized ordinary character certificate for ambient row 21

The isolated row-21 presentation certificate is definitionally the row-21
entry of the complete relation table, so its exact 31-class norm packages
directly as the ordinary row certificate.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Ambient ordinary row 21, certified by exact class values and norm. -/
def alternatingSixAmbientRow21OrdinaryCharacterRowCertificate :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate .row21 :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateOfClassValues
    .row21 alternatingSixAmbientRow21ClassCharacterCertificate

/-- The packaged certificate uses the row-21 relation-table representation. -/
@[simp]
theorem alternatingSixAmbientRow21OrdinaryCharacterRowCertificate_matrixRow :
    alternatingSixAmbientRow21OrdinaryCharacterRowCertificate.matrixRow =
      alternatingSixAmbientOrdinaryRelationTable.row .row21 :=
  rfl

end InductiveMcKay
end McKayConjecture
