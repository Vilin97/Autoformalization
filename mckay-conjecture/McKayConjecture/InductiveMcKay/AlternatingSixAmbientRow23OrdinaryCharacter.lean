/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterRowAssembly
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow23CharacterNorm

/-!
# The normalized ordinary character certificate for ambient row 23

The isolated row-23 presentation certificate is definitionally the row-23
entry of the complete relation table, so its exact 31-class norm packages
directly as the ordinary row certificate.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Ambient ordinary row 23, certified by exact class values and norm. -/
def alternatingSixAmbientRow23OrdinaryCharacterRowCertificate :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate .row23 :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateOfClassValues
    .row23 alternatingSixAmbientRow23ClassCharacterCertificate

/-- The packaged certificate uses the row-23 relation-table representation. -/
@[simp]
theorem alternatingSixAmbientRow23OrdinaryCharacterRowCertificate_matrixRow :
    alternatingSixAmbientRow23OrdinaryCharacterRowCertificate.matrixRow =
      alternatingSixAmbientOrdinaryRelationTable.row .row23 :=
  rfl

end InductiveMcKay
end McKayConjecture
