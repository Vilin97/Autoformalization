/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterRowAssembly
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow22CharacterNorm

/-!
# The normalized ordinary character certificate for ambient row 22

The isolated row-22 presentation certificate is definitionally the row-22
entry of the complete relation table, so its exact 31-class norm packages
directly as the ordinary row certificate.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Ambient ordinary row 22, certified by exact class values and norm. -/
def alternatingSixAmbientRow22OrdinaryCharacterRowCertificate :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate .row22 :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateOfClassValues
    .row22 alternatingSixAmbientRow22ClassCharacterCertificate

/-- The packaged certificate uses the row-22 relation-table representation. -/
@[simp]
theorem alternatingSixAmbientRow22OrdinaryCharacterRowCertificate_matrixRow :
    alternatingSixAmbientRow22OrdinaryCharacterRowCertificate.matrixRow =
      alternatingSixAmbientOrdinaryRelationTable.row .row22 :=
  rfl

end InductiveMcKay
end McKayConjecture
