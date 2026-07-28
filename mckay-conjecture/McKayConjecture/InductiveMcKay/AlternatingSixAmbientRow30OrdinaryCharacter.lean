/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterRowAssembly
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow30CharacterNorm

/-!
# The normalized ordinary character certificate for ambient row 30

The isolated row-30 presentation certificate is definitionally the row-30
entry of the complete relation table, so its exact 31-class norm packages
directly as the ordinary row certificate.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Ambient ordinary row 30, certified by exact class values and norm. -/
def alternatingSixAmbientRow30OrdinaryCharacterRowCertificate :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate .row30 :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateOfClassValues
    .row30 alternatingSixAmbientRow30ClassCharacterCertificate

/-- The packaged certificate uses the row-30 relation-table representation. -/
@[simp]
theorem alternatingSixAmbientRow30OrdinaryCharacterRowCertificate_matrixRow :
    alternatingSixAmbientRow30OrdinaryCharacterRowCertificate.matrixRow =
      alternatingSixAmbientOrdinaryRelationTable.row .row30 :=
  rfl

end InductiveMcKay
end McKayConjecture
