/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterRowAssembly
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow20CharacterNorm

/-!
# The normalized ordinary character certificate for ambient row 20

The isolated low-footprint row-20 relation certificate is definitionally the
row-20 entry of the complete ambient relation table. Its 31-class norm
certificate therefore packages directly as the ordinary row certificate used
by the ambient table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Ambient ordinary row 20, certified by its exact class values and norm. -/
def alternatingSixAmbientRow20OrdinaryCharacterRowCertificate :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate .row20 :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateOfClassValues
    .row20 alternatingSixAmbientRow20ClassCharacterCertificate

/-- The packaged ordinary certificate uses the row-20 relation-table
representation. -/
@[simp]
theorem alternatingSixAmbientRow20OrdinaryCharacterRowCertificate_matrixRow :
    alternatingSixAmbientRow20OrdinaryCharacterRowCertificate.matrixRow =
      alternatingSixAmbientOrdinaryRelationTable.row .row20 :=
  rfl

end InductiveMcKay
end McKayConjecture
