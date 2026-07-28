/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterRowAssembly
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24CharacterNorm

/-!
# The normalized ordinary character certificate for ambient row 24

The isolated low-footprint row-24 relation certificate is definitionally the
row-24 entry of the complete ambient relation table. Consequently its
31-class norm certificate packages directly as the ordinary row certificate
used by the ambient table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Ambient ordinary row 24, certified by its exact class values and norm. -/
def alternatingSixAmbientRow24OrdinaryCharacterRowCertificate :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate .row24 :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateOfClassValues
    .row24 alternatingSixAmbientRow24ClassCharacterCertificate

/-- The packaged ordinary certificate uses the row-24 relation-table
representation. -/
@[simp]
theorem alternatingSixAmbientRow24OrdinaryCharacterRowCertificate_matrixRow :
    alternatingSixAmbientRow24OrdinaryCharacterRowCertificate.matrixRow =
      alternatingSixAmbientOrdinaryRelationTable.row .row24 :=
  rfl

end InductiveMcKay
end McKayConjecture
