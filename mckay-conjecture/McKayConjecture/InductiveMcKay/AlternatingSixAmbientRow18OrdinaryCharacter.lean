/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterRowAssembly
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18Simple

/-!
# The normalized ordinary character certificate for ambient row 18

The split common-commutant calculation proves that row 18 of the completed
relation table is simple.  This module packages that result in the common
ordinary-table interface.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Ambient ordinary row 18, certified by its scalar common commutant. -/
def alternatingSixAmbientRow18OrdinaryCharacterRowCertificate :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate .row18 :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateOfSimple .row18

@[simp]
theorem alternatingSixAmbientRow18OrdinaryCharacterRowCertificate_matrixRow :
    alternatingSixAmbientRow18OrdinaryCharacterRowCertificate.matrixRow =
      alternatingSixAmbientOrdinaryRelationTable.row .row18 :=
  rfl

end InductiveMcKay
end McKayConjecture
