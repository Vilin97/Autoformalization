/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterRowAssembly
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P1CharacterNorm

/-!
# Normalized ATLAS degree-12 power-one ordinary character

The isolated relation certificate is definitionally the power-one entry of
the complete ambient relation table, so its exact class-value norm packages
directly as the ordinary row certificate used by the ambient table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- The first ATLAS degree-twelve row as a normalized ordinary character. -/
def alternatingSixAmbientAtlasTwelvePowerOneOrdinaryCharacterRowCertificate :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate
      .atlasTwelvePowerOne :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateOfClassValues
    .atlasTwelvePowerOne
    alternatingSixAmbientAtlas12P1ClassCharacterCertificate

/-- The packaged certificate uses the power-one relation-table row. -/
@[simp]
theorem
    alternatingSixAmbientAtlasTwelvePowerOneOrdinaryCharacterRowCertificate_matrixRow :
    (alternatingSixAmbientAtlasTwelvePowerOneOrdinaryCharacterRowCertificate
      ).matrixRow =
      alternatingSixAmbientOrdinaryRelationTable.row
        .atlasTwelvePowerOne :=
  rfl

end InductiveMcKay
end McKayConjecture
