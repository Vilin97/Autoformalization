/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterRowAssembly
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P11CharacterNorm

/-!
# Normalized ATLAS degree-12 power-eleven ordinary character

The isolated relation certificate is definitionally the power-eleven entry
of the complete ambient relation table, so its exact class-value norm
packages directly as the corresponding ordinary row certificate.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- The last ATLAS degree-twelve row as a normalized ordinary character. -/
def
    alternatingSixAmbientAtlasTwelvePowerElevenOrdinaryCharacterRowCertificate :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate
      .atlasTwelvePowerEleven :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateOfClassValues
    .atlasTwelvePowerEleven
    alternatingSixAmbientAtlas12P11ClassCharacterCertificate

/-- The packaged certificate uses the power-eleven relation-table row. -/
@[simp]
theorem
    alternatingSixAmbientAtlasTwelvePowerElevenOrdinaryCharacterRowCertificate_matrixRow :
    (alternatingSixAmbientAtlasTwelvePowerElevenOrdinaryCharacterRowCertificate
      ).matrixRow =
      alternatingSixAmbientOrdinaryRelationTable.row
        .atlasTwelvePowerEleven :=
  rfl

end InductiveMcKay
end McKayConjecture
