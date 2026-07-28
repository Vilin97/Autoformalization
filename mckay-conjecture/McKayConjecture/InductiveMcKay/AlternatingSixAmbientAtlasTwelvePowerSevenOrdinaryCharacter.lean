/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterRowAssembly
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenCharacterNorm

/-!
# Ordinary character certificate for the ATLAS degree-12 power-seven row

The isolated presentation and 31-class norm certificates package as the
ordinary row selected by `atlasTwelvePowerSeven`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- The normalized ATLAS degree-12 power-seven ordinary character. -/
def
    alternatingSixAmbientAtlasTwelvePowerSevenOrdinaryCharacterRowCertificate :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate
      .atlasTwelvePowerSeven :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateOfClassValues
    .atlasTwelvePowerSeven
    alternatingSixAmbientAtlasTwelvePowerSevenClassCharacterCertificate

private abbrev powerSevenOrdinaryCertificate :=
  alternatingSixAmbientAtlasTwelvePowerSevenOrdinaryCharacterRowCertificate

/-- The packaged certificate uses its relation-table matrix row. -/
@[simp]
theorem
    alternatingSixAmbientAtlasTwelvePowerSevenOrdinaryCharacterRowCertificate_matrixRow :
    powerSevenOrdinaryCertificate.matrixRow =
      alternatingSixAmbientOrdinaryRelationTable.row
        .atlasTwelvePowerSeven :=
  rfl

end InductiveMcKay
end McKayConjecture
