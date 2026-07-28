/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryCharacterRowAssembly
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoCharacterNorm

/-!
# Ordinary character certificate for the ATLAS degree-12 power-two row

The isolated presentation and exact 31-class norm certificates package as the
ordinary row selected by `atlasTwelvePowerTwo`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- The normalized ATLAS degree-12 power-two ordinary character. -/
def
    alternatingSixAmbientAtlasTwelvePowerTwoOrdinaryCharacterRowCertificate :
    AlternatingSixAmbientOrdinaryCharacterRowCertificate
      .atlasTwelvePowerTwo :=
  alternatingSixAmbientOrdinaryCharacterRowCertificateOfClassValues
    .atlasTwelvePowerTwo
    alternatingSixAmbientAtlasTwelvePowerTwoClassCharacterCertificate

/-- The packaged certificate uses its relation-table matrix row. -/
@[simp]
theorem
    alternatingSixAmbientAtlasTwelvePowerTwoOrdinaryCharacterRowCertificate_matrixRow :
    (alternatingSixAmbientAtlasTwelvePowerTwoOrdinaryCharacterRowCertificate
      ).matrixRow =
      alternatingSixAmbientOrdinaryRelationTable.row
        .atlasTwelvePowerTwo :=
  rfl

end InductiveMcKay
end McKayConjecture
