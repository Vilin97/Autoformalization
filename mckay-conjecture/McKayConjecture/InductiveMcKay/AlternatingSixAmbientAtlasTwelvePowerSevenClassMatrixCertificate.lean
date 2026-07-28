/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassRepresentativeMatrixEvaluation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsAtlas12Power7

/-!
# Matrix certificate for the ATLAS degree-12 power-seven row

This module isolates the degree-twelve power-seven ATLAS matrices and their
four split presentation-relation proofs from the complete ambient relation
table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for the ATLAS degree-12 power-seven row. -/
def alternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate :
    AlternatingSixSchurMatrixRowCertificate (Fin 12) :=
  alternatingSixAmbientMatrixRowCertificate
    .orderSixPositive
    alternatingSixFiveAmbient_atlas12Power7_matrixA
    alternatingSixFiveAmbient_atlas12Power7_matrixB
    alternatingSixFiveAmbient_atlas12Power7_matrixA_sq
    alternatingSixFiveAmbient_atlas12Power7_matrixB_fourth
    alternatingSixFiveAmbient_atlas12Power7_matrixAB_fifth
    alternatingSixFiveAmbient_atlas12Power7_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
