/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassRepresentativeMatrixEvaluation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsAtlas12Power11

/-!
# Low-footprint matrix certificate for ATLAS degree 12, power 11

This module isolates the eleventh-power ATLAS matrices and their four split
presentation-relation proofs from the complete ambient relation table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for the eleventh-power ATLAS row. -/
def alternatingSixAmbientAtlas12P11ClassMatrixCertificate :
    AlternatingSixSchurMatrixRowCertificate (Fin 12) :=
  alternatingSixAmbientMatrixRowCertificate
    .orderSixNegative
    alternatingSixFiveAmbient_atlas12Power11_matrixA
    alternatingSixFiveAmbient_atlas12Power11_matrixB
    alternatingSixFiveAmbient_atlas12Power11_matrixA_sq
    alternatingSixFiveAmbient_atlas12Power11_matrixB_fourth
    alternatingSixFiveAmbient_atlas12Power11_matrixAB_fifth
    alternatingSixFiveAmbient_atlas12Power11_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
