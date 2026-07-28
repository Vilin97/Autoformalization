/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassRepresentativeMatrixEvaluation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsAtlas12Power2

/-!
# Exact matrix certificate for the ATLAS degree-twelve power-2 row

This module isolates the power-2 matrices and their four split
presentation-relation proofs from the rest of the ambient ordinary table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for the ATLAS power-2 ordinary row. -/
def alternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate :
    AlternatingSixSchurMatrixRowCertificate (Fin 12) :=
  alternatingSixAmbientMatrixRowCertificate
    .orderSixNegative
    alternatingSixFiveAmbient_atlas12Power2_matrixA
    alternatingSixFiveAmbient_atlas12Power2_matrixB
    alternatingSixFiveAmbient_atlas12Power2_matrixA_sq
    alternatingSixFiveAmbient_atlas12Power2_matrixB_fourth
    alternatingSixFiveAmbient_atlas12Power2_matrixAB_fifth
    alternatingSixFiveAmbient_atlas12Power2_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
