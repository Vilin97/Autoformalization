/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassRepresentativeMatrixEvaluation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsAtlas12Power1

/-!
# Low-footprint matrix certificate for ATLAS degree 12, power 1

This module isolates the first degree-twelve ATLAS matrices and their four
split presentation-relation proofs from the complete ambient relation table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for the first degree-twelve ATLAS row. -/
def alternatingSixAmbientAtlas12P1ClassMatrixCertificate :
    AlternatingSixSchurMatrixRowCertificate (Fin 12) :=
  alternatingSixAmbientMatrixRowCertificate
    .orderSixPositive
    alternatingSixFiveAmbient_atlas12Power1_matrixA
    alternatingSixFiveAmbient_atlas12Power1_matrixB
    alternatingSixFiveAmbient_atlas12Power1_matrixA_sq
    alternatingSixFiveAmbient_atlas12Power1_matrixB_fourth
    alternatingSixFiveAmbient_atlas12Power1_matrixAB_fifth
    alternatingSixFiveAmbient_atlas12Power1_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
