/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassRepresentativeMatrixEvaluation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow24

/-!
# Low-footprint exact matrix certificate for ambient row 24

This module packages only row 24 and its four split presentation-relation
proofs. Consumers evaluating its class representatives therefore need not
import the other degree-five, degree-ten, and degree-fifteen matrix rows.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for ordinary row 24, isolated from the
multi-row relation table. -/
def alternatingSixAmbientRow24ClassMatrixCertificate :
    AlternatingSixSchurMatrixRowCertificate (Fin 10) :=
  alternatingSixAmbientMatrixRowCertificate
    .orderTwo
    alternatingSixFiveAmbient_row24_matrixA
    alternatingSixFiveAmbient_row24_matrixB
    alternatingSixFiveAmbient_row24_matrixA_sq
    alternatingSixFiveAmbient_row24_matrixB_fourth
    alternatingSixFiveAmbient_row24_matrixAB_fifth
    alternatingSixFiveAmbient_row24_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
