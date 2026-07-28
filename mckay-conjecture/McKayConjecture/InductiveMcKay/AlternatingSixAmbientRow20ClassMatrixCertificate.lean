/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassRepresentativeMatrixEvaluation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow20

/-!
# Low-footprint exact matrix certificate for ambient row 20

This module packages only row 20 and its four split presentation-relation
proofs. Consumers evaluating its class representatives therefore avoid
importing the other degree-eight and degree-nine matrix rows.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for ordinary row 20, isolated from the
multi-row relation table. -/
def alternatingSixAmbientRow20ClassMatrixCertificate :
    AlternatingSixSchurMatrixRowCertificate (Fin 9) :=
  alternatingSixAmbientMatrixRowCertificate
    .trivial
    alternatingSixFiveAmbient_row20_matrixA
    alternatingSixFiveAmbient_row20_matrixB
    alternatingSixFiveAmbient_row20_matrixA_sq
    alternatingSixFiveAmbient_row20_matrixB_fourth
    alternatingSixFiveAmbient_row20_matrixAB_fifth
    alternatingSixFiveAmbient_row20_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
