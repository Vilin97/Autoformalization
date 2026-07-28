/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassRepresentativeMatrixEvaluation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow19

/-!
# Low-footprint exact matrix certificate for ambient row 19

This module packages only row 19 and its four split presentation-relation
proofs.  In particular, consumers evaluating its class representatives need
not import the other degree-eight and degree-nine matrix rows.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for ordinary row 19, isolated from the
multi-row relation table. -/
def alternatingSixAmbientRow19ClassMatrixCertificate :
    AlternatingSixSchurMatrixRowCertificate (Fin 8) :=
  alternatingSixAmbientMatrixRowCertificate
    .orderTwo
    alternatingSixFiveAmbient_row19_matrixA
    alternatingSixFiveAmbient_row19_matrixB
    alternatingSixFiveAmbient_row19_matrixA_sq
    alternatingSixFiveAmbient_row19_matrixB_fourth
    alternatingSixFiveAmbient_row19_matrixAB_fifth
    alternatingSixFiveAmbient_row19_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
