/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassRepresentativeMatrixEvaluation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow31

/-!
# Low-footprint exact matrix certificate for ambient row 31

This module isolates the degree-fifteen row-31 matrices and their four split
presentation-relation proofs from the rest of the ambient ordinary table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for ordinary row 31. -/
def alternatingSixAmbientRow31ClassMatrixCertificate :
    AlternatingSixSchurMatrixRowCertificate (Fin 15) :=
  alternatingSixAmbientMatrixRowCertificate
    .orderThreeNegative
    alternatingSixFiveAmbient_row31_matrixA
    alternatingSixFiveAmbient_row31_matrixB
    alternatingSixFiveAmbient_row31_matrixA_sq
    alternatingSixFiveAmbient_row31_matrixB_fourth
    alternatingSixFiveAmbient_row31_matrixAB_fifth
    alternatingSixFiveAmbient_row31_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
