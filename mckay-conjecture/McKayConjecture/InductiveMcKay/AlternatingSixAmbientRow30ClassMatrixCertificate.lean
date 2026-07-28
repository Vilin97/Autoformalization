/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassRepresentativeMatrixEvaluation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow30

/-!
# Low-footprint exact matrix certificate for ambient row 30

This module isolates the degree-fifteen row-30 matrices and their four split
presentation-relation proofs from the rest of the ambient ordinary table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for ordinary row 30. -/
def alternatingSixAmbientRow30ClassMatrixCertificate :
    AlternatingSixSchurMatrixRowCertificate (Fin 15) :=
  alternatingSixAmbientMatrixRowCertificate
    .orderThreePositive
    alternatingSixFiveAmbient_row30_matrixA
    alternatingSixFiveAmbient_row30_matrixB
    alternatingSixFiveAmbient_row30_matrixA_sq
    alternatingSixFiveAmbient_row30_matrixB_fourth
    alternatingSixFiveAmbient_row30_matrixAB_fifth
    alternatingSixFiveAmbient_row30_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
