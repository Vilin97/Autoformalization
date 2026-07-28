/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassRepresentativeMatrixEvaluation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow22

/-!
# Low-footprint exact matrix certificate for ambient row 22

This module isolates the degree-nine row-22 matrices and their four split
presentation-relation proofs from the rest of the ambient ordinary table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for ordinary row 22. -/
def alternatingSixAmbientRow22ClassMatrixCertificate :
    AlternatingSixSchurMatrixRowCertificate (Fin 9) :=
  alternatingSixAmbientMatrixRowCertificate
    .orderThreeNegative
    alternatingSixFiveAmbient_row22_matrixA
    alternatingSixFiveAmbient_row22_matrixB
    alternatingSixFiveAmbient_row22_matrixA_sq
    alternatingSixFiveAmbient_row22_matrixB_fourth
    alternatingSixFiveAmbient_row22_matrixAB_fifth
    alternatingSixFiveAmbient_row22_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
