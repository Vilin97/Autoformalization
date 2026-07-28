/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassRepresentativeMatrixEvaluation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow21

/-!
# Low-footprint exact matrix certificate for ambient row 21

This module isolates the degree-nine row-21 matrices and their four split
presentation-relation proofs from the rest of the ambient ordinary table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for ordinary row 21. -/
def alternatingSixAmbientRow21ClassMatrixCertificate :
    AlternatingSixSchurMatrixRowCertificate (Fin 9) :=
  alternatingSixAmbientMatrixRowCertificate
    .orderThreePositive
    alternatingSixFiveAmbient_row21_matrixA
    alternatingSixFiveAmbient_row21_matrixB
    alternatingSixFiveAmbient_row21_matrixA_sq
    alternatingSixFiveAmbient_row21_matrixB_fourth
    alternatingSixFiveAmbient_row21_matrixAB_fifth
    alternatingSixFiveAmbient_row21_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
