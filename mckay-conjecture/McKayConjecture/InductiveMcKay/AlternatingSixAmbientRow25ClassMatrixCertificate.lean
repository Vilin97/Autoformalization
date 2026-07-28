/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassRepresentativeMatrixEvaluation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow25

/-!
# Low-footprint exact matrix certificate for ambient row 25

This module isolates the degree-ten row-25 matrices and their four split
presentation-relation proofs from the rest of the ambient ordinary table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for ordinary row 25. -/
def alternatingSixAmbientRow25ClassMatrixCertificate :
    AlternatingSixSchurMatrixRowCertificate (Fin 10) :=
  alternatingSixAmbientMatrixRowCertificate
    .orderTwo
    alternatingSixFiveAmbient_row25_matrixA
    alternatingSixFiveAmbient_row25_matrixB
    alternatingSixFiveAmbient_row25_matrixA_sq
    alternatingSixFiveAmbient_row25_matrixB_fourth
    alternatingSixFiveAmbient_row25_matrixAB_fifth
    alternatingSixFiveAmbient_row25_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
