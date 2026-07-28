/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientClassRepresentativeMatrixEvaluation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow23

/-!
# Low-footprint exact matrix certificate for ambient row 23

This module isolates the degree-ten row-23 matrices and their four split
presentation-relation proofs from the rest of the ambient ordinary table.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for ordinary row 23. -/
def alternatingSixAmbientRow23ClassMatrixCertificate :
    AlternatingSixSchurMatrixRowCertificate (Fin 10) :=
  alternatingSixAmbientMatrixRowCertificate
    .trivial
    alternatingSixFiveAmbient_row23_matrixA
    alternatingSixFiveAmbient_row23_matrixB
    alternatingSixFiveAmbient_row23_matrixA_sq
    alternatingSixFiveAmbient_row23_matrixB_fourth
    alternatingSixFiveAmbient_row23_matrixAB_fifth
    alternatingSixFiveAmbient_row23_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
