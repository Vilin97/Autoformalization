/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryRows
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow01
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow02
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow03
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow04
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow05

/-!
# Degree-one and degree-three ordinary matrix rows for `6.A₆`

This file packages the generated presentation relations for ordinary rows
`1` through `5` into the reusable ambient matrix-row interface.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for the degree-one ordinary row. -/
def alternatingSixAmbientRow01MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row01 :=
  alternatingSixAmbientMatrixRowCertificate
    .trivial
    alternatingSixFiveAmbient_row01_matrixA
    alternatingSixFiveAmbient_row01_matrixB
    alternatingSixFiveAmbient_row01_matrixA_sq
    alternatingSixFiveAmbient_row01_matrixB_fourth
    alternatingSixFiveAmbient_row01_matrixAB_fifth
    alternatingSixFiveAmbient_row01_matrixABSquared_fifth

/-- Exact presentation certificate for the first positive order-three row. -/
def alternatingSixAmbientRow02MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row02 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderThreePositive
    alternatingSixFiveAmbient_row02_matrixA
    alternatingSixFiveAmbient_row02_matrixB
    alternatingSixFiveAmbient_row02_matrixA_sq
    alternatingSixFiveAmbient_row02_matrixB_fourth
    alternatingSixFiveAmbient_row02_matrixAB_fifth
    alternatingSixFiveAmbient_row02_matrixABSquared_fifth

/-- Exact presentation certificate for the second positive order-three row. -/
def alternatingSixAmbientRow03MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row03 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderThreePositive
    alternatingSixFiveAmbient_row03_matrixA
    alternatingSixFiveAmbient_row03_matrixB
    alternatingSixFiveAmbient_row03_matrixA_sq
    alternatingSixFiveAmbient_row03_matrixB_fourth
    alternatingSixFiveAmbient_row03_matrixAB_fifth
    alternatingSixFiveAmbient_row03_matrixABSquared_fifth

/-- Exact presentation certificate for the first negative order-three row. -/
def alternatingSixAmbientRow04MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row04 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderThreeNegative
    alternatingSixFiveAmbient_row04_matrixA
    alternatingSixFiveAmbient_row04_matrixB
    alternatingSixFiveAmbient_row04_matrixA_sq
    alternatingSixFiveAmbient_row04_matrixB_fourth
    alternatingSixFiveAmbient_row04_matrixAB_fifth
    alternatingSixFiveAmbient_row04_matrixABSquared_fifth

/-- Exact presentation certificate for the second negative order-three row. -/
def alternatingSixAmbientRow05MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row05 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderThreeNegative
    alternatingSixFiveAmbient_row05_matrixA
    alternatingSixFiveAmbient_row05_matrixB
    alternatingSixFiveAmbient_row05_matrixA_sq
    alternatingSixFiveAmbient_row05_matrixB_fourth
    alternatingSixFiveAmbient_row05_matrixAB_fifth
    alternatingSixFiveAmbient_row05_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
