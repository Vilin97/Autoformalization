/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryRows
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow06
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow07
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow10
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow11
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow12
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow13
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow14
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow15

/-!
# Degree-four and degree-six ordinary matrix rows for `6.A₆`

This file packages the generated presentation relations for ordinary rows
`6`, `7`, and `10` through `15`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for ordinary row `6`. -/
def alternatingSixAmbientRow06MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row06 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderTwo
    alternatingSixFiveAmbient_row06_matrixA
    alternatingSixFiveAmbient_row06_matrixB
    alternatingSixFiveAmbient_row06_matrixA_sq
    alternatingSixFiveAmbient_row06_matrixB_fourth
    alternatingSixFiveAmbient_row06_matrixAB_fifth
    alternatingSixFiveAmbient_row06_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `7`. -/
def alternatingSixAmbientRow07MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row07 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderTwo
    alternatingSixFiveAmbient_row07_matrixA
    alternatingSixFiveAmbient_row07_matrixB
    alternatingSixFiveAmbient_row07_matrixA_sq
    alternatingSixFiveAmbient_row07_matrixB_fourth
    alternatingSixFiveAmbient_row07_matrixAB_fifth
    alternatingSixFiveAmbient_row07_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `10`. -/
def alternatingSixAmbientRow10MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row10 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderThreePositive
    alternatingSixFiveAmbient_row10_matrixA
    alternatingSixFiveAmbient_row10_matrixB
    alternatingSixFiveAmbient_row10_matrixA_sq
    alternatingSixFiveAmbient_row10_matrixB_fourth
    alternatingSixFiveAmbient_row10_matrixAB_fifth
    alternatingSixFiveAmbient_row10_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `11`. -/
def alternatingSixAmbientRow11MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row11 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderThreeNegative
    alternatingSixFiveAmbient_row11_matrixA
    alternatingSixFiveAmbient_row11_matrixB
    alternatingSixFiveAmbient_row11_matrixA_sq
    alternatingSixFiveAmbient_row11_matrixB_fourth
    alternatingSixFiveAmbient_row11_matrixAB_fifth
    alternatingSixFiveAmbient_row11_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `12`. -/
def alternatingSixAmbientRow12MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row12 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderSixPositive
    alternatingSixFiveAmbient_row12_matrixA
    alternatingSixFiveAmbient_row12_matrixB
    alternatingSixFiveAmbient_row12_matrixA_sq
    alternatingSixFiveAmbient_row12_matrixB_fourth
    alternatingSixFiveAmbient_row12_matrixAB_fifth
    alternatingSixFiveAmbient_row12_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `13`. -/
def alternatingSixAmbientRow13MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row13 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderSixPositive
    alternatingSixFiveAmbient_row13_matrixA
    alternatingSixFiveAmbient_row13_matrixB
    alternatingSixFiveAmbient_row13_matrixA_sq
    alternatingSixFiveAmbient_row13_matrixB_fourth
    alternatingSixFiveAmbient_row13_matrixAB_fifth
    alternatingSixFiveAmbient_row13_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `14`. -/
def alternatingSixAmbientRow14MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row14 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderSixNegative
    alternatingSixFiveAmbient_row14_matrixA
    alternatingSixFiveAmbient_row14_matrixB
    alternatingSixFiveAmbient_row14_matrixA_sq
    alternatingSixFiveAmbient_row14_matrixB_fourth
    alternatingSixFiveAmbient_row14_matrixAB_fifth
    alternatingSixFiveAmbient_row14_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `15`. -/
def alternatingSixAmbientRow15MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row15 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderSixNegative
    alternatingSixFiveAmbient_row15_matrixA
    alternatingSixFiveAmbient_row15_matrixB
    alternatingSixFiveAmbient_row15_matrixA_sq
    alternatingSixFiveAmbient_row15_matrixB_fourth
    alternatingSixFiveAmbient_row15_matrixAB_fifth
    alternatingSixFiveAmbient_row15_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
