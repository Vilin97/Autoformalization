/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryRows
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow08
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow09
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow23
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow24
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow25
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow30
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow31

/-!
# Degree-five, degree-ten, and degree-fifteen ordinary rows for `6.A₆`

This file packages the generated presentation relations for ordinary rows
`8`, `9`, `23` through `25`, `30`, and `31`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for ordinary row `8`. -/
def alternatingSixAmbientRow08MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row08 :=
  alternatingSixAmbientMatrixRowCertificate
    .trivial
    alternatingSixFiveAmbient_row08_matrixA
    alternatingSixFiveAmbient_row08_matrixB
    alternatingSixFiveAmbient_row08_matrixA_sq
    alternatingSixFiveAmbient_row08_matrixB_fourth
    alternatingSixFiveAmbient_row08_matrixAB_fifth
    alternatingSixFiveAmbient_row08_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `9`. -/
def alternatingSixAmbientRow09MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row09 :=
  alternatingSixAmbientMatrixRowCertificate
    .trivial
    alternatingSixFiveAmbient_row09_matrixA
    alternatingSixFiveAmbient_row09_matrixB
    alternatingSixFiveAmbient_row09_matrixA_sq
    alternatingSixFiveAmbient_row09_matrixB_fourth
    alternatingSixFiveAmbient_row09_matrixAB_fifth
    alternatingSixFiveAmbient_row09_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `23`. -/
def alternatingSixAmbientRow23MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row23 :=
  alternatingSixAmbientMatrixRowCertificate
    .trivial
    alternatingSixFiveAmbient_row23_matrixA
    alternatingSixFiveAmbient_row23_matrixB
    alternatingSixFiveAmbient_row23_matrixA_sq
    alternatingSixFiveAmbient_row23_matrixB_fourth
    alternatingSixFiveAmbient_row23_matrixAB_fifth
    alternatingSixFiveAmbient_row23_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `24`. -/
def alternatingSixAmbientRow24MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row24 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderTwo
    alternatingSixFiveAmbient_row24_matrixA
    alternatingSixFiveAmbient_row24_matrixB
    alternatingSixFiveAmbient_row24_matrixA_sq
    alternatingSixFiveAmbient_row24_matrixB_fourth
    alternatingSixFiveAmbient_row24_matrixAB_fifth
    alternatingSixFiveAmbient_row24_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `25`. -/
def alternatingSixAmbientRow25MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row25 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderTwo
    alternatingSixFiveAmbient_row25_matrixA
    alternatingSixFiveAmbient_row25_matrixB
    alternatingSixFiveAmbient_row25_matrixA_sq
    alternatingSixFiveAmbient_row25_matrixB_fourth
    alternatingSixFiveAmbient_row25_matrixAB_fifth
    alternatingSixFiveAmbient_row25_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `30`. -/
def alternatingSixAmbientRow30MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row30 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderThreePositive
    alternatingSixFiveAmbient_row30_matrixA
    alternatingSixFiveAmbient_row30_matrixB
    alternatingSixFiveAmbient_row30_matrixA_sq
    alternatingSixFiveAmbient_row30_matrixB_fourth
    alternatingSixFiveAmbient_row30_matrixAB_fifth
    alternatingSixFiveAmbient_row30_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `31`. -/
def alternatingSixAmbientRow31MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row31 :=
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
