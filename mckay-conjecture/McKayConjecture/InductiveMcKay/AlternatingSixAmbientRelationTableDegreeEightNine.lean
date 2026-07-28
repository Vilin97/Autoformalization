/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryRows
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow16
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow17
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow18
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow19
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow20
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow21
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow22

/-!
# Degree-eight and degree-nine ordinary matrix rows for `6.A₆`

This file packages the generated presentation relations for ordinary rows
`16` through `22`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for ordinary row `16`. -/
def alternatingSixAmbientRow16MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row16 :=
  alternatingSixAmbientMatrixRowCertificate
    .trivial
    alternatingSixFiveAmbient_row16_matrixA
    alternatingSixFiveAmbient_row16_matrixB
    alternatingSixFiveAmbient_row16_matrixA_sq
    alternatingSixFiveAmbient_row16_matrixB_fourth
    alternatingSixFiveAmbient_row16_matrixAB_fifth
    alternatingSixFiveAmbient_row16_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `17`. -/
def alternatingSixAmbientRow17MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row17 :=
  alternatingSixAmbientMatrixRowCertificate
    .trivial
    alternatingSixFiveAmbient_row17_matrixA
    alternatingSixFiveAmbient_row17_matrixB
    alternatingSixFiveAmbient_row17_matrixA_sq
    alternatingSixFiveAmbient_row17_matrixB_fourth
    alternatingSixFiveAmbient_row17_matrixAB_fifth
    alternatingSixFiveAmbient_row17_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `18`. -/
def alternatingSixAmbientRow18MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row18 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderTwo
    alternatingSixFiveAmbient_row18_matrixA
    alternatingSixFiveAmbient_row18_matrixB
    alternatingSixFiveAmbient_row18_matrixA_sq
    alternatingSixFiveAmbient_row18_matrixB_fourth
    alternatingSixFiveAmbient_row18_matrixAB_fifth
    alternatingSixFiveAmbient_row18_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `19`. -/
def alternatingSixAmbientRow19MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row19 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderTwo
    alternatingSixFiveAmbient_row19_matrixA
    alternatingSixFiveAmbient_row19_matrixB
    alternatingSixFiveAmbient_row19_matrixA_sq
    alternatingSixFiveAmbient_row19_matrixB_fourth
    alternatingSixFiveAmbient_row19_matrixAB_fifth
    alternatingSixFiveAmbient_row19_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `20`. -/
def alternatingSixAmbientRow20MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row20 :=
  alternatingSixAmbientMatrixRowCertificate
    .trivial
    alternatingSixFiveAmbient_row20_matrixA
    alternatingSixFiveAmbient_row20_matrixB
    alternatingSixFiveAmbient_row20_matrixA_sq
    alternatingSixFiveAmbient_row20_matrixB_fourth
    alternatingSixFiveAmbient_row20_matrixAB_fifth
    alternatingSixFiveAmbient_row20_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `21`. -/
def alternatingSixAmbientRow21MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row21 :=
  alternatingSixAmbientMatrixRowCertificate
    .orderThreePositive
    alternatingSixFiveAmbient_row21_matrixA
    alternatingSixFiveAmbient_row21_matrixB
    alternatingSixFiveAmbient_row21_matrixA_sq
    alternatingSixFiveAmbient_row21_matrixB_fourth
    alternatingSixFiveAmbient_row21_matrixAB_fifth
    alternatingSixFiveAmbient_row21_matrixABSquared_fifth

/-- Exact presentation certificate for ordinary row `22`. -/
def alternatingSixAmbientRow22MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row22 :=
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
