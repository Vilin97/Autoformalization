/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryRows
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsAtlas12Power1
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsAtlas12Power2
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsAtlas12Power7
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsAtlas12Power11

/-!
# Degree-twelve ordinary matrix rows for `6.A₆`

This file packages the four Galois powers of the sparse characteristic-zero
ATLAS representation into the reusable ambient matrix-row interface.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact presentation certificate for the first degree-twelve Galois row. -/
def alternatingSixAmbientAtlasTwelvePowerOneMatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .atlasTwelvePowerOne :=
  alternatingSixAmbientMatrixRowCertificate
    .orderSixPositive
    alternatingSixFiveAmbient_atlas12Power1_matrixA
    alternatingSixFiveAmbient_atlas12Power1_matrixB
    alternatingSixFiveAmbient_atlas12Power1_matrixA_sq
    alternatingSixFiveAmbient_atlas12Power1_matrixB_fourth
    alternatingSixFiveAmbient_atlas12Power1_matrixAB_fifth
    alternatingSixFiveAmbient_atlas12Power1_matrixABSquared_fifth

/-- Exact presentation certificate for the second degree-twelve Galois row. -/
def alternatingSixAmbientAtlasTwelvePowerTwoMatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .atlasTwelvePowerTwo :=
  alternatingSixAmbientMatrixRowCertificate
    .orderSixNegative
    alternatingSixFiveAmbient_atlas12Power2_matrixA
    alternatingSixFiveAmbient_atlas12Power2_matrixB
    alternatingSixFiveAmbient_atlas12Power2_matrixA_sq
    alternatingSixFiveAmbient_atlas12Power2_matrixB_fourth
    alternatingSixFiveAmbient_atlas12Power2_matrixAB_fifth
    alternatingSixFiveAmbient_atlas12Power2_matrixABSquared_fifth

/-- Exact presentation certificate for the seventh degree-twelve Galois row. -/
def alternatingSixAmbientAtlasTwelvePowerSevenMatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .atlasTwelvePowerSeven :=
  alternatingSixAmbientMatrixRowCertificate
    .orderSixPositive
    alternatingSixFiveAmbient_atlas12Power7_matrixA
    alternatingSixFiveAmbient_atlas12Power7_matrixB
    alternatingSixFiveAmbient_atlas12Power7_matrixA_sq
    alternatingSixFiveAmbient_atlas12Power7_matrixB_fourth
    alternatingSixFiveAmbient_atlas12Power7_matrixAB_fifth
    alternatingSixFiveAmbient_atlas12Power7_matrixABSquared_fifth

/-- Exact presentation certificate for the eleventh degree-twelve Galois row. -/
def alternatingSixAmbientAtlasTwelvePowerElevenMatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .atlasTwelvePowerEleven :=
  alternatingSixAmbientMatrixRowCertificate
    .orderSixNegative
    alternatingSixFiveAmbient_atlas12Power11_matrixA
    alternatingSixFiveAmbient_atlas12Power11_matrixB
    alternatingSixFiveAmbient_atlas12Power11_matrixA_sq
    alternatingSixFiveAmbient_atlas12Power11_matrixB_fourth
    alternatingSixFiveAmbient_atlas12Power11_matrixAB_fifth
    alternatingSixFiveAmbient_atlas12Power11_matrixABSquared_fifth

end InductiveMcKay
end McKayConjecture
