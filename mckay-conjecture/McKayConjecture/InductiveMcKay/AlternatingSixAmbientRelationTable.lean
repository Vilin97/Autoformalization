/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTableDegreeOneThree
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTableDegreeFourSix
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTableDegreeFiveTenFifteen
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTableDegreeEightNine
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTableDegreeTwelve

/-!
# Complete ordinary relation table for `6.A₆`

The degree-specific files check and package the thirty-one generated matrix
rows.  This file merely assembles them into the dependent table interface.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact generator matrices and presentation proofs for all thirty-one
ordinary rows of the canonical sixfold cover of `A₆`. -/
def alternatingSixAmbientOrdinaryRelationTable :
    AlternatingSixAmbientOrdinaryRelationTableCertificate where
  row
    | .row01 => alternatingSixAmbientRow01MatrixCertificate
    | .row02 => alternatingSixAmbientRow02MatrixCertificate
    | .row03 => alternatingSixAmbientRow03MatrixCertificate
    | .row04 => alternatingSixAmbientRow04MatrixCertificate
    | .row05 => alternatingSixAmbientRow05MatrixCertificate
    | .row06 => alternatingSixAmbientRow06MatrixCertificate
    | .row07 => alternatingSixAmbientRow07MatrixCertificate
    | .row08 => alternatingSixAmbientRow08MatrixCertificate
    | .row09 => alternatingSixAmbientRow09MatrixCertificate
    | .row10 => alternatingSixAmbientRow10MatrixCertificate
    | .row11 => alternatingSixAmbientRow11MatrixCertificate
    | .row12 => alternatingSixAmbientRow12MatrixCertificate
    | .row13 => alternatingSixAmbientRow13MatrixCertificate
    | .row14 => alternatingSixAmbientRow14MatrixCertificate
    | .row15 => alternatingSixAmbientRow15MatrixCertificate
    | .row16 => alternatingSixAmbientRow16MatrixCertificate
    | .row17 => alternatingSixAmbientRow17MatrixCertificate
    | .row18 => alternatingSixAmbientRow18MatrixCertificate
    | .row19 => alternatingSixAmbientRow19MatrixCertificate
    | .row20 => alternatingSixAmbientRow20MatrixCertificate
    | .row21 => alternatingSixAmbientRow21MatrixCertificate
    | .row22 => alternatingSixAmbientRow22MatrixCertificate
    | .row23 => alternatingSixAmbientRow23MatrixCertificate
    | .row24 => alternatingSixAmbientRow24MatrixCertificate
    | .row25 => alternatingSixAmbientRow25MatrixCertificate
    | .row30 => alternatingSixAmbientRow30MatrixCertificate
    | .row31 => alternatingSixAmbientRow31MatrixCertificate
    | .atlasTwelvePowerOne =>
        alternatingSixAmbientAtlasTwelvePowerOneMatrixCertificate
    | .atlasTwelvePowerTwo =>
        alternatingSixAmbientAtlasTwelvePowerTwoMatrixCertificate
    | .atlasTwelvePowerSeven =>
        alternatingSixAmbientAtlasTwelvePowerSevenMatrixCertificate
    | .atlasTwelvePowerEleven =>
        alternatingSixAmbientAtlasTwelvePowerElevenMatrixCertificate

end InductiveMcKay
end McKayConjecture
