/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTableDegreeOneThree
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTableDegreeFourSix
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTableDegreeEightNine
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientRows

/-!
# Compatibility aliases for initial five-local ambient representations

The complete ordinary relation table supersedes the original four-row
milestone.  This file retains its public names as thin aliases to the
degree-specific ordinary certificates.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- Compatibility alias for the exact certificate at ambient GAP row `2`. -/
def alternatingSixFiveAmbientRow02MatrixCertificate :
    AlternatingSixFiveAmbientMatrixRowCertificate .row02 :=
  alternatingSixAmbientRow02MatrixCertificate

/-- Compatibility alias for the exact certificate at ambient GAP row `6`. -/
def alternatingSixFiveAmbientRow06MatrixCertificate :
    AlternatingSixFiveAmbientMatrixRowCertificate .row06 :=
  alternatingSixAmbientRow06MatrixCertificate

/-- Compatibility alias for the exact certificate at ambient GAP row `10`. -/
def alternatingSixFiveAmbientRow10MatrixCertificate :
    AlternatingSixFiveAmbientMatrixRowCertificate .row10 :=
  alternatingSixAmbientRow10MatrixCertificate

/-- Compatibility alias for the exact certificate at ambient GAP row `16`. -/
def alternatingSixFiveAmbientRow16MatrixCertificate :
    AlternatingSixFiveAmbientMatrixRowCertificate .row16 :=
  alternatingSixAmbientRow16MatrixCertificate

/-- Compatibility alias for the exact `GL₃(ℂ)` representation afforded by
ambient row `2`. -/
def alternatingSixFiveAmbientRow02GLRepresentation :
    AlternatingSixUniversalCover →*
      Matrix.GeneralLinearGroup (Fin 3) ℂ :=
  alternatingSixFiveAmbientRow02MatrixCertificate
    |>.universalCoverGLRepresentation

/-- Compatibility alias for the exact `GL₄(ℂ)` representation afforded by
ambient row `6`. -/
def alternatingSixFiveAmbientRow06GLRepresentation :
    AlternatingSixUniversalCover →*
      Matrix.GeneralLinearGroup (Fin 4) ℂ :=
  alternatingSixFiveAmbientRow06MatrixCertificate
    |>.universalCoverGLRepresentation

/-- Compatibility alias for the exact `GL₆(ℂ)` representation afforded by
ambient row `10`. -/
def alternatingSixFiveAmbientRow10GLRepresentation :
    AlternatingSixUniversalCover →*
      Matrix.GeneralLinearGroup (Fin 6) ℂ :=
  alternatingSixFiveAmbientRow10MatrixCertificate
    |>.universalCoverGLRepresentation

/-- Compatibility alias for the exact `GL₈(ℂ)` representation afforded by
ambient row `16`. -/
def alternatingSixFiveAmbientRow16GLRepresentation :
    AlternatingSixUniversalCover →*
      Matrix.GeneralLinearGroup (Fin 8) ℂ :=
  alternatingSixFiveAmbientRow16MatrixCertificate
    |>.universalCoverGLRepresentation

end InductiveMcKay
end McKayConjecture
