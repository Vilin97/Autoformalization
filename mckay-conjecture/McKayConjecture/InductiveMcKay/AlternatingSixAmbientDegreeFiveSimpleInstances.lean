/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryRows
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow08DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow09DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientScalarPattern
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientTwoGeneratorCharacterRow
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow08
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow09

/-!
# Simplicity of the degree-five ambient rows

The exact relation certificates for ordinary rows `08` and `09` are combined
with their scalar common-commutant proofs.  This module deliberately contains
only the named `Simple` instances, so character-row and trace-separation
interfaces can import it without introducing a dependency cycle.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance row08CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row08.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance row09CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row09.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

private abbrev row08MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row08 :=
  alternatingSixAmbientMatrixRowCertificate
    .trivial
    alternatingSixFiveAmbient_row08_matrixA
    alternatingSixFiveAmbient_row08_matrixB
    alternatingSixFiveAmbient_row08_matrixA_sq
    alternatingSixFiveAmbient_row08_matrixB_fourth
    alternatingSixFiveAmbient_row08_matrixAB_fifth
    alternatingSixFiveAmbient_row08_matrixABSquared_fifth

private abbrev row09MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row09 :=
  alternatingSixAmbientMatrixRowCertificate
    .trivial
    alternatingSixFiveAmbient_row09_matrixA
    alternatingSixFiveAmbient_row09_matrixB
    alternatingSixFiveAmbient_row09_matrixA_sq
    alternatingSixFiveAmbient_row09_matrixB_fourth
    alternatingSixFiveAmbient_row09_matrixAB_fifth
    alternatingSixFiveAmbient_row09_matrixABSquared_fifth

/-- The row 08 canonical-cover representation is simple. -/
instance alternatingSixAmbientRow08RepresentationSimple :
    Simple
      (FDRep.of
        row08MatrixCertificate.universalCoverRepresentation) := by
  apply
    row08MatrixCertificate.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow08_scalar_commutant X hA hB

/-- The row 09 canonical-cover representation is simple. -/
instance alternatingSixAmbientRow09RepresentationSimple :
    Simple
      (FDRep.of
        row09MatrixCertificate.universalCoverRepresentation) := by
  apply
    row09MatrixCertificate.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow09_scalar_commutant X hA hB

end InductiveMcKay
end McKayConjecture
