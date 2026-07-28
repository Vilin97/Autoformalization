/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow16DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow17DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientTwoGeneratorCharacterRow

/-!
# Initial degree-eight ambient simple instances

The completed ordinary relation table supplies the exact canonical-cover
representations at rows `16` and `17`.  Their diagonal-basis common-commutant
calculations imply that both representations are simple.

This module deliberately exports only two named `Simple` instances.  It does
not define character-row certificates or import character-separation files.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

local instance degreeEightInitialRow16CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row16.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance degreeEightInitialRow17CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row17.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

private abbrev degreeEightInitialRow16MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row16 :=
  alternatingSixAmbientOrdinaryRelationTable.row .row16

private abbrev degreeEightInitialRow17MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row17 :=
  alternatingSixAmbientOrdinaryRelationTable.row .row17

/-- The completed-table representation at ordinary row `16` is simple. -/
instance alternatingSixAmbientDegreeEightInitialRow16RepresentationSimple :
    Simple
      (FDRep.of
        degreeEightInitialRow16MatrixCertificate.universalCoverRepresentation) := by
  apply
    degreeEightInitialRow16MatrixCertificate
      |>.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow16_scalar_commutant X hA hB

/-- The completed-table representation at ordinary row `17` is simple. -/
instance alternatingSixAmbientDegreeEightInitialRow17RepresentationSimple :
    Simple
      (FDRep.of
        degreeEightInitialRow17MatrixCertificate.universalCoverRepresentation) := by
  apply
    degreeEightInitialRow17MatrixCertificate
      |>.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow17_scalar_commutant X hA hB

end InductiveMcKay
end McKayConjecture
