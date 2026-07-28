/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTable
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientTwoGeneratorCharacterRow

/-!
# Ambient row 18 simple instance

The completed ordinary relation table supplies the canonical-cover
representation at row `18`. Its common-commutant calculation implies that
the representation is simple.

This module deliberately exports only the named `Simple` instance. It does
not define a character-row certificate or import character-separation files.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

local instance row18CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row18.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

private abbrev row18MatrixCertificate :
    AlternatingSixAmbientOrdinaryMatrixRowCertificate .row18 :=
  alternatingSixAmbientOrdinaryRelationTable.row .row18

/-- The completed-table representation at ordinary row `18` is simple. -/
instance alternatingSixAmbientRow18RepresentationSimple :
    Simple (FDRep.of row18MatrixCertificate.universalCoverRepresentation) := by
  apply
    row18MatrixCertificate
      |>.universalCoverRepresentation_simple_of_scalar_commutant
  intro X hA hB
  exact alternatingSixAmbientRow18_scalar_commutant X hA hB

end InductiveMcKay
end McKayConjecture
