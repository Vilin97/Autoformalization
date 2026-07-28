/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTable

/-!
# Scalar metadata for the ordinary relation table of `6.A₆`

Every generated matrix row is built from the scalar pattern recorded by its
ordinary-row index.  This module exposes that definitional agreement once, so
character-row assembly cannot accidentally pair exact matrices with unrelated
central-character metadata.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- The four exact relator scalars in every ordinary relation-table row agree
with the scalar pattern advertised by its row index. -/
theorem alternatingSixAmbientOrdinaryRelationTable_relatorScalar_eq_scalarPattern
    (row : AlternatingSixAmbientOrdinaryRow) (i : Fin 4) :
    (alternatingSixAmbientOrdinaryRelationTable.row row).relatorScalar i =
      alternatingSixComplexCyclotomicRoot ^
        row.scalarPattern.exponent i := by
  cases row <;> rfl

end InductiveMcKay
end McKayConjecture
