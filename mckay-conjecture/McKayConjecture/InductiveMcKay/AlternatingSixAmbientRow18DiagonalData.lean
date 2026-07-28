/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18TransformedDataRow7

/-!
# Checked diagonal data for ambient row 18

This wrapper assembles the independently checked transformed-generator rows
and preserves the public diagonal-data import path.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Exact second stage of the row 18 generator
conjugation. -/
theorem alternatingSixAmbientRow18TransformedGeneratorA_fromIntermediate_eq :
    alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis =
      alternatingSixAmbientRow18TransformedGeneratorA := by
  ext i j
  fin_cases i
  · exact alternatingSixAmbientRow18TransformedGeneratorA_fromIntermediate_row0 j
  · exact alternatingSixAmbientRow18TransformedGeneratorA_fromIntermediate_row1 j
  · exact alternatingSixAmbientRow18TransformedGeneratorA_fromIntermediate_row2 j
  · exact alternatingSixAmbientRow18TransformedGeneratorA_fromIntermediate_row3 j
  · exact alternatingSixAmbientRow18TransformedGeneratorA_fromIntermediate_row4 j
  · exact alternatingSixAmbientRow18TransformedGeneratorA_fromIntermediate_row5 j
  · exact alternatingSixAmbientRow18TransformedGeneratorA_fromIntermediate_row6 j
  · exact alternatingSixAmbientRow18TransformedGeneratorA_fromIntermediate_row7 j

/-- Exact conjugation formula for the row 18 first generator. -/
theorem alternatingSixAmbientRow18TransformedGeneratorA_eq :
    alternatingSixAmbientRow18EigenbasisInverse *
        alternatingSixFiveAmbient_row18_matrixA *
        alternatingSixAmbientRow18Eigenbasis =
      alternatingSixAmbientRow18TransformedGeneratorA := by
  rw [alternatingSixAmbientRow18InverseTimesGeneratorA_eq]
  exact
    alternatingSixAmbientRow18TransformedGeneratorA_fromIntermediate_eq


end InductiveMcKay
end McKayConjecture
