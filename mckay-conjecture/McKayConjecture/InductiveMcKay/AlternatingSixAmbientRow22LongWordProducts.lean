/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow22LongWordProductAB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow22LongWordProductABB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow22LongWordProductABBB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow22LongWordProductPrefix77
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow22LongWordProductPrefix79

/-!
# Checked products for the two long row-22 class words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The original row-22 matrices multiply to the reduced `ab` matrix. -/
theorem alternatingSixAmbientRow22_longMatrixAB_eq :
    alternatingSixFiveAmbient_row22_matrixA *
        alternatingSixFiveAmbient_row22_matrixB =
      alternatingSixAmbientRow22LongMatrixAB :=
  alternatingSixAmbientRow22_longMatrixAB_mul

/-- Reduced matrix for the left-associated word `ab²`. -/
theorem alternatingSixAmbientRow22_longMatrixABB_eq :
    (alternatingSixFiveAmbient_row22_matrixA *
      alternatingSixFiveAmbient_row22_matrixB) *
      alternatingSixFiveAmbient_row22_matrixB =
      alternatingSixAmbientRow22LongMatrixABB := by
  rw [alternatingSixAmbientRow22_longMatrixAB_eq,
    alternatingSixAmbientRow22_longMatrixABB_mul]

/-- Reduced matrix for the left-associated word `ab³`. -/
theorem alternatingSixAmbientRow22_longMatrixABBB_eq :
    ((alternatingSixFiveAmbient_row22_matrixA *
        alternatingSixFiveAmbient_row22_matrixB) *
      alternatingSixFiveAmbient_row22_matrixB) *
      alternatingSixFiveAmbient_row22_matrixB =
      alternatingSixAmbientRow22LongMatrixABBB := by
  rw [alternatingSixAmbientRow22_longMatrixABB_eq,
    alternatingSixAmbientRow22_longMatrixABBB_mul]

end InductiveMcKay
end McKayConjecture
