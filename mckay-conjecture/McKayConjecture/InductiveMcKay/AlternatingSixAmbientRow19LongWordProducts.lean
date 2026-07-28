/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19LongWordProductAB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19LongWordProductABB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19LongWordProductABBB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19LongWordProductPrefix77
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19LongWordProductPrefix79

/-!
# Checked products for the two long row-19 class words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The original row-19 matrices multiply to the reduced `ab` matrix. -/
theorem alternatingSixAmbientRow19_longMatrixAB_eq :
    alternatingSixFiveAmbient_row19_matrixA *
        alternatingSixFiveAmbient_row19_matrixB =
      alternatingSixAmbientRow19LongMatrixAB :=
  alternatingSixAmbientRow19_longMatrixAB_mul

/-- Reduced matrix for the left-associated word `ab²`. -/
theorem alternatingSixAmbientRow19_longMatrixABB_eq :
    (alternatingSixFiveAmbient_row19_matrixA *
      alternatingSixFiveAmbient_row19_matrixB) *
      alternatingSixFiveAmbient_row19_matrixB =
      alternatingSixAmbientRow19LongMatrixABB := by
  rw [alternatingSixAmbientRow19_longMatrixAB_eq,
    alternatingSixAmbientRow19_longMatrixABB_mul]

/-- Reduced matrix for the left-associated word `ab³`. -/
theorem alternatingSixAmbientRow19_longMatrixABBB_eq :
    ((alternatingSixFiveAmbient_row19_matrixA *
        alternatingSixFiveAmbient_row19_matrixB) *
      alternatingSixFiveAmbient_row19_matrixB) *
      alternatingSixFiveAmbient_row19_matrixB =
      alternatingSixAmbientRow19LongMatrixABBB := by
  rw [alternatingSixAmbientRow19_longMatrixABB_eq,
    alternatingSixAmbientRow19_longMatrixABBB_mul]

end InductiveMcKay
end McKayConjecture
