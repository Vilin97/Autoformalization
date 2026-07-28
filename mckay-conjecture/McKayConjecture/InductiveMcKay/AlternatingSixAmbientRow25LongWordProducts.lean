/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25LongWordProductAB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25LongWordProductABB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25LongWordProductABBB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25LongWordProductPrefix77
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25LongWordProductPrefix79

/-!
# Checked products for the two long row-25 class words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The original row-25 matrices multiply to the reduced `ab` matrix. -/
theorem alternatingSixAmbientRow25_longMatrixAB_eq :
    alternatingSixFiveAmbient_row25_matrixA *
        alternatingSixFiveAmbient_row25_matrixB =
      alternatingSixAmbientRow25LongMatrixAB :=
  alternatingSixAmbientRow25_longMatrixAB_mul

/-- Reduced matrix for the left-associated word `ab²`. -/
theorem alternatingSixAmbientRow25_longMatrixABB_eq :
    (alternatingSixFiveAmbient_row25_matrixA *
      alternatingSixFiveAmbient_row25_matrixB) *
      alternatingSixFiveAmbient_row25_matrixB =
      alternatingSixAmbientRow25LongMatrixABB := by
  rw [alternatingSixAmbientRow25_longMatrixAB_eq,
    alternatingSixAmbientRow25_longMatrixABB_mul]

/-- Reduced matrix for the left-associated word `ab³`. -/
theorem alternatingSixAmbientRow25_longMatrixABBB_eq :
    ((alternatingSixFiveAmbient_row25_matrixA *
        alternatingSixFiveAmbient_row25_matrixB) *
      alternatingSixFiveAmbient_row25_matrixB) *
      alternatingSixFiveAmbient_row25_matrixB =
      alternatingSixAmbientRow25LongMatrixABBB := by
  rw [alternatingSixAmbientRow25_longMatrixABB_eq,
    alternatingSixAmbientRow25_longMatrixABBB_mul]

end InductiveMcKay
end McKayConjecture
