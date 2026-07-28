/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow21LongWordProductAB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow21LongWordProductABB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow21LongWordProductABBB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow21LongWordProductPrefix77
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow21LongWordProductPrefix79

/-!
# Checked products for the two long row-21 class words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The original row-21 matrices multiply to the reduced `ab` matrix. -/
theorem alternatingSixAmbientRow21_longMatrixAB_eq :
    alternatingSixFiveAmbient_row21_matrixA *
        alternatingSixFiveAmbient_row21_matrixB =
      alternatingSixAmbientRow21LongMatrixAB :=
  alternatingSixAmbientRow21_longMatrixAB_mul

/-- Reduced matrix for the left-associated word `ab²`. -/
theorem alternatingSixAmbientRow21_longMatrixABB_eq :
    (alternatingSixFiveAmbient_row21_matrixA *
      alternatingSixFiveAmbient_row21_matrixB) *
      alternatingSixFiveAmbient_row21_matrixB =
      alternatingSixAmbientRow21LongMatrixABB := by
  rw [alternatingSixAmbientRow21_longMatrixAB_eq,
    alternatingSixAmbientRow21_longMatrixABB_mul]

/-- Reduced matrix for the left-associated word `ab³`. -/
theorem alternatingSixAmbientRow21_longMatrixABBB_eq :
    ((alternatingSixFiveAmbient_row21_matrixA *
        alternatingSixFiveAmbient_row21_matrixB) *
      alternatingSixFiveAmbient_row21_matrixB) *
      alternatingSixFiveAmbient_row21_matrixB =
      alternatingSixAmbientRow21LongMatrixABBB := by
  rw [alternatingSixAmbientRow21_longMatrixABB_eq,
    alternatingSixAmbientRow21_longMatrixABBB_mul]

end InductiveMcKay
end McKayConjecture
