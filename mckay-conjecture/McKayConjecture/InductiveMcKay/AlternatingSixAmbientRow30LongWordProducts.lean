/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow30LongWordProductAB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow30LongWordProductABB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow30LongWordProductABBB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow30LongWordProductPrefix77
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow30LongWordProductPrefix79

/-!
# Checked products for the two long row-30 class words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The original row-30 matrices multiply to the reduced `ab` matrix. -/
theorem alternatingSixAmbientRow30_longMatrixAB_eq :
    alternatingSixFiveAmbient_row30_matrixA *
        alternatingSixFiveAmbient_row30_matrixB =
      alternatingSixAmbientRow30LongMatrixAB :=
  alternatingSixAmbientRow30_longMatrixAB_mul

/-- Reduced matrix for the left-associated word `ab²`. -/
theorem alternatingSixAmbientRow30_longMatrixABB_eq :
    (alternatingSixFiveAmbient_row30_matrixA *
      alternatingSixFiveAmbient_row30_matrixB) *
      alternatingSixFiveAmbient_row30_matrixB =
      alternatingSixAmbientRow30LongMatrixABB := by
  rw [alternatingSixAmbientRow30_longMatrixAB_eq,
    alternatingSixAmbientRow30_longMatrixABB_mul]

/-- Reduced matrix for the left-associated word `ab³`. -/
theorem alternatingSixAmbientRow30_longMatrixABBB_eq :
    ((alternatingSixFiveAmbient_row30_matrixA *
        alternatingSixFiveAmbient_row30_matrixB) *
      alternatingSixFiveAmbient_row30_matrixB) *
      alternatingSixFiveAmbient_row30_matrixB =
      alternatingSixAmbientRow30LongMatrixABBB := by
  rw [alternatingSixAmbientRow30_longMatrixABB_eq,
    alternatingSixAmbientRow30_longMatrixABBB_mul]

end InductiveMcKay
end McKayConjecture
