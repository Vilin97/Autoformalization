/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow20LongWordProductAB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow20LongWordProductABB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow20LongWordProductABBB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow20LongWordProductPrefix77
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow20LongWordProductPrefix79

/-!
# Checked products for the two long row-20 class words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The original row-20 matrices multiply to the reduced `ab` matrix. -/
theorem alternatingSixAmbientRow20_longMatrixAB_eq :
    alternatingSixFiveAmbient_row20_matrixA *
        alternatingSixFiveAmbient_row20_matrixB =
      alternatingSixAmbientRow20LongMatrixAB :=
  alternatingSixAmbientRow20_longMatrixAB_mul

/-- Reduced matrix for the left-associated word `ab²`. -/
theorem alternatingSixAmbientRow20_longMatrixABB_eq :
    (alternatingSixFiveAmbient_row20_matrixA *
      alternatingSixFiveAmbient_row20_matrixB) *
      alternatingSixFiveAmbient_row20_matrixB =
      alternatingSixAmbientRow20LongMatrixABB := by
  rw [alternatingSixAmbientRow20_longMatrixAB_eq,
    alternatingSixAmbientRow20_longMatrixABB_mul]

/-- Reduced matrix for the left-associated word `ab³`. -/
theorem alternatingSixAmbientRow20_longMatrixABBB_eq :
    ((alternatingSixFiveAmbient_row20_matrixA *
        alternatingSixFiveAmbient_row20_matrixB) *
      alternatingSixFiveAmbient_row20_matrixB) *
      alternatingSixFiveAmbient_row20_matrixB =
      alternatingSixAmbientRow20LongMatrixABBB := by
  rw [alternatingSixAmbientRow20_longMatrixABB_eq,
    alternatingSixAmbientRow20_longMatrixABBB_mul]

end InductiveMcKay
end McKayConjecture
