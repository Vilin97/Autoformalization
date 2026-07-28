/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow31LongWordProductAB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow31LongWordProductABB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow31LongWordProductABBB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow31LongWordProductPrefix77
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow31LongWordProductPrefix79

/-!
# Checked products for the two long row-31 class words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The original row-31 matrices multiply to the reduced `ab` matrix. -/
theorem alternatingSixAmbientRow31_longMatrixAB_eq :
    alternatingSixFiveAmbient_row31_matrixA *
        alternatingSixFiveAmbient_row31_matrixB =
      alternatingSixAmbientRow31LongMatrixAB :=
  alternatingSixAmbientRow31_longMatrixAB_mul

/-- Reduced matrix for the left-associated word `ab²`. -/
theorem alternatingSixAmbientRow31_longMatrixABB_eq :
    (alternatingSixFiveAmbient_row31_matrixA *
      alternatingSixFiveAmbient_row31_matrixB) *
      alternatingSixFiveAmbient_row31_matrixB =
      alternatingSixAmbientRow31LongMatrixABB := by
  rw [alternatingSixAmbientRow31_longMatrixAB_eq,
    alternatingSixAmbientRow31_longMatrixABB_mul]

/-- Reduced matrix for the left-associated word `ab³`. -/
theorem alternatingSixAmbientRow31_longMatrixABBB_eq :
    ((alternatingSixFiveAmbient_row31_matrixA *
        alternatingSixFiveAmbient_row31_matrixB) *
      alternatingSixFiveAmbient_row31_matrixB) *
      alternatingSixFiveAmbient_row31_matrixB =
      alternatingSixAmbientRow31LongMatrixABBB := by
  rw [alternatingSixAmbientRow31_longMatrixABB_eq,
    alternatingSixAmbientRow31_longMatrixABBB_mul]

end InductiveMcKay
end McKayConjecture
