/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow23LongWordProductAB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow23LongWordProductABB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow23LongWordProductABBB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow23LongWordProductPrefix77
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow23LongWordProductPrefix79

/-!
# Checked products for the two long row-23 class words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The original row-23 matrices multiply to the reduced `ab` matrix. -/
theorem alternatingSixAmbientRow23_longMatrixAB_eq :
    alternatingSixFiveAmbient_row23_matrixA *
        alternatingSixFiveAmbient_row23_matrixB =
      alternatingSixAmbientRow23LongMatrixAB :=
  alternatingSixAmbientRow23_longMatrixAB_mul

/-- Reduced matrix for the left-associated word `ab²`. -/
theorem alternatingSixAmbientRow23_longMatrixABB_eq :
    (alternatingSixFiveAmbient_row23_matrixA *
      alternatingSixFiveAmbient_row23_matrixB) *
      alternatingSixFiveAmbient_row23_matrixB =
      alternatingSixAmbientRow23LongMatrixABB := by
  rw [alternatingSixAmbientRow23_longMatrixAB_eq,
    alternatingSixAmbientRow23_longMatrixABB_mul]

/-- Reduced matrix for the left-associated word `ab³`. -/
theorem alternatingSixAmbientRow23_longMatrixABBB_eq :
    ((alternatingSixFiveAmbient_row23_matrixA *
        alternatingSixFiveAmbient_row23_matrixB) *
      alternatingSixFiveAmbient_row23_matrixB) *
      alternatingSixFiveAmbient_row23_matrixB =
      alternatingSixAmbientRow23LongMatrixABBB := by
  rw [alternatingSixAmbientRow23_longMatrixABB_eq,
    alternatingSixAmbientRow23_longMatrixABBB_mul]

end InductiveMcKay
end McKayConjecture
