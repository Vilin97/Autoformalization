/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24LongWordProductAB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24LongWordProductABB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24LongWordProductABBB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24LongWordProductPrefix77
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24LongWordProductPrefix79

/-!
# Checked products for the two long row-24 class words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The original row-24 matrices multiply to the reduced `ab` matrix. -/
theorem alternatingSixAmbientRow24_longMatrixAB_eq :
    alternatingSixFiveAmbient_row24_matrixA *
        alternatingSixFiveAmbient_row24_matrixB =
      alternatingSixAmbientRow24LongMatrixAB :=
  alternatingSixAmbientRow24_longMatrixAB_mul

/-- Reduced matrix for the left-associated word `ab²`. -/
theorem alternatingSixAmbientRow24_longMatrixABB_eq :
    (alternatingSixFiveAmbient_row24_matrixA *
      alternatingSixFiveAmbient_row24_matrixB) *
      alternatingSixFiveAmbient_row24_matrixB =
      alternatingSixAmbientRow24LongMatrixABB := by
  rw [alternatingSixAmbientRow24_longMatrixAB_eq,
    alternatingSixAmbientRow24_longMatrixABB_mul]

/-- Reduced matrix for the left-associated word `ab³`. -/
theorem alternatingSixAmbientRow24_longMatrixABBB_eq :
    ((alternatingSixFiveAmbient_row24_matrixA *
        alternatingSixFiveAmbient_row24_matrixB) *
      alternatingSixFiveAmbient_row24_matrixB) *
      alternatingSixFiveAmbient_row24_matrixB =
      alternatingSixAmbientRow24LongMatrixABBB := by
  rw [alternatingSixAmbientRow24_longMatrixABB_eq,
    alternatingSixAmbientRow24_longMatrixABBB_mul]

end InductiveMcKay
end McKayConjecture
