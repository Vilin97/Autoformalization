/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P11LongWordProductAB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P11LongWordProductABB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P11LongWordProductABBB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P11LongWordProductPrefix77
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P11LongWordProductPrefix79

/-!
# Checked products for the two long ATLAS degree-12 power-eleven class words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The original ATLAS degree-12 power-eleven matrices multiply to the reduced `ab` matrix. -/
theorem alternatingSixAmbientAtlas12P11_longMatrixAB_eq :
    alternatingSixFiveAmbient_atlas12Power11_matrixA *
        alternatingSixFiveAmbient_atlas12Power11_matrixB =
      alternatingSixAmbientAtlas12P11LongMatrixAB :=
  alternatingSixAmbientAtlas12P11_longMatrixAB_mul

/-- Reduced matrix for the left-associated word `ab²`. -/
theorem alternatingSixAmbientAtlas12P11_longMatrixABB_eq :
    (alternatingSixFiveAmbient_atlas12Power11_matrixA *
      alternatingSixFiveAmbient_atlas12Power11_matrixB) *
      alternatingSixFiveAmbient_atlas12Power11_matrixB =
      alternatingSixAmbientAtlas12P11LongMatrixABB := by
  rw [alternatingSixAmbientAtlas12P11_longMatrixAB_eq,
    alternatingSixAmbientAtlas12P11_longMatrixABB_mul]

/-- Reduced matrix for the left-associated word `ab³`. -/
theorem alternatingSixAmbientAtlas12P11_longMatrixABBB_eq :
    ((alternatingSixFiveAmbient_atlas12Power11_matrixA *
        alternatingSixFiveAmbient_atlas12Power11_matrixB) *
      alternatingSixFiveAmbient_atlas12Power11_matrixB) *
      alternatingSixFiveAmbient_atlas12Power11_matrixB =
      alternatingSixAmbientAtlas12P11LongMatrixABBB := by
  rw [alternatingSixAmbientAtlas12P11_longMatrixABB_eq,
    alternatingSixAmbientAtlas12P11_longMatrixABBB_mul]

end InductiveMcKay
end McKayConjecture
