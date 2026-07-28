/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenLongWordProductAB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenLongWordProductABB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenLongWordProductABBB
import
  McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenLongWordProductPrefix77
import
  McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenLongWordProductPrefix79

/-!
# Checked products for the two long ATLAS degree-12 power-seven class words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The original ATLAS degree-12 power-seven matrices multiply to the reduced `ab` matrix. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixAB_eq :
    alternatingSixFiveAmbient_atlas12Power7_matrixA *
        alternatingSixFiveAmbient_atlas12Power7_matrixB =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB :=
  alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixAB_mul

/-- Reduced matrix for the left-associated word `ab²`. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABB_eq :
    (alternatingSixFiveAmbient_atlas12Power7_matrixA *
      alternatingSixFiveAmbient_atlas12Power7_matrixB) *
      alternatingSixFiveAmbient_atlas12Power7_matrixB =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB := by
  rw [alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixAB_eq,
    alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABB_mul]

/-- Reduced matrix for the left-associated word `ab³`. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_eq :
    ((alternatingSixFiveAmbient_atlas12Power7_matrixA *
        alternatingSixFiveAmbient_atlas12Power7_matrixB) *
      alternatingSixFiveAmbient_atlas12Power7_matrixB) *
      alternatingSixFiveAmbient_atlas12Power7_matrixB =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB := by
  rw [alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABB_eq,
    alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_mul]

end InductiveMcKay
end McKayConjecture
