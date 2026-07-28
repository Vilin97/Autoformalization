/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoLongWordProductAB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoLongWordProductABB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoLongWordProductABBB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoLongWordProductP77
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoLongWordProductP79
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoLongWordProductState77
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoLongWordProductState79

/-!
# Checked products for the ATLAS power-2 long words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The original matrices multiply to the reduced `ab` matrix. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_eq :
    alternatingSixFiveAmbient_atlas12Power2_matrixA *
        alternatingSixFiveAmbient_atlas12Power2_matrixB =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB :=
  alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_mul

/-- Reduced matrix for the left-associated word `ab²`. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixABB_eq :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA *
      alternatingSixFiveAmbient_atlas12Power2_matrixB) *
      alternatingSixFiveAmbient_atlas12Power2_matrixB =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABB := by
  rw [alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_eq,
    alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixABB_mul]

/-- Reduced matrix for the left-associated word `ab³`. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixABBB_eq :
    ((alternatingSixFiveAmbient_atlas12Power2_matrixA *
        alternatingSixFiveAmbient_atlas12Power2_matrixB) *
      alternatingSixFiveAmbient_atlas12Power2_matrixB) *
      alternatingSixFiveAmbient_atlas12Power2_matrixB =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB := by
  rw [alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixABB_eq,
    alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixABBB_mul]

end InductiveMcKay
end McKayConjecture
