/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P1LongWordProductAB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P1LongWordProductABB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P1LongWordProductABBB
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P1LongWordProductPrefix77
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P1LongWordProductPrefix79

/-!
# Checked products for the two long ATLAS degree-12 power-one class words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The original ATLAS degree-12 power-one matrices multiply to the reduced `ab` matrix. -/
theorem alternatingSixAmbientAtlas12P1_longMatrixAB_eq :
    alternatingSixFiveAmbient_atlas12Power1_matrixA *
        alternatingSixFiveAmbient_atlas12Power1_matrixB =
      alternatingSixAmbientAtlas12P1LongMatrixAB :=
  alternatingSixAmbientAtlas12P1_longMatrixAB_mul

/-- Reduced matrix for the left-associated word `ab²`. -/
theorem alternatingSixAmbientAtlas12P1_longMatrixABB_eq :
    (alternatingSixFiveAmbient_atlas12Power1_matrixA *
      alternatingSixFiveAmbient_atlas12Power1_matrixB) *
      alternatingSixFiveAmbient_atlas12Power1_matrixB =
      alternatingSixAmbientAtlas12P1LongMatrixABB := by
  rw [alternatingSixAmbientAtlas12P1_longMatrixAB_eq,
    alternatingSixAmbientAtlas12P1_longMatrixABB_mul]

/-- Reduced matrix for the left-associated word `ab³`. -/
theorem alternatingSixAmbientAtlas12P1_longMatrixABBB_eq :
    ((alternatingSixFiveAmbient_atlas12Power1_matrixA *
        alternatingSixFiveAmbient_atlas12Power1_matrixB) *
      alternatingSixFiveAmbient_atlas12Power1_matrixB) *
      alternatingSixFiveAmbient_atlas12Power1_matrixB =
      alternatingSixAmbientAtlas12P1LongMatrixABBB := by
  rw [alternatingSixAmbientAtlas12P1_longMatrixABB_eq,
    alternatingSixAmbientAtlas12P1_longMatrixABBB_mul]

end InductiveMcKay
end McKayConjecture
