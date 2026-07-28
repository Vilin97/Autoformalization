/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormChecker
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions04

/-!
# Checked binary-icosahedral transitions, rows 40–49
-/

namespace McKayConjecture
namespace GroupTheory

theorem binaryIcosahedralNormalFormTransitionRow040_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      40 binaryIcosahedralNormalFormTransitionRow040 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow041_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      41 binaryIcosahedralNormalFormTransitionRow041 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow042_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      42 binaryIcosahedralNormalFormTransitionRow042 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow043_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      43 binaryIcosahedralNormalFormTransitionRow043 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow044_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      44 binaryIcosahedralNormalFormTransitionRow044 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow045_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      45 binaryIcosahedralNormalFormTransitionRow045 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow046_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      46 binaryIcosahedralNormalFormTransitionRow046 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow047_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      47 binaryIcosahedralNormalFormTransitionRow047 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow048_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      48 binaryIcosahedralNormalFormTransitionRow048 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow049_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      49 binaryIcosahedralNormalFormTransitionRow049 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

end GroupTheory
end McKayConjecture
