/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormChecker
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions05

/-!
# Checked binary-icosahedral transitions, rows 50–59
-/

namespace McKayConjecture
namespace GroupTheory

theorem binaryIcosahedralNormalFormTransitionRow050_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      50 binaryIcosahedralNormalFormTransitionRow050 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow051_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      51 binaryIcosahedralNormalFormTransitionRow051 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow052_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      52 binaryIcosahedralNormalFormTransitionRow052 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow053_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      53 binaryIcosahedralNormalFormTransitionRow053 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow054_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      54 binaryIcosahedralNormalFormTransitionRow054 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow055_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      55 binaryIcosahedralNormalFormTransitionRow055 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow056_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      56 binaryIcosahedralNormalFormTransitionRow056 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow057_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      57 binaryIcosahedralNormalFormTransitionRow057 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow058_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      58 binaryIcosahedralNormalFormTransitionRow058 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow059_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      59 binaryIcosahedralNormalFormTransitionRow059 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

end GroupTheory
end McKayConjecture
