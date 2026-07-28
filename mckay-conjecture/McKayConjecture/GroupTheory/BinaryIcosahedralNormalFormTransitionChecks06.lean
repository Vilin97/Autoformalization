/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormChecker
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions06

/-!
# Checked binary-icosahedral transitions, rows 60–69
-/

namespace McKayConjecture
namespace GroupTheory

theorem binaryIcosahedralNormalFormTransitionRow060_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      60 binaryIcosahedralNormalFormTransitionRow060 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow061_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      61 binaryIcosahedralNormalFormTransitionRow061 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow062_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      62 binaryIcosahedralNormalFormTransitionRow062 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow063_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      63 binaryIcosahedralNormalFormTransitionRow063 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow064_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      64 binaryIcosahedralNormalFormTransitionRow064 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow065_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      65 binaryIcosahedralNormalFormTransitionRow065 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow066_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      66 binaryIcosahedralNormalFormTransitionRow066 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow067_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      67 binaryIcosahedralNormalFormTransitionRow067 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow068_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      68 binaryIcosahedralNormalFormTransitionRow068 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow069_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      69 binaryIcosahedralNormalFormTransitionRow069 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

end GroupTheory
end McKayConjecture
