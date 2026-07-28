/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormChecker
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions08

/-!
# Checked binary-icosahedral transitions, rows 80–89
-/

namespace McKayConjecture
namespace GroupTheory

theorem binaryIcosahedralNormalFormTransitionRow080_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      80 binaryIcosahedralNormalFormTransitionRow080 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow081_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      81 binaryIcosahedralNormalFormTransitionRow081 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow082_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      82 binaryIcosahedralNormalFormTransitionRow082 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow083_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      83 binaryIcosahedralNormalFormTransitionRow083 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow084_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      84 binaryIcosahedralNormalFormTransitionRow084 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow085_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      85 binaryIcosahedralNormalFormTransitionRow085 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow086_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      86 binaryIcosahedralNormalFormTransitionRow086 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow087_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      87 binaryIcosahedralNormalFormTransitionRow087 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow088_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      88 binaryIcosahedralNormalFormTransitionRow088 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow089_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      89 binaryIcosahedralNormalFormTransitionRow089 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

end GroupTheory
end McKayConjecture
