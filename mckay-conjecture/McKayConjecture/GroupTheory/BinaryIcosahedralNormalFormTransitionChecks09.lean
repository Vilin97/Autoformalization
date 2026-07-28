/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormChecker
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitions09

/-!
# Checked binary-icosahedral transitions, rows 90–99
-/

namespace McKayConjecture
namespace GroupTheory

theorem binaryIcosahedralNormalFormTransitionRow090_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      90 binaryIcosahedralNormalFormTransitionRow090 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow091_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      91 binaryIcosahedralNormalFormTransitionRow091 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow092_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      92 binaryIcosahedralNormalFormTransitionRow092 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow093_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      93 binaryIcosahedralNormalFormTransitionRow093 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow094_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      94 binaryIcosahedralNormalFormTransitionRow094 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow095_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      95 binaryIcosahedralNormalFormTransitionRow095 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow096_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      96 binaryIcosahedralNormalFormTransitionRow096 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow097_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      97 binaryIcosahedralNormalFormTransitionRow097 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow098_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      98 binaryIcosahedralNormalFormTransitionRow098 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

theorem binaryIcosahedralNormalFormTransitionRow099_valid :
    binaryIcosahedralNormalFormTransitionRowValid
      binaryIcosahedralRewritePatterns
      99 binaryIcosahedralNormalFormTransitionRow099 := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  intro letter
  fin_cases letter <;> decide

end GroupTheory
end McKayConjecture
