/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormChecker
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRules12

/-!
# Checked binary-icosahedral rewrite rules 120–121
-/

namespace McKayConjecture
namespace GroupTheory

theorem binaryIcosahedralRewriteRule120_valid :
    binaryIcosahedralRewriteRuleValid
      binaryIcosahedralRewriteRule120 := by
  unfold binaryIcosahedralRewriteRuleValid
  native_decide

theorem binaryIcosahedralRewriteRule121_valid :
    binaryIcosahedralRewriteRuleValid
      binaryIcosahedralRewriteRule121 := by
  unfold binaryIcosahedralRewriteRuleValid
  native_decide

end GroupTheory
end McKayConjecture
