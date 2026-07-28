/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRuleData
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRuleChecks00
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRuleChecks01
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRuleChecks02
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRuleChecks03
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRuleChecks04
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRuleChecks05
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRuleChecks06
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRuleChecks07
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRuleChecks08
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRuleChecks09
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRuleChecks10
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRuleChecks11
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRuleChecks12

/-!
# All checked binary-icosahedral rewrite rules
-/

namespace McKayConjecture
namespace GroupTheory

theorem binaryIcosahedralRewriteRules_valid :
    ∀ i : Fin 122,
      binaryIcosahedralRewriteRuleValid
        (binaryIcosahedralRewriteRules i) := by
  unfold binaryIcosahedralRewriteRuleValid
  native_decide

end GroupTheory
end McKayConjecture
