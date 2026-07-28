/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormData
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitionChecks00
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitionChecks01
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitionChecks02
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitionChecks03
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitionChecks04
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitionChecks05
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitionChecks06
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitionChecks07
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitionChecks08
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitionChecks09
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitionChecks10
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitionChecks11

/-!
# All checked binary-icosahedral normal-form transitions
-/

namespace McKayConjecture
namespace GroupTheory

theorem binaryIcosahedralNormalFormTransitions_valid :
    ∀ i : Fin 120,
      binaryIcosahedralNormalFormTransitionRowValid
        binaryIcosahedralRewritePatterns
        i (binaryIcosahedralNormalFormTransitions i) := by
  unfold binaryIcosahedralNormalFormTransitionRowValid
  native_decide

end GroupTheory
end McKayConjecture
