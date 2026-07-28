/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoNormalizerTable
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoOuterActions

/-!
# Outer equivariance of the standard four-row `p = 2` matching

This file contains the finite row calculation: the standard McKay matching
intertwines the diagonal outer permutations of the ambient and normalizer
odd-degree tables.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeTwoForRowEquivariance :
    Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The standard four-row matching intertwines the two explicit outer row
permutations. -/
theorem specialLinearTwoFiveTwoMcKayRowEquiv_outer
    (r : SpecialLinearTwoFivePPrimeCharacterRow 2) :
    specialLinearTwoFiveTwoMcKayRowEquiv
        (specialLinearTwoFiveTwoOuterPPrimeRow r) =
      specialLinearTwoFiveTwoNormalizerOuterPPrimeRow
        (specialLinearTwoFiveTwoMcKayRowEquiv r) := by
  rcases r with ⟨r, hr⟩
  rcases r with _ | k | k | _ | _ | _ | _
  · rfl
  · exact False.elim <| hr <| by
      simp [specialLinearTwoFiveCharacterRowDegree]
  · fin_cases k <;>
      apply Subtype.ext <;>
      rfl
  · exact False.elim <| hr <| by
      simp [specialLinearTwoFiveCharacterRowDegree]
  · exact False.elim <| hr <| by
      simp [specialLinearTwoFiveCharacterRowDegree]
  · rfl
  · exact False.elim <| hr <| by
      simp [specialLinearTwoFiveCharacterRowDegree]

end InductiveMcKay
end McKayConjecture
