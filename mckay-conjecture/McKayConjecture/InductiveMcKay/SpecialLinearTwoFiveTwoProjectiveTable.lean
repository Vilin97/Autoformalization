/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoSymmetricFourthProjectiveRow
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoTrivialProjectiveRow

/-!
# The complete projective `2'`-table of `SL(2, 𝔽₅)`

The four odd-degree rows consist of the trivial row, the two
symmetric-square rows, and the symmetric-fourth-power row.  The preceding
row calculations combine here into the complete local inductive McKay
datum at `p = 2`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeTwoForProjectiveTable :
    Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Every odd-degree row satisfies the exact-normalizer projective
compatibility clause. -/
theorem specialLinearTwoFiveTwo_allRows_tripleCompatible
    (r : SpecialLinearTwoFivePPrimeCharacterRow 2) :
    specialLinearTwoFiveTwoEquivariantMcKayEquiv
      |>.toExactNormalizerLocalCorrespondence.TripleCompatible
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv r) := by
  rcases r with ⟨r, hr⟩
  rcases r with _ | k | k | _ | _ | _ | _
  · have hrow :
        (⟨.trivial, hr⟩ :
          SpecialLinearTwoFivePPrimeCharacterRow 2) =
            specialLinearTwoFiveTwoTrivialPPrimeRow :=
      Subtype.ext (by rfl)
    rw [hrow]
    exact specialLinearTwoFiveTwoTrivialRow_tripleCompatible
  · exact False.elim <| hr <| by
      simp [specialLinearTwoFiveCharacterRowDegree]
  · have hrow :
        (⟨.symmetricSquare k, hr⟩ :
          SpecialLinearTwoFivePPrimeCharacterRow 2) =
            specialLinearTwoFiveTwoSymmetricSquarePPrimeRow k :=
      Subtype.ext (by rfl)
    rw [hrow]
    exact
      specialLinearTwoFiveTwoSymmetricSquareRow_tripleCompatible k
  · exact False.elim <| hr <| by
      simp [specialLinearTwoFiveCharacterRowDegree]
  · exact False.elim <| hr <| by
      simp [specialLinearTwoFiveCharacterRowDegree]
  · have hrow :
        (⟨.symmetricFourthPower, hr⟩ :
          SpecialLinearTwoFivePPrimeCharacterRow 2) =
            specialLinearTwoFiveTwoSymmetricFourthPPrimeRow :=
      Subtype.ext (by rfl)
    rw [hrow]
    exact
      specialLinearTwoFiveTwoSymmetricFourthRow_tripleCompatible
  · exact False.elim <| hr <| by
      simp [specialLinearTwoFiveCharacterRowDegree]

/-- The complete checked projective table at `p = 2`. -/
def specialLinearTwoFiveTwoProjectiveTableCompletion :
    SpecialLinearTwoFiveTwoProjectiveTableCompletion where
  characterTable := specialLinearTwoFiveTwoCharacterTableCompletion
  projectiveRow r :=
    ExactNormalizerProjectiveRowData.ofTripleCompatible
      specialLinearTwoFiveTwoEquivariantMcKayEquiv
      (specialLinearTwoFiveTwoPPrimeCharacterEquiv r)
      (specialLinearTwoFiveTwo_allRows_tripleCompatible r)

end InductiveMcKay
end McKayConjecture
