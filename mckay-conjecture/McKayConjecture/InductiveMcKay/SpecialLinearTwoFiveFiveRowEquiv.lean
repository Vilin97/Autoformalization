/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveFiveNormalizerTable
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveThreeOuterActions

/-!
# Row matching for the `5'`-tables of `SL(2, 𝔽₅)`

The eight ambient rows of degree prime to five are matched with the four
linear and four two-dimensional rows of the dicyclic Sylow-five normalizer.
The matching preserves the action of the central involution and pairs the
two outer-swapped ambient pairs with the two outer-swapped pairs of
two-dimensional normalizer rows.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open QuaternionGroupFive

/-- Exchange the two indices in each opposite pair of `Fin 4`. -/
def specialLinearTwoFiveFiveOppositeIndex (k : Fin 4) : Fin 4 :=
  ⟨(k.val + 2) % 4, Nat.mod_lt _ (by omega)⟩

@[simp]
theorem specialLinearTwoFiveFiveOppositeIndex_zero :
    specialLinearTwoFiveFiveOppositeIndex 0 = 2 := by
  rfl

@[simp]
theorem specialLinearTwoFiveFiveOppositeIndex_one :
    specialLinearTwoFiveFiveOppositeIndex 1 = 3 := by
  rfl

@[simp]
theorem specialLinearTwoFiveFiveOppositeIndex_two :
    specialLinearTwoFiveFiveOppositeIndex 2 = 0 := by
  rfl

@[simp]
theorem specialLinearTwoFiveFiveOppositeIndex_three :
    specialLinearTwoFiveFiveOppositeIndex 3 = 1 := by
  rfl

/-- The normalizer row attached to an ambient ordinary-character row.
The `symmetricFourthPower` branch has degree divisible by five and is
irrelevant after restriction to the `5'` subtype. -/
def specialLinearTwoFiveFiveNormalizerRowOfAmbient :
    SpecialLinearTwoFiveCharacterRow → CharacterRow
  | .trivial => .linear 0
  | .faithful k =>
      .twoDimensional (Fin.cases 0 (fun _ : Fin 1 ↦ 2) k)
  | .symmetricSquare k =>
      .twoDimensional (Fin.cases 1 (fun _ : Fin 1 ↦ 3) k)
  | .symmetricCube => .linear 1
  | .tensor => .linear 2
  | .symmetricFourthPower => .linear 0
  | .symmetricFifthPower => .linear 3

/-- The ambient row attached to a normalizer row. -/
def specialLinearTwoFiveFiveAmbientRowOfNormalizer :
    CharacterRow → SpecialLinearTwoFiveCharacterRow
  | .linear j =>
      if j = 0 then .trivial
      else if j = 1 then .symmetricCube
      else if j = 2 then .tensor
      else .symmetricFifthPower
  | .twoDimensional k =>
      if k = 0 then .faithful 0
      else if k = 1 then .symmetricSquare 0
      else if k = 2 then .faithful 1
      else .symmetricSquare 1

theorem specialLinearTwoFiveFiveAmbientRowOfNormalizer_isPPrime
    (r : CharacterRow) :
    ¬5 ∣ specialLinearTwoFiveCharacterRowDegree
      (specialLinearTwoFiveFiveAmbientRowOfNormalizer r) := by
  rcases r with j | k
  · fin_cases j <;>
      decide
  · fin_cases k <;>
      decide

/-- The explicit eight-row matching between the ambient and exact-normalizer
`5'`-tables. -/
def specialLinearTwoFiveFiveCharacterRowEquiv :
    SpecialLinearTwoFivePPrimeCharacterRow 5 ≃ CharacterRow where
  toFun r :=
    specialLinearTwoFiveFiveNormalizerRowOfAmbient r.1
  invFun r :=
    ⟨specialLinearTwoFiveFiveAmbientRowOfNormalizer r,
      specialLinearTwoFiveFiveAmbientRowOfNormalizer_isPPrime r⟩
  left_inv r := by
    apply Subtype.ext
    rcases r with ⟨r, hr⟩
    rcases r with _ | k | k | _ | _ | _ | _
    · rfl
    · fin_cases k <;> rfl
    · fin_cases k <;> rfl
    · rfl
    · rfl
    · exfalso
      apply hr
      simp [specialLinearTwoFiveCharacterRowDegree]
    · rfl
  right_inv r := by
    rcases r with j | k
    · fin_cases j <;> rfl
    · fin_cases k <;> rfl

/-- The normalizer row permutation induced by the diagonal outer
automorphism: the four linear rows are fixed and opposite two-dimensional
rows are exchanged. -/
def specialLinearTwoFiveFiveNormalizerOuterCharacterRow :
    CharacterRow → CharacterRow
  | .linear j => .linear j
  | .twoDimensional k =>
      .twoDimensional (specialLinearTwoFiveFiveOppositeIndex k)

/-- The standard eight-row matching intertwines the explicit outer row
permutations. -/
theorem specialLinearTwoFiveFiveCharacterRowEquiv_outer
    (r : SpecialLinearTwoFivePPrimeCharacterRow 5) :
    specialLinearTwoFiveFiveCharacterRowEquiv
        ⟨specialLinearTwoFiveOuterCharacterRow r.1, by
          rw [specialLinearTwoFiveOuterCharacterRow_degree]
          exact r.2⟩ =
      specialLinearTwoFiveFiveNormalizerOuterCharacterRow
        (specialLinearTwoFiveFiveCharacterRowEquiv r) := by
  rcases r with ⟨r, hr⟩
  rcases r with _ | k | k | _ | _ | _ | _
  · rfl
  · fin_cases k <;> rfl
  · fin_cases k <;> rfl
  · rfl
  · rfl
  · exact False.elim <| hr <| by
      simp [specialLinearTwoFiveCharacterRowDegree]
  · rfl

end InductiveMcKay
end McKayConjecture
