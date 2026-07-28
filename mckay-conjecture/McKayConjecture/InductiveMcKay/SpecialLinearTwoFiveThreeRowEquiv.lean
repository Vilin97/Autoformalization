/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveCharacterValues
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveThreeNormalizerRepresentations

/-!
# Row matching for the `3'`-tables of `SL(2, 𝔽₅)`

The six ambient rows are matched with the four linear and two
two-dimensional rows of the generalized quaternion normalizer.  The
matching preserves the action of the central involution: the two faithful
ambient rows correspond to the two odd linear rows.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- The normalizer row attached to an ambient ordinary-character row.
The two branches which have degree divisible by three are irrelevant after
restriction to `SpecialLinearTwoFivePPrimeCharacterRow 3`. -/
def specialLinearTwoFiveThreeNormalizerRowOfAmbient :
    SpecialLinearTwoFiveCharacterRow →
      QuaternionGroupThreeCharacterRow
  | .trivial => .linear 0
  | .faithful k =>
      if k = 0 then .linear 1 else .linear 3
  | .symmetricSquare _ => .linear 0
  | .symmetricCube => .twoDimensional 0
  | .tensor => .linear 2
  | .symmetricFourthPower => .twoDimensional 1
  | .symmetricFifthPower => .linear 0

/-- The ambient row attached to a normalizer row. -/
def specialLinearTwoFiveThreeAmbientRowOfNormalizer :
    QuaternionGroupThreeCharacterRow →
      SpecialLinearTwoFiveCharacterRow
  | .linear j =>
      if j = 0 then .trivial
      else if j = 1 then .faithful 0
      else if j = 2 then .tensor
      else .faithful 1
  | .twoDimensional k =>
      Fin.cases .symmetricCube
        (fun _ : Fin 1 => .symmetricFourthPower) k

theorem specialLinearTwoFiveThreeAmbientRowOfNormalizer_isPPrime :
    ∀ r : QuaternionGroupThreeCharacterRow,
      ¬3 ∣ specialLinearTwoFiveCharacterRowDegree
        (specialLinearTwoFiveThreeAmbientRowOfNormalizer r) := by
  intro r
  rcases r with j | k
  · fin_cases j <;> native_decide
  · fin_cases k <;> native_decide

/-- The explicit six-row matching between the ambient and exact-normalizer
`3'`-tables. -/
def specialLinearTwoFiveThreeCharacterRowEquiv :
    SpecialLinearTwoFivePPrimeCharacterRow 3 ≃
      QuaternionGroupThreeCharacterRow where
  toFun r :=
    specialLinearTwoFiveThreeNormalizerRowOfAmbient r.1
  invFun r :=
    ⟨specialLinearTwoFiveThreeAmbientRowOfNormalizer r,
      specialLinearTwoFiveThreeAmbientRowOfNormalizer_isPPrime r⟩
  left_inv r := by
    apply Subtype.ext
    rcases r with ⟨r, hr⟩
    rcases r with _ | k | k | _ | _ | _ | _
    · rfl
    · fin_cases k <;> rfl
    · exfalso
      apply hr
      simp [specialLinearTwoFiveCharacterRowDegree]
    · rfl
    · rfl
    · rfl
    · exfalso
      apply hr
      simp [specialLinearTwoFiveCharacterRowDegree]
  right_inv r := by
    rcases r with j | k
    · fin_cases j <;> rfl
    · fin_cases k <;> rfl

@[simp]
theorem specialLinearTwoFiveThreeCharacterRowEquiv_trivial :
    specialLinearTwoFiveThreeCharacterRowEquiv
      ⟨.trivial, by native_decide⟩ =
        .linear 0 :=
  rfl

@[simp]
theorem specialLinearTwoFiveThreeCharacterRowEquiv_faithful_zero :
    specialLinearTwoFiveThreeCharacterRowEquiv
      ⟨.faithful 0, by native_decide⟩ =
        .linear 1 :=
  rfl

@[simp]
theorem specialLinearTwoFiveThreeCharacterRowEquiv_faithful_one :
    specialLinearTwoFiveThreeCharacterRowEquiv
      ⟨.faithful 1, by native_decide⟩ =
        .linear 3 :=
  rfl

@[simp]
theorem specialLinearTwoFiveThreeCharacterRowEquiv_symmetricCube :
    specialLinearTwoFiveThreeCharacterRowEquiv
      ⟨.symmetricCube, by native_decide⟩ =
        .twoDimensional 0 :=
  rfl

@[simp]
theorem specialLinearTwoFiveThreeCharacterRowEquiv_tensor :
    specialLinearTwoFiveThreeCharacterRowEquiv
      ⟨.tensor, by native_decide⟩ =
        .linear 2 :=
  rfl

@[simp]
theorem specialLinearTwoFiveThreeCharacterRowEquiv_symmetricFourthPower :
    specialLinearTwoFiveThreeCharacterRowEquiv
      ⟨.symmetricFourthPower, by native_decide⟩ =
        .twoDimensional 1 :=
  rfl

end InductiveMcKay
end McKayConjecture
