/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InnerAutomorphism
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveThreeOuterActions
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoNormalizerOuterActions

/-!
# The outer action on the ambient `2'`-character table of `SL(2, 𝔽₅)`

The Sylow-three-adapted and diagonal outer representatives differ by an
inner automorphism.  Hence the diagonal representative induces the same
row permutation on the ambient table, and that permutation preserves the
odd-degree rows.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeTwoForOuterActions :
    Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The diagonal outer representative has the same character action as the
Sylow-three-adapted representative: their quotient is inner. -/
theorem
    specialLinearTwoFiveDiagonalOuterAutomorphism_smul_irreducibleCharacter
    (r : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveDiagonalOuterAutomorphism •
        specialLinearTwoFiveIrreducibleCharacter r =
      specialLinearTwoFiveIrreducibleCharacter
        (specialLinearTwoFiveOuterCharacterRow r) := by
  simpa only [
    specialLinearTwoFiveSylowThreeOuterAutomorphism,
    mul_smul, IrreducibleCharacter.conj_smul] using
    specialLinearTwoFiveOuterAutomorphism_smul_irreducibleCharacter r

/-- The diagonal outer permutation preserves the odd-degree ambient rows. -/
def specialLinearTwoFiveTwoOuterPPrimeRow
    (r : SpecialLinearTwoFivePPrimeCharacterRow 2) :
    SpecialLinearTwoFivePPrimeCharacterRow 2 :=
  ⟨specialLinearTwoFiveOuterCharacterRow r.1, by
    rw [specialLinearTwoFiveOuterCharacterRow_degree]
    exact r.2⟩

@[simp]
theorem specialLinearTwoFiveDiagonalOuterAutomorphism_smul_pPrimeCharacter
    (r : SpecialLinearTwoFivePPrimeCharacterRow 2) :
    specialLinearTwoFiveDiagonalOuterAutomorphism •
        specialLinearTwoFivePPrimeCharacterEquiv 2 r =
      specialLinearTwoFivePPrimeCharacterEquiv 2
        (specialLinearTwoFiveTwoOuterPPrimeRow r) := by
  apply Subtype.ext
  exact
    specialLinearTwoFiveDiagonalOuterAutomorphism_smul_irreducibleCharacter
      r.1

end InductiveMcKay
end McKayConjecture
