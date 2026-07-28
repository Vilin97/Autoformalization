/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveCharacterTable
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveFiveNormalizerTable
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveThreeNormalizerTable
import McKayConjecture.Proof.Cardinality

/-!
# Numerical McKay equalities for `SL(2, 𝔽₅)`

The complete nine-row ambient table and the exact quaternion-normalizer
tables immediately settle the cardinal McKay statement at the odd primes
three and five.  The stronger equivariant projective comparison needed by
the inductive condition is deliberately kept separate.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeThreeForMcKayCardinality :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

local instance factPrimeFiveForMcKayCardinality :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- There are six ambient irreducible characters of `3'`-degree. -/
theorem natCard_specialLinearTwoFiveThreePPrimeCharacter :
    Nat.card
        (PPrimeIrreducibleCharacter
          SpecialLinearTwoFive 3) =
      6 := by
  calc
    Nat.card
          (PPrimeIrreducibleCharacter
            SpecialLinearTwoFive 3) =
        Nat.card
          (SpecialLinearTwoFivePPrimeCharacterRow 3) :=
      Nat.card_congr
        (specialLinearTwoFivePPrimeCharacterEquiv 3).symm
    _ = 6 :=
      natCard_specialLinearTwoFiveThreePPrimeCharacterRow

/-- There are eight ambient irreducible characters of `5'`-degree. -/
theorem natCard_specialLinearTwoFiveFivePPrimeCharacter :
    Nat.card
        (PPrimeIrreducibleCharacter
          SpecialLinearTwoFive 5) =
      8 := by
  calc
    Nat.card
          (PPrimeIrreducibleCharacter
            SpecialLinearTwoFive 5) =
        Nat.card
          (SpecialLinearTwoFivePPrimeCharacterRow 5) :=
      Nat.card_congr
        (specialLinearTwoFivePPrimeCharacterEquiv 5).symm
    _ = 8 :=
      natCard_specialLinearTwoFiveFivePPrimeCharacterRow

/-- The ordinary McKay cardinal equality for `SL(2, 𝔽₅)` at `p = 3`. -/
theorem specialLinearTwoFive_statement_at_three :
    Statement SpecialLinearTwoFive 3
      specialLinearTwoFiveSylowThree := by
  rw [Statement.iff_natCard_eq]
  rw [natCard_specialLinearTwoFiveThreePPrimeCharacter,
    natCard_specialLinearTwoFiveThreeNormalizerPPrimeCharacter]

/-- The ordinary McKay cardinal equality for `SL(2, 𝔽₅)` at `p = 5`. -/
theorem specialLinearTwoFive_statement_at_five :
    Statement SpecialLinearTwoFive 5
      specialLinearTwoFiveSylowFive := by
  rw [Statement.iff_natCard_eq]
  rw [natCard_specialLinearTwoFiveFivePPrimeCharacter,
    natCard_specialLinearTwoFiveFiveNormalizerPPrimeCharacter]

end InductiveMcKay
end McKayConjecture
