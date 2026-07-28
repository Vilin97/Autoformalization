/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.IrreducibleCharacterBasis
import McKayConjecture.GroupTheory.AlternatingSixThreeNormalizerConjugacyClasses

/-!
# Ordinary character count for the three-normalizer of `6.A₆`

The class-function basis theorem identifies ordinary irreducible
characters with a basis indexed in cardinality by conjugacy classes.
The explicit commuting-pair calculation for `3^(1+2) ⋊ C₈` therefore
gives `28` ordinary irreducible characters, both in coordinates and in
the actual fixed normalizer.
-/

namespace McKayConjecture
namespace AlternatingSixThreeNormalizer

open GroupTheory

/-- The computable coordinate normalizer has twenty-eight ordinary
irreducible complex characters. -/
theorem natCard_irreducibleCharacter_coordinates :
    Nat.card
        (IrreducibleCharacter
          AlternatingSixThreeNormalizerCoordinates) =
      28 := by
  calc
    Nat.card
        (IrreducibleCharacter
          AlternatingSixThreeNormalizerCoordinates) =
        Nat.card
          (ConjClasses AlternatingSixThreeNormalizerCoordinates) :=
      ClassFunction.natCard_irreducibleCharacter_eq_conjClasses
    _ = 28 :=
      natCard_conjClasses_alternatingSixThreeNormalizerCoordinates

/-- The actual fixed Sylow-three normalizer in the canonical universal
cover has twenty-eight ordinary irreducible complex characters. -/
theorem natCard_irreducibleCharacter_actualNormalizer :
    Nat.card
        (IrreducibleCharacter
          AlternatingSixUniversalCoverThreeNormalizer) =
      28 := by
  calc
    Nat.card
        (IrreducibleCharacter
          AlternatingSixUniversalCoverThreeNormalizer) =
        Nat.card
          (ConjClasses
            AlternatingSixUniversalCoverThreeNormalizer) :=
      ClassFunction.natCard_irreducibleCharacter_eq_conjClasses
    _ = 28 :=
      natCard_conjClasses_alternatingSixUniversalCoverThreeNormalizer

end AlternatingSixThreeNormalizer
end McKayConjecture
