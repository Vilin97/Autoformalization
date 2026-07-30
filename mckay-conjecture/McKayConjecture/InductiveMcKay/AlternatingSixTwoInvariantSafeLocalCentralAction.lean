/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixTwoCTblLibInvariantSafeRowIdentification
import McKayConjecture.InductiveMcKay.AlternatingSixTwoCTblLibLocalBridgeObstruction

/-!
# The central coordinate in the invariant-safe two-local action

Both corrected outer automorphisms invert the central `C₃` factor of the
actual Sylow-two normalizer.  Character evaluation on a generator therefore
determines the first coordinate of every semantic row image: it is negation
in `Fin 3`.

For the invariant-safe position orientation, both audited local permutations
have the same effect on that coordinate.  Consequently each full local
bridge is equivalent to equality of only the remaining quaternion sign pair.
This removes the arbitrary cyclic orientation from the finite seam without
claiming that the chosen positions are the true CTblLib order.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoInvariantSafeLocalCentralActionFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- Negating a cyclic-three character parameter inverts its third root. -/
theorem CyclicThree.thirdRootParameter_neg
    (j : Fin 3) :
    CyclicThree.thirdRootParameter (-j) =
      (CyclicThree.thirdRootParameter j)⁻¹ := by
  fin_cases j
  · rfl
  · change
      CyclicThree.primitiveThirdRootUnit ^ 2 =
        (CyclicThree.primitiveThirdRootUnit ^ 1)⁻¹
    symm
    rw [pow_one]
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ]
    exact CyclicThree.primitiveThirdRootUnit_pow_three
  · change
      CyclicThree.primitiveThirdRootUnit ^ 1 =
        (CyclicThree.primitiveThirdRootUnit ^ 2)⁻¹
    symm
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_add]
    exact CyclicThree.primitiveThirdRootUnit_pow_three

/-- The genuine first corrected local action negates the cyclic-three
coordinate of every enumerated row. -/
theorem
    alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation_fst
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    (alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation r).1 =
      -r.1 := by
  apply CyclicThree.thirdRootParameter_injective
  apply Units.ext
  have hcharacter :=
    alternatingSixTwoActualNormalizerRowPermutation_character
      (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
        (alternatingSixUniversalCoverSylow 2)) r
  have hcharacter' :
      alternatingSixTwoActualNormalizerPPrimeCharacterEquiv
          (alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation r) =
        (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
            (alternatingSixUniversalCoverSylow 2)) •
          alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r := by
    simpa [alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation]
      using hcharacter
  have hvalue :=
    congrArg
      (fun χ :
          PPrimeIrreducibleCharacter
            (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) 2 =>
        χ.1.values
          alternatingSixTwoActualNormalizerCentralThreeGenerator)
      hcharacter'
  rw [
    alternatingSixTwoActualNormalizerCharacter_values_centralThreeGenerator,
    alternatingSixTwoCorrectedAlphaOne_smul_character_values_centralThreeGenerator
  ] at hvalue
  calc
    (CyclicThree.thirdRootParameter
        (alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation r).1 :
      ℂ) =
        (CyclicThree.thirdRootParameter r.1 : ℂ)⁻¹ :=
      hvalue
    _ = (CyclicThree.thirdRootParameter (-r.1) : ℂ) := by
      simpa using congrArg Units.val
        (CyclicThree.thirdRootParameter_neg r.1).symm

/-- The genuine second corrected local action negates the cyclic-three
coordinate of every enumerated row. -/
theorem
    alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation_fst
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    (alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation r).1 =
      -r.1 := by
  apply CyclicThree.thirdRootParameter_injective
  apply Units.ext
  have hcharacter :=
    alternatingSixTwoActualNormalizerRowPermutation_character
      (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
        (alternatingSixUniversalCoverSylow 2)) r
  have hcharacter' :
      alternatingSixTwoActualNormalizerPPrimeCharacterEquiv
          (alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation r) =
        (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
            (alternatingSixUniversalCoverSylow 2)) •
          alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r := by
    simpa [alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation]
      using hcharacter
  have hvalue :=
    congrArg
      (fun χ :
          PPrimeIrreducibleCharacter
            (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) 2 =>
        χ.1.values
          alternatingSixTwoActualNormalizerCentralThreeGenerator)
      hcharacter'
  rw [
    alternatingSixTwoActualNormalizerCharacter_values_centralThreeGenerator,
    alternatingSixTwoCorrectedAlphaTwo_smul_character_values_centralThreeGenerator
  ] at hvalue
  calc
    (CyclicThree.thirdRootParameter
        (alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation r).1 :
      ℂ) =
        (CyclicThree.thirdRootParameter r.1 : ℂ)⁻¹ :=
      hvalue
    _ = (CyclicThree.thirdRootParameter (-r.1) : ℂ) := by
      simpa using congrArg Units.val
        (CyclicThree.thirdRootParameter_neg r.1).symm

/-- Under the invariant-safe orientation, the first audited local
permutation negates the cyclic-three coordinate. -/
theorem
    alternatingSixTwoCTblLibInvariantSafe_localAlphaOne_fst
    (i : Fin 12) :
    (alternatingSixTwoCTblLibInvariantSafeRowIdentification.localPositionEquiv
        (alternatingSixCTblLibTwoPPrimeActionData.localAlphaOne i)).1 =
      - (alternatingSixTwoCTblLibInvariantSafeRowIdentification
          |>.localPositionEquiv i).1 := by
  change
    (alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        (alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv
          (alternatingSixCTblLibTwoPPrimeActionData.candidate.symm
            (alternatingSixCTblLibTwoPPrimeActionData.localAlphaOne i)))).1 =
      - (alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
          (alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv
            (alternatingSixCTblLibTwoPPrimeActionData.candidate.symm i))).1
  rw [
    alternatingSixCTblLibTwo_candidate_symm_apply
      (alternatingSixCTblLibTwoPPrimeActionData.localAlphaOne i),
    alternatingSixCTblLibTwo_candidate_symm_apply i
  ]
  fin_cases i <;>
    rfl

/-- Under the invariant-safe orientation, the second audited local
permutation negates the cyclic-three coordinate. -/
theorem
    alternatingSixTwoCTblLibInvariantSafe_localAlphaTwo_fst
    (i : Fin 12) :
    (alternatingSixTwoCTblLibInvariantSafeRowIdentification.localPositionEquiv
        (alternatingSixCTblLibTwoPPrimeActionData.localAlphaTwo i)).1 =
      - (alternatingSixTwoCTblLibInvariantSafeRowIdentification
          |>.localPositionEquiv i).1 := by
  change
    (alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        (alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv
          (alternatingSixCTblLibTwoPPrimeActionData.candidate.symm
            (alternatingSixCTblLibTwoPPrimeActionData.localAlphaTwo i)))).1 =
      - (alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
          (alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv
            (alternatingSixCTblLibTwoPPrimeActionData.candidate.symm i))).1
  rw [
    alternatingSixCTblLibTwo_candidate_symm_apply
      (alternatingSixCTblLibTwoPPrimeActionData.localAlphaTwo i),
    alternatingSixCTblLibTwo_candidate_symm_apply i
  ]
  fin_cases i <;>
    rfl

/-- The residual first-generator local seam after the forced central
coordinate has been removed. -/
def AlternatingSixTwoInvariantSafeLocalAlphaOneSignBridge : Prop :=
  ∀ i : Fin 12,
    (alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
        (alternatingSixTwoCTblLibInvariantSafeRowIdentification
          |>.localPositionEquiv i)).2 =
      (alternatingSixTwoCTblLibInvariantSafeRowIdentification
        |>.localPositionEquiv
          (alternatingSixCTblLibTwoPPrimeActionData.localAlphaOne i)).2

/-- The residual second-generator local seam after the forced central
coordinate has been removed. -/
def AlternatingSixTwoInvariantSafeLocalAlphaTwoSignBridge : Prop :=
  ∀ i : Fin 12,
    (alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
        (alternatingSixTwoCTblLibInvariantSafeRowIdentification
          |>.localPositionEquiv i)).2 =
      (alternatingSixTwoCTblLibInvariantSafeRowIdentification
        |>.localPositionEquiv
          (alternatingSixCTblLibTwoPPrimeActionData.localAlphaTwo i)).2

/-- For the invariant-safe orientation, the first full local bridge is
exactly the residual quaternion sign-pair equality. -/
theorem
    alternatingSixTwoCTblLibInvariantSafe_localAlphaOneBridge_iff_signBridge :
    (alternatingSixTwoCTblLibInvariantSafeRowIdentification
        |>.LocalCorrectedAlphaOneBridge) ↔
      AlternatingSixTwoInvariantSafeLocalAlphaOneSignBridge := by
  constructor
  · intro h i
    exact congrArg Prod.snd (h i)
  · intro h i
    apply Prod.ext
    · rw [
        alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation_fst,
        alternatingSixTwoCTblLibInvariantSafe_localAlphaOne_fst
      ]
    · exact h i

/-- For the invariant-safe orientation, the second full local bridge is
exactly the residual quaternion sign-pair equality. -/
theorem
    alternatingSixTwoCTblLibInvariantSafe_localAlphaTwoBridge_iff_signBridge :
    (alternatingSixTwoCTblLibInvariantSafeRowIdentification
        |>.LocalCorrectedAlphaTwoBridge) ↔
      AlternatingSixTwoInvariantSafeLocalAlphaTwoSignBridge := by
  constructor
  · intro h i
    exact congrArg Prod.snd (h i)
  · intro h i
    apply Prod.ext
    · rw [
        alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation_fst,
        alternatingSixTwoCTblLibInvariantSafe_localAlphaTwo_fst
      ]
    · exact h i

end InductiveMcKay
end McKayConjecture
