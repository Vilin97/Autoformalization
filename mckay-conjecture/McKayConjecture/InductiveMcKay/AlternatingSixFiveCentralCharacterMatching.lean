/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.AlternatingSixFiveNormalizerCentralCharacter
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCentralBlockRowMatching

/-!
# Exact advertised central-scalar matching for the five-local `A₆` table

This file aligns the analytic roots used by the concrete normalizer
character table with the fixed primitive 120th root used by the ambient
`6.A₆` matrix table.  It then proves that the concrete model's central
scalar is exactly the scalar advertised by its ambient central-block
label.  Transport to the fixed actual normalizer and evaluation of the
ambient enumerated character at the corresponding central element are
separate character-level obligations.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The cyclic-three root used by the local table is the fortieth power
of the ambient primitive 120th root. -/
theorem cyclicThree_primitiveThirdRoot_eq_ambientRoot_pow_forty :
    CyclicThree.primitiveThirdRoot = ζ ^ 40 := by
  rw [CyclicThree.primitiveThirdRoot,
    alternatingSixComplexCyclotomicRoot, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- The dicyclic tenth root used by the local table is the twelfth power
of the ambient primitive 120th root. -/
theorem quaternionFive_primitiveTenthRoot_eq_ambientRoot_pow_twelve :
    QuaternionGroupFive.primitiveTenthRoot = ζ ^ 12 := by
  rw [QuaternionGroupFive.primitiveTenthRoot,
    alternatingSixComplexCyclotomicRoot, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- The sixtieth power of the ambient root is `-1`. -/
theorem alternatingSixComplexCyclotomicRoot_pow_sixty :
    ζ ^ 60 = -1 := by
  rw [alternatingSixComplexCyclotomicRoot, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1 <;> ring

/-- The central involution scalar in a concrete dicyclic row is exactly
the sign recorded by `alternatingSixFiveDicyclicCentralIsNegative`. -/
theorem fiveNormalizer_dicyclicCentralScalar_eq_sign
    (r : CyclicFiveInversionSemidirect.CharacterRow) :
    AlternatingSixFiveNormalizerSemidirectCharacterTable.dicyclicCentralScalar r =
      if alternatingSixFiveDicyclicCentralIsNegative r then
        (ζ ^ 60)
      else
        1 := by
  rcases r with k | k
  · fin_cases k <;>
      norm_num [
        AlternatingSixFiveNormalizerSemidirectCharacterTable.dicyclicCentralScalar,
        alternatingSixFiveDicyclicCentralIsNegative,
        QuaternionGroupFive.fourthRootParameter,
        QuaternionGroupFive.imaginaryUnit,
        Complex.I_mul_I,
        alternatingSixComplexCyclotomicRoot_pow_sixty
      ]
  · fin_cases k
    · simp only [
        AlternatingSixFiveNormalizerSemidirectCharacterTable.dicyclicCentralScalar,
        QuaternionGroupFive.twoDimensionalParameter,
        quaternionFive_primitiveTenthRoot_eq_ambientRoot_pow_twelve,
        Fin.isValue,
        Fin.val_zero,
        zero_add,
        pow_one
      ]
      ring_nf
      rfl
    · simp only [
        AlternatingSixFiveNormalizerSemidirectCharacterTable.dicyclicCentralScalar,
        QuaternionGroupFive.twoDimensionalParameter,
        quaternionFive_primitiveTenthRoot_eq_ambientRoot_pow_twelve,
        alternatingSixFiveDicyclicCentralIsNegative,
        Fin.isValue,
        Fin.val_one,
        Nat.reduceAdd,
        Bool.false_eq_true,
        ↓reduceIte
      ]
      ring_nf
      exact alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one
    · simp only [
        AlternatingSixFiveNormalizerSemidirectCharacterTable.dicyclicCentralScalar,
        QuaternionGroupFive.twoDimensionalParameter,
        quaternionFive_primitiveTenthRoot_eq_ambientRoot_pow_twelve,
        alternatingSixFiveDicyclicCentralIsNegative,
        Fin.isValue,
        Bool.true_eq_false,
        ↓reduceIte
      ]
      ring_nf
      rw [show (180 : ℕ) = 120 + 60 by omega, pow_add,
        alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one,
        one_mul]
      simp [alternatingSixFiveDicyclicCentralIsNegative]
    · simp only [
        AlternatingSixFiveNormalizerSemidirectCharacterTable.dicyclicCentralScalar,
        QuaternionGroupFive.twoDimensionalParameter,
        quaternionFive_primitiveTenthRoot_eq_ambientRoot_pow_twelve,
        alternatingSixFiveDicyclicCentralIsNegative,
        Fin.isValue,
        Bool.false_eq_true,
        ↓reduceIte
      ]
      ring_nf
      rw [show (240 : ℕ) = 120 + 120 by omega, pow_add,
        alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one,
        one_mul]
      simp [alternatingSixFiveDicyclicCentralIsNegative]

/-- The cyclic-three contribution at the element `2` has exponents
`0`, `80`, and `40` in the ambient root convention. -/
theorem fiveNormalizer_cyclicThreeCentralScalar
    (j : Fin 3) :
    (CyclicThree.thirdRootParameter j : ℂ) ^ 2 =
      ζ ^ (![0, 80, 40] j) := by
  fin_cases j <;>
    simp [
      CyclicThree.thirdRootParameter,
      CyclicThree.primitiveThirdRootUnit,
      cyclicThree_primitiveThirdRoot_eq_ambientRoot_pow_forty,
      ← pow_mul
    ]
  · rw [show (160 : ℕ) = 120 + 40 by omega, pow_add,
      alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one,
      one_mul]

/-- The concrete central scalar attached to a five-normalizer row agrees
with the first scalar in its sixfold-cover central-block pattern. -/
theorem fiveNormalizer_centralScalar_eq_centralBlock
    (r : AlternatingSixFiveConcreteNormalizerRow) :
    AlternatingSixFiveNormalizerSemidirectCharacterTable.centralScalar r =
      ζ ^
        (alternatingSixFiveConcreteNormalizerCentralBlock r).exponent 0 := by
  rcases r with ⟨j, r⟩
  rw [
    AlternatingSixFiveNormalizerSemidirectCharacterTable.centralScalar,
    fiveNormalizer_cyclicThreeCentralScalar,
    fiveNormalizer_dicyclicCentralScalar_eq_sign
  ]
  rcases r with k | k <;> fin_cases j <;> fin_cases k
  all_goals
    simp [
      alternatingSixFiveConcreteNormalizerCentralBlock,
      alternatingSixFiveDicyclicCentralIsNegative,
      AlternatingSixAmbientScalarPattern.exponent
    ]
  all_goals try ring
  all_goals
    rw [show (140 : ℕ) = 120 + 20 by omega, pow_add,
      alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one,
      one_mul]

/-- The explicit legacy-index matching preserves the exact complex scalar,
not merely its finite central-block label. -/
theorem alternatingSixFiveCentralBlockRowEquiv_preserves_centralScalar
    (r : AlternatingSixFiveAmbientRow) :
    AlternatingSixFiveNormalizerSemidirectCharacterTable.centralScalar
        (alternatingSixFiveCentralBlockRowEquiv r) =
      ζ ^ r.toAmbientRowIndex.scalarPattern.exponent 0 := by
  rw [fiveNormalizer_centralScalar_eq_centralBlock,
    alternatingSixFiveCentralBlockRowEquiv_preserves_centralBlock]

/-- Exact scalar preservation for the arithmetic prime-to-five ambient
row subtype. -/
theorem
    alternatingSixAmbientFivePPrimeCentralBlockRowEquiv_preserves_centralScalar
    (r : AlternatingSixAmbientPPrimeRowIndex 5) :
    AlternatingSixFiveNormalizerSemidirectCharacterTable.centralScalar
        (alternatingSixAmbientFivePPrimeCentralBlockRowEquiv r) =
      ζ ^ r.1.scalarPattern.exponent 0 := by
  rw [fiveNormalizer_centralScalar_eq_centralBlock,
    alternatingSixAmbientFivePPrimeCentralBlockRowEquiv_preserves_centralBlock]

end InductiveMcKay
end McKayConjecture
