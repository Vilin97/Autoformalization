/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurFiveNormalizerSemidirect

/-!
# The central generator in the five-normalizer product model

The concrete five-normalizer is `C₃ × (C₅ ⋊ C₄)`.  The generator `c` of
the order-six center of the presented cover is represented in this product
by

`(2, x²)`,

where `2 : ZMod 3` contributes `c⁴` and the square of the `C₄` generator
contributes the central involution `c³`.  Their product is `c⁷ = c`.

This exact identification is the group-theoretic input needed to compare
the central-character blocks of the ambient and five-local character
tables.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- The element of the concrete five-normalizer model representing the
distinguished order-six central generator of the presented cover. -/
def alternatingSixFiveNormalizerSemidirectCentralGenerator :
    Multiplicative (ZMod 3) × CyclicFiveInversionSemidirect :=
  (Multiplicative.ofAdd 2, cyclicFourSemidirectGenerator ^ 2)

/-- The square of the `C₄` generator pulls back to the central element
`a⁵` of the dicyclic presentation. -/
theorem
    quaternionFiveEquivCyclicFiveInversionSemidirect_symm_generator_sq :
    quaternionFiveEquivCyclicFiveInversionSemidirect.symm
        (cyclicFourSemidirectGenerator ^ 2) =
      QuaternionGroup.a (5 : ZMod 10) := by
  apply quaternionFiveEquivCyclicFiveInversionSemidirect.injective
  rw [
    quaternionFiveEquivCyclicFiveInversionSemidirect.apply_symm_apply
  ]
  change
    cyclicFourSemidirectGenerator ^ 2 =
      QuaternionGroup.zmodPower
        cyclicFiveSemidirectDicyclicGenerator
        cyclicFiveSemidirectDicyclicGenerator_pow_ten
        (5 : ZMod 10)
  rw [
    show (5 : ZMod 10) = ((5 : ℕ) : ZMod 10) by rfl,
    QuaternionGroup.zmodPower_natCast
  ]
  exact cyclicFiveSemidirectDicyclicGenerator_pow_five.symm

/-- The element `2` in the cyclic-three factor maps to `c⁴`. -/
theorem alternatingSixSchurFiveCentralThreeHom_ofAdd_two :
    alternatingSixSchurFiveCentralThreeHom
        (Multiplicative.ofAdd 2) =
      alternatingSixSchurFiveCentral ^ 4 := by
  have hinput :
      (Multiplicative.ofAdd 2 : Multiplicative (ZMod 3)) =
        (Multiplicative.ofAdd 1) ^ 2 := by
    decide
  rw [hinput, map_pow]
  have hgenerator :
      alternatingSixSchurFiveCentralThreeHom
          (Multiplicative.ofAdd 1) =
        alternatingSixSchurFiveCentral ^ 2 := by
    have hpow :
        (alternatingSixSchurFiveCentral ^ 2) ^ 3 = 1 := by
      rw [← pow_mul]
      exact alternatingSixSchurPresentedK0_pow_six
    change
      QuaternionGroup.zmodPower
          (alternatingSixSchurFiveCentral ^ 2)
          hpow (1 : ZMod 3) =
        _
    rw [
      show (1 : ZMod 3) = ((1 : ℕ) : ZMod 3) by rfl,
      QuaternionGroup.zmodPower_natCast,
      pow_one
    ]
  rw [hgenerator]
  group

/-- The product-model central generator maps exactly to the distinguished
central generator `c` in the presented cover. -/
theorem
    cyclicThreeTimesCyclicFiveInversionSemidirectEquivSchurFiveNormalizer_centralGenerator :
    ((cyclicThreeTimesCyclicFiveInversionSemidirectEquivSchurFiveNormalizer
          alternatingSixFiveNormalizerSemidirectCentralGenerator :
        Subgroup.normalizer
          (alternatingSixSchurFiveSylow :
            Set AlternatingSixSchurPresentedGroup)) :
      AlternatingSixSchurPresentedGroup) =
        alternatingSixSchurFiveCentral := by
  rw [
    cyclicThreeTimesCyclicFiveInversionSemidirectEquivSchurFiveNormalizer,
    MulEquiv.trans_apply
  ]
  change
    ((cyclicThreeTimesQuaternionFiveEquivSchurFiveNormalizer
          (Multiplicative.ofAdd 2,
            quaternionFiveEquivCyclicFiveInversionSemidirect.symm
              (cyclicFourSemidirectGenerator ^ 2)) :
        Subgroup.normalizer
          (alternatingSixSchurFiveSylow :
            Set AlternatingSixSchurPresentedGroup)) :
      AlternatingSixSchurPresentedGroup) =
        _
  rw [
    quaternionFiveEquivCyclicFiveInversionSemidirect_symm_generator_sq
  ]
  change
    alternatingSixSchurFiveCentralThreeHom
          (Multiplicative.ofAdd 2) *
        quaternionFiveToAlternatingSixSchur
          (QuaternionGroup.a (5 : ZMod 10)) =
      _
  rw [alternatingSixSchurFiveCentralThreeHom_ofAdd_two]
  change
    alternatingSixSchurFiveCentral ^ 4 *
        QuaternionGroup.zmodPower
          alternatingSixSchurFiveDicyclicGenerator
          alternatingSixSchurFiveDicyclicGenerator_pow_ten
          (5 : ZMod 10) =
      _
  rw [
    show (5 : ZMod 10) = ((5 : ℕ) : ZMod 10) by rfl,
    QuaternionGroup.zmodPower_natCast,
    alternatingSixSchurFiveDicyclicGenerator_pow_five
  ]
  calc
    alternatingSixSchurFiveCentral ^ 4 *
          alternatingSixSchurFiveCentral ^ 3 =
        alternatingSixSchurFiveCentral ^ 7 := by
      group
    _ = alternatingSixSchurFiveCentral := by
      rw [
        show alternatingSixSchurFiveCentral ^ 7 =
            alternatingSixSchurFiveCentral ^ 6 *
              alternatingSixSchurFiveCentral by
          group,
        alternatingSixSchurPresentedK0_pow_six,
        one_mul
      ]

end GroupTheory
end McKayConjecture
