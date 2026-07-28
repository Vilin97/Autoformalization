/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import McKayConjecture.GroupTheory.SpecialLinearTwoFive

/-!
# The Sylow-five normalizer in `SL(2, 𝔽₅)`

The normalizer of the fixed upper-unitriangular Sylow `5`-subgroup is the
dicyclic group of order twenty.  We identify it explicitly with
`QuaternionGroup 5`.

The dicyclic generator `a` is sent to the order-ten matrix `-u`, where
`u = [[1,1],[0,1]]`, and `x` is sent to `diag(2,3)`.  These satisfy

* `a ^ 10 = 1`;
* `x ^ 2 = a ^ 5 = -1`; and
* `x * a * x⁻¹ = a⁻¹`.

The finite multiplication and normalizer checks are kernel-checked by
native evaluation.  No presentation theorem is used.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace McKayConjecture
namespace GroupTheory

/-- The order-ten dicyclic generator in the Sylow-five normalizer. -/
def specialLinearTwoFiveSylowFiveNormalizerA :
    SpecialLinearTwoFive :=
  -specialLinearTwoFive_orderFiveElement

/-- The order-four dicyclic generator in the Sylow-five normalizer. -/
def specialLinearTwoFiveSylowFiveNormalizerX :
    SpecialLinearTwoFive :=
  specialLinearTwoFiveQuaternionJ

/-- The concrete dicyclic map into `SL(2, 𝔽₅)`. -/
def quaternionFiveToSpecialLinearTwoFive :
    QuaternionGroup 5 →* SpecialLinearTwoFive where
  toFun
    | QuaternionGroup.a i =>
        specialLinearTwoFiveSylowFiveNormalizerA ^ i.val
    | QuaternionGroup.xa i =>
        specialLinearTwoFiveSylowFiveNormalizerX *
          specialLinearTwoFiveSylowFiveNormalizerA ^ i.val
  map_one' := by
    native_decide
  map_mul' := by
    native_decide

/-- The concrete dicyclic map is injective. -/
theorem quaternionFiveToSpecialLinearTwoFive_injective :
    Function.Injective quaternionFiveToSpecialLinearTwoFive := by
  native_decide

/-- Every element in the concrete dicyclic image normalizes the fixed
Sylow-five subgroup. -/
theorem quaternionFiveToSpecialLinearTwoFive_mem_normalizer
    (g : QuaternionGroup 5) :
    quaternionFiveToSpecialLinearTwoFive g ∈
      Subgroup.normalizer
        (specialLinearTwoFiveSylowFive :
          Set SpecialLinearTwoFive) := by
  change
    quaternionFiveToSpecialLinearTwoFive g ∈
      (Subgroup.normalizer
        ((specialLinearTwoFiveSylowFive :
          Subgroup SpecialLinearTwoFive) :
          Set SpecialLinearTwoFive) :
        Set SpecialLinearTwoFive)
  rw [coe_finiteSetNormalizer
    (specialLinearTwoFiveSylowFive :
      Subgroup SpecialLinearTwoFive)
    specialLinearTwoFiveFiveSubgroupElements
    coe_specialLinearTwoFiveSylowFive]
  rcases g with i | i <;>
    fin_cases i <;>
      native_decide

/-- The concrete dicyclic homomorphism, with codomain restricted to the
exact Sylow-five normalizer. -/
def quaternionFiveToSylowFiveNormalizer :
    QuaternionGroup 5 →*
      Subgroup.normalizer
        (specialLinearTwoFiveSylowFive :
          Set SpecialLinearTwoFive) :=
  quaternionFiveToSpecialLinearTwoFive.codRestrict
    (Subgroup.normalizer
      (specialLinearTwoFiveSylowFive :
        Set SpecialLinearTwoFive))
    quaternionFiveToSpecialLinearTwoFive_mem_normalizer

/-- The restricted dicyclic homomorphism is bijective. -/
theorem quaternionFiveToSylowFiveNormalizer_bijective :
    Function.Bijective quaternionFiveToSylowFiveNormalizer := by
  apply
    (Nat.bijective_iff_injective_and_card
      quaternionFiveToSylowFiveNormalizer).2
  constructor
  · intro g h hgh
    apply quaternionFiveToSpecialLinearTwoFive_injective
    exact congrArg Subtype.val hgh
  · rw [natCard_specialLinearTwoFiveSylowFiveNormalizer]
    change Nat.card (QuaternionGroup 5) = 20
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

/-- The fixed Sylow-five normalizer is the dicyclic group of order
twenty. -/
def quaternionFiveEquivSylowFiveNormalizer :
    QuaternionGroup 5 ≃*
      Subgroup.normalizer
        (specialLinearTwoFiveSylowFive :
          Set SpecialLinearTwoFive) :=
  MulEquiv.ofBijective
    quaternionFiveToSylowFiveNormalizer
    quaternionFiveToSylowFiveNormalizer_bijective

@[simp]
theorem quaternionFiveEquivSylowFiveNormalizer_apply
    (g : QuaternionGroup 5) :
    (quaternionFiveEquivSylowFiveNormalizer g :
      SpecialLinearTwoFive) =
        quaternionFiveToSpecialLinearTwoFive g :=
  rfl

end GroupTheory
end McKayConjecture
