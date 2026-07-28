/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.SpecialLinearTwoFive
import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# The Sylow-three normalizer in `SL(2, 𝔽₅)`

The normalizer of the chosen Sylow `3`-subgroup of `SL(2, ZMod 5)` is the
generalized quaternion group of order twelve.  This file makes the
identification executable.

The two matrix generators are

* `A = -[[0,-1],[1,-1]]`, of order six; and
* `X = [[0,2],[2,0]]`, of order four.

They satisfy `X² = A³` and `X⁻¹ A X = A⁻¹`.  The map from
`QuaternionGroup 3`, in its concrete `a i`/`xa i` normal form, sends
`a i` to `A ^ i.val` and `xa i` to `X * A ^ i.val`.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace McKayConjecture
namespace GroupTheory

/-- The exact normalizer of the chosen Sylow `3`-subgroup. -/
abbrev SpecialLinearTwoFiveSylowThreeNormalizer :=
  Subgroup.normalizer
    (specialLinearTwoFiveSylowThree : Set SpecialLinearTwoFive)

local instance :
    Fintype SpecialLinearTwoFiveSylowThreeNormalizer :=
  Fintype.ofFinite SpecialLinearTwoFiveSylowThreeNormalizer

/-- The order-six cyclic generator in the Sylow `3`-normalizer. -/
def specialLinearTwoFiveSylowThreeNormalizerA :
    SpecialLinearTwoFiveSylowThreeNormalizer :=
  ⟨-specialLinearTwoFive_orderThreeElement, by
    rw [Subgroup.mem_set_normalizer_iff,
      coe_specialLinearTwoFiveSylowThree]
    native_decide⟩

/-- The ambient order-four matrix used for the second normalizer
generator. -/
def specialLinearTwoFiveSylowThreeNormalizerXMatrix :
    SpecialLinearTwoFive :=
  ⟨!![(0 : ZMod 5), 2; 2, 0], by native_decide⟩

/-- The order-four quaternion generator in the Sylow `3`-normalizer. -/
def specialLinearTwoFiveSylowThreeNormalizerX :
    SpecialLinearTwoFiveSylowThreeNormalizer :=
  ⟨specialLinearTwoFiveSylowThreeNormalizerXMatrix, by
    rw [Subgroup.mem_set_normalizer_iff,
      coe_specialLinearTwoFiveSylowThree]
    native_decide⟩

/-- The two explicit normalizer generators obey the generalized quaternion
relations for `QuaternionGroup 3`. -/
theorem specialLinearTwoFiveSylowThreeNormalizer_generator_relations :
    specialLinearTwoFiveSylowThreeNormalizerA ^ 6 = 1 ∧
      specialLinearTwoFiveSylowThreeNormalizerX ^ 2 =
        specialLinearTwoFiveSylowThreeNormalizerA ^ 3 ∧
      specialLinearTwoFiveSylowThreeNormalizerX⁻¹ *
          specialLinearTwoFiveSylowThreeNormalizerA *
          specialLinearTwoFiveSylowThreeNormalizerX =
        specialLinearTwoFiveSylowThreeNormalizerA⁻¹ := by
  native_decide

/-- The executable homomorphism from generalized quaternion normal forms to
the exact Sylow `3`-normalizer. -/
def quaternionGroupThreeToSpecialLinearTwoFiveSylowThreeNormalizer :
    QuaternionGroup 3 →*
      SpecialLinearTwoFiveSylowThreeNormalizer where
  toFun
    | QuaternionGroup.a i =>
        specialLinearTwoFiveSylowThreeNormalizerA ^ i.val
    | QuaternionGroup.xa i =>
        specialLinearTwoFiveSylowThreeNormalizerX *
          specialLinearTwoFiveSylowThreeNormalizerA ^ i.val
  map_one' := by native_decide
  map_mul' := by native_decide

/-- The explicit normal-form homomorphism is a bijection. -/
theorem quaternionGroupThreeToSpecialLinearTwoFiveSylowThreeNormalizer_bijective :
    Function.Bijective
      quaternionGroupThreeToSpecialLinearTwoFiveSylowThreeNormalizer := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro g h
    rcases g with i | i <;> rcases h with j | j
    all_goals
      revert i j
      native_decide
  · rw [QuaternionGroup.card]
    norm_num
    rw [← Nat.card_eq_fintype_card]
    exact natCard_specialLinearTwoFiveSylowThreeNormalizer.symm

/-- The concrete multiplicative equivalence
`QuaternionGroup 3 ≃* N_SL(2,5)(P₃)`. -/
def quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer :
    QuaternionGroup 3 ≃*
      SpecialLinearTwoFiveSylowThreeNormalizer :=
  MulEquiv.ofBijective
    quaternionGroupThreeToSpecialLinearTwoFiveSylowThreeNormalizer
    quaternionGroupThreeToSpecialLinearTwoFiveSylowThreeNormalizer_bijective

@[simp]
theorem quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer_apply_a
    (i : ZMod 6) :
    quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer
        (QuaternionGroup.a i) =
      specialLinearTwoFiveSylowThreeNormalizerA ^ i.val :=
  rfl

@[simp]
theorem quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer_apply_xa
    (i : ZMod 6) :
    quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer
        (QuaternionGroup.xa i) =
      specialLinearTwoFiveSylowThreeNormalizerX *
        specialLinearTwoFiveSylowThreeNormalizerA ^ i.val :=
  rfl

end GroupTheory
end McKayConjecture
