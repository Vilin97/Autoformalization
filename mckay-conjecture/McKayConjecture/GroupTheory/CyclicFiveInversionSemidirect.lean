/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.QuaternionGroupLiftInjective
import Mathlib.GroupTheory.SemidirectProduct

/-!
# The inversion semidirect product of `C₅` by `C₄`

This file fixes a concrete model for `C₅ ⋊ C₄`, where a generator of
`C₄` acts on `C₅` by inversion.  Its square acts trivially, so the
resulting group is the dicyclic group of order twenty.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

abbrev CyclicFive := Multiplicative (ZMod 5)

abbrev CyclicFour := Multiplicative (ZMod 4)

private theorem cyclicFiveInversion_pow_four :
    (MulEquiv.inv CyclicFive : MulAut CyclicFive) ^ 4 = 1 := by
  ext i
  change i⁻¹⁻¹⁻¹⁻¹ = i
  simp

/-- The generator of `C₄` acts on `C₅` by inversion. -/
def cyclicFiveInversionAction : CyclicFour →* MulAut CyclicFive where
  toFun j :=
    QuaternionGroup.zmodPower
      (MulEquiv.inv CyclicFive)
      cyclicFiveInversion_pow_four
      (Multiplicative.toAdd j)
  map_one' :=
    QuaternionGroup.zmodPower_zero
      (MulEquiv.inv CyclicFive)
      cyclicFiveInversion_pow_four
  map_mul' i j :=
    QuaternionGroup.zmodPower_add
      (MulEquiv.inv CyclicFive)
      cyclicFiveInversion_pow_four
      (Multiplicative.toAdd i)
      (Multiplicative.toAdd j)

/-- The concrete inversion semidirect product `C₅ ⋊ C₄`. -/
abbrev CyclicFiveInversionSemidirect :=
  CyclicFive ⋊[cyclicFiveInversionAction] CyclicFour

/-- The canonical generator of the normal `C₅`. -/
def cyclicFiveSemidirectGenerator :
    CyclicFiveInversionSemidirect :=
  SemidirectProduct.inl (Multiplicative.ofAdd 1)

/-- The canonical generator of the acting `C₄`. -/
def cyclicFourSemidirectGenerator :
    CyclicFiveInversionSemidirect :=
  SemidirectProduct.inr (Multiplicative.ofAdd 1)

@[simp]
theorem cyclicFiveInversionAction_generator
    (i : CyclicFive) :
    cyclicFiveInversionAction (Multiplicative.ofAdd 1) i = i⁻¹ := by
  change
    QuaternionGroup.zmodPower
        (MulEquiv.inv CyclicFive)
        cyclicFiveInversion_pow_four
        ((1 : ℕ) : ZMod 4) i =
      i⁻¹
  rw [QuaternionGroup.zmodPower_natCast]
  rfl

@[simp]
theorem cyclicFiveInversionAction_generator_sq
    (i : CyclicFive) :
    cyclicFiveInversionAction
        ((Multiplicative.ofAdd 1 : CyclicFour) ^ 2) i =
      i := by
  change
    QuaternionGroup.zmodPower
        (MulEquiv.inv CyclicFive)
        cyclicFiveInversion_pow_four
        ((2 : ℕ) : ZMod 4) i =
      i
  rw [QuaternionGroup.zmodPower_natCast]
  change i⁻¹⁻¹ = i
  simp

@[simp]
theorem cyclicFiveSemidirectGenerator_pow_five :
    cyclicFiveSemidirectGenerator ^ 5 = 1 := by
  rw [cyclicFiveSemidirectGenerator, ← map_pow]
  congr

@[simp]
theorem cyclicFourSemidirectGenerator_pow_four :
    cyclicFourSemidirectGenerator ^ 4 = 1 := by
  rw [cyclicFourSemidirectGenerator, ← map_pow]
  congr

theorem cyclicFourSemidirectGenerator_conj :
    cyclicFourSemidirectGenerator *
          cyclicFiveSemidirectGenerator *
          cyclicFourSemidirectGenerator⁻¹ =
      cyclicFiveSemidirectGenerator⁻¹ := by
  rw [cyclicFourSemidirectGenerator,
    cyclicFiveSemidirectGenerator]
  calc
    SemidirectProduct.inr
          (Multiplicative.ofAdd (1 : ZMod 4)) *
          SemidirectProduct.inl
            (Multiplicative.ofAdd (1 : ZMod 5)) *
          (SemidirectProduct.inr
            (Multiplicative.ofAdd (1 : ZMod 4)))⁻¹ =
        SemidirectProduct.inl
          (cyclicFiveInversionAction
            (Multiplicative.ofAdd (1 : ZMod 4))
            (Multiplicative.ofAdd (1 : ZMod 5))) :=
      (SemidirectProduct.inl_aut
        (Multiplicative.ofAdd (1 : ZMod 4))
        (Multiplicative.ofAdd (1 : ZMod 5))).symm
    _ =
        SemidirectProduct.inl
          ((Multiplicative.ofAdd 1 : CyclicFive)⁻¹) := by
      rw [cyclicFiveInversionAction_generator]
    _ =
        (SemidirectProduct.inl
          (Multiplicative.ofAdd 1 : CyclicFive))⁻¹ := by
      rw [map_inv]

/-- The order-ten generator used to compare the semidirect product with
`QuaternionGroup 5`. -/
def cyclicFiveSemidirectDicyclicGenerator :
    CyclicFiveInversionSemidirect :=
  cyclicFiveSemidirectGenerator ^ 3 *
    cyclicFourSemidirectGenerator ^ 2

theorem cyclicFiveSemidirectDicyclicGenerator_sq :
    cyclicFiveSemidirectDicyclicGenerator ^ 2 =
      cyclicFiveSemidirectGenerator := by
  decide

theorem cyclicFiveSemidirectDicyclicGenerator_pow_ten :
    cyclicFiveSemidirectDicyclicGenerator ^ 10 = 1 := by
  decide

theorem cyclicFiveSemidirectDicyclicGenerator_pow_five :
    cyclicFiveSemidirectDicyclicGenerator ^ 5 =
      cyclicFourSemidirectGenerator ^ 2 := by
  decide

theorem cyclicFiveSemidirectDicyclicGenerator_mul_fourGenerator :
    cyclicFiveSemidirectDicyclicGenerator *
          cyclicFourSemidirectGenerator =
      cyclicFourSemidirectGenerator *
        cyclicFiveSemidirectDicyclicGenerator⁻¹ := by
  decide

private theorem cyclicFourSemidirectGenerator_sq_zmodPower :
    cyclicFourSemidirectGenerator *
        cyclicFourSemidirectGenerator =
      QuaternionGroup.zmodPower
        cyclicFiveSemidirectDicyclicGenerator
        cyclicFiveSemidirectDicyclicGenerator_pow_ten
        ((5 : ℕ) : ZMod 10) := by
  rw [QuaternionGroup.zmodPower_natCast]
  simpa [pow_two] using
    cyclicFiveSemidirectDicyclicGenerator_pow_five.symm

private theorem cyclicFiveSemidirectDicyclicConj
    (i : ZMod 10) :
    QuaternionGroup.zmodPower
          cyclicFiveSemidirectDicyclicGenerator
          cyclicFiveSemidirectDicyclicGenerator_pow_ten i *
        cyclicFourSemidirectGenerator =
      cyclicFourSemidirectGenerator *
        QuaternionGroup.zmodPower
          cyclicFiveSemidirectDicyclicGenerator
          cyclicFiveSemidirectDicyclicGenerator_pow_ten (-i) :=
  QuaternionGroup.zmodPower_mul_eq_mul_zmodPower_neg
    cyclicFiveSemidirectDicyclicGenerator
    cyclicFourSemidirectGenerator
    cyclicFiveSemidirectDicyclicGenerator_pow_ten
    cyclicFiveSemidirectDicyclicGenerator_mul_fourGenerator i

/-- The dicyclic presentation map into the inversion semidirect
product. -/
def quaternionFiveToCyclicFiveInversionSemidirect :
    QuaternionGroup 5 →* CyclicFiveInversionSemidirect :=
  QuaternionGroup.lift
    cyclicFiveSemidirectDicyclicGenerator
    cyclicFourSemidirectGenerator
    cyclicFiveSemidirectDicyclicGenerator_pow_ten
    cyclicFourSemidirectGenerator_sq_zmodPower
    cyclicFiveSemidirectDicyclicConj

@[simp]
theorem quaternionFiveToCyclicFiveInversionSemidirect_a_one :
    quaternionFiveToCyclicFiveInversionSemidirect
        (QuaternionGroup.a 1) =
      cyclicFiveSemidirectDicyclicGenerator := by
  change
    QuaternionGroup.zmodPower
        cyclicFiveSemidirectDicyclicGenerator
        cyclicFiveSemidirectDicyclicGenerator_pow_ten
        ((1 : ℕ) : ZMod 10) =
      cyclicFiveSemidirectDicyclicGenerator
  rw [QuaternionGroup.zmodPower_natCast]
  simp

@[simp]
theorem quaternionFiveToCyclicFiveInversionSemidirect_xa_zero :
    quaternionFiveToCyclicFiveInversionSemidirect
        (QuaternionGroup.xa 0) =
      cyclicFourSemidirectGenerator := by
  change
    cyclicFourSemidirectGenerator *
        QuaternionGroup.zmodPower
          cyclicFiveSemidirectDicyclicGenerator
          cyclicFiveSemidirectDicyclicGenerator_pow_ten
          (0 : ZMod 10) =
      cyclicFourSemidirectGenerator
  rw [QuaternionGroup.zmodPower_zero]
  simp

theorem cyclicFourSemidirectGenerator_sq_mem_center :
    cyclicFourSemidirectGenerator ^ 2 ∈
      Subgroup.center CyclicFiveInversionSemidirect := by
  rw [Subgroup.mem_center_iff]
  intro y
  rw [cyclicFourSemidirectGenerator]
  rw [show
    (SemidirectProduct.inr
        (Multiplicative.ofAdd (1 : ZMod 4)) :
          CyclicFiveInversionSemidirect) ^ 2 =
      SemidirectProduct.inr
        ((Multiplicative.ofAdd (1 : ZMod 4) :
          CyclicFour) ^ 2) from
    ((SemidirectProduct.inr :
      CyclicFour →* CyclicFiveInversionSemidirect).map_pow
        (Multiplicative.ofAdd (1 : ZMod 4)) 2).symm]
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left,
      SemidirectProduct.left_inr, map_one,
      mul_one, one_mul]
    exact
      (cyclicFiveInversionAction_generator_sq y.left).symm
  · simp only [SemidirectProduct.mul_right,
      SemidirectProduct.right_inr]
    exact mul_comm _ _

theorem quaternionFiveToCyclicFiveInversionSemidirect_surjective :
    Function.Surjective
      quaternionFiveToCyclicFiveInversionSemidirect := by
  intro y
  rw [← SemidirectProduct.inl_left_mul_inr_right y]
  refine ⟨
    (QuaternionGroup.a 1) ^
        (2 * (Multiplicative.toAdd y.left).val) *
      (QuaternionGroup.xa 0) ^
        (Multiplicative.toAdd y.right).val, ?_⟩
  rw [map_mul, map_pow, map_pow,
    quaternionFiveToCyclicFiveInversionSemidirect_a_one,
    quaternionFiveToCyclicFiveInversionSemidirect_xa_zero]
  have hleft :
      cyclicFiveSemidirectDicyclicGenerator ^
          (2 * (Multiplicative.toAdd y.left).val) =
        cyclicFiveSemidirectGenerator ^
          (Multiplicative.toAdd y.left).val := by
    rw [pow_mul,
      cyclicFiveSemidirectDicyclicGenerator_sq]
  rw [hleft]
  congr
  · rw [cyclicFiveSemidirectGenerator,
      ← map_pow]
    congr
    apply Multiplicative.toAdd.injective
    simp
  · rw [cyclicFourSemidirectGenerator,
      ← map_pow]
    congr
    apply Multiplicative.toAdd.injective
    simp

private noncomputable instance :
    Fintype CyclicFiveInversionSemidirect :=
  Fintype.ofEquiv (CyclicFive × CyclicFour)
    SemidirectProduct.equivProd.symm

/-- The inversion semidirect product is the standard dicyclic group of
order twenty. -/
def quaternionFiveEquivCyclicFiveInversionSemidirect :
    QuaternionGroup 5 ≃* CyclicFiveInversionSemidirect :=
  MulEquiv.ofBijective
    quaternionFiveToCyclicFiveInversionSemidirect
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨
        quaternionFiveToCyclicFiveInversionSemidirect_surjective,
        by
          rw [QuaternionGroup.card]
          change 20 = Fintype.card CyclicFiveInversionSemidirect
          rw [Fintype.card_congr SemidirectProduct.equivProd]
          simp [ZMod.card, Fintype.card_multiplicative]⟩)

@[simp]
theorem orderOf_cyclicFourSemidirectGenerator :
    orderOf cyclicFourSemidirectGenerator = 4 := by
  calc
    orderOf cyclicFourSemidirectGenerator =
        orderOf
          (quaternionFiveEquivCyclicFiveInversionSemidirect
            (QuaternionGroup.xa 0)) := by
      rw [quaternionFiveEquivCyclicFiveInversionSemidirect]
      exact congrArg orderOf
        quaternionFiveToCyclicFiveInversionSemidirect_xa_zero.symm
    _ = orderOf (QuaternionGroup.xa (0 : ZMod 10)) :=
      quaternionFiveEquivCyclicFiveInversionSemidirect.orderOf_eq _
    _ = 4 := by
      exact QuaternionGroup.orderOf_xa
        (n := 5) (0 : ZMod 10)

@[simp]
theorem orderOf_cyclicFourSemidirectGenerator_sq :
    orderOf (cyclicFourSemidirectGenerator ^ 2) = 2 := by
  rw [orderOf_pow, orderOf_cyclicFourSemidirectGenerator]
  norm_num

end GroupTheory
end McKayConjecture
