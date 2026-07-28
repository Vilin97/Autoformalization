/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurFiveNormalizerModel
import McKayConjecture.GroupTheory.QuaternionGroupLiftInjective

/-!
# The dicyclic factor of the five-local normalizer

The corrected elements from
`AlternatingSixSchurFiveNormalizerModel` generate an explicit copy of
`QuaternionGroup 5`.  The order-ten generator is
`p³c³`; its fifth power and the square of the order-four generator are
both the central involution `c³`.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixSchurFiveFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

@[simp]
theorem orderOf_alternatingSixSchurFiveCentral :
    orderOf alternatingSixSchurFiveCentral = 6 :=
  orderOf_alternatingSixSchurPresentedK0

@[simp]
theorem alternatingSixSchurProjection_fiveElement :
    alternatingSixSchurProjection alternatingSixSchurFiveElement =
      alternatingSixPresentationA *
        alternatingSixPresentationB ^ 2 := by
  simp [alternatingSixSchurFiveElement,
    alternatingSixSchurFiveCentral]

theorem alternatingSixSchurFiveElement_ne_one :
    alternatingSixSchurFiveElement ≠ 1 := by
  intro h
  have hmap := congrArg alternatingSixSchurProjection h
  rw [alternatingSixSchurProjection_fiveElement,
    map_one] at hmap
  exact
    (by decide :
      alternatingSixPresentationA *
          alternatingSixPresentationB ^ 2 ≠
        (1 : AlternatingSix)) hmap

@[simp]
theorem orderOf_alternatingSixSchurFiveElement :
    orderOf alternatingSixSchurFiveElement = 5 :=
  orderOf_eq_prime
    alternatingSixSchurFiveElement_pow_five
    alternatingSixSchurFiveElement_ne_one

theorem alternatingSixSchurFiveCentral_pow_three_ne_one :
    alternatingSixSchurFiveCentral ^ 3 ≠ 1 := by
  intro h
  have hdvd := orderOf_dvd_of_pow_eq_one h
  rw [orderOf_alternatingSixSchurFiveCentral] at hdvd
  norm_num at hdvd

@[simp]
theorem orderOf_alternatingSixSchurFiveCentral_pow_three :
    orderOf (alternatingSixSchurFiveCentral ^ 3) = 2 := by
  rw [orderOf_pow,
    orderOf_alternatingSixSchurFiveCentral]
  norm_num

@[simp]
theorem orderOf_alternatingSixSchurFiveCentral_sq :
    orderOf (alternatingSixSchurFiveCentral ^ 2) = 3 := by
  rw [orderOf_pow,
    orderOf_alternatingSixSchurFiveCentral]
  norm_num

@[simp]
theorem orderOf_alternatingSixSchurFiveNormalizerElement :
    orderOf alternatingSixSchurFiveNormalizerElement = 4 := by
  change
    orderOf alternatingSixSchurFiveNormalizerElement =
      2 ^ (1 + 1)
  apply orderOf_eq_prime_pow
  · norm_num
    simpa [alternatingSixSchurFiveNormalizerElement_sq] using
      alternatingSixSchurFiveCentral_pow_three_ne_one
  · norm_num
    calc
      alternatingSixSchurFiveNormalizerElement ^ 4 =
          (alternatingSixSchurFiveNormalizerElement ^ 2) ^ 2 := by group
      _ = (alternatingSixSchurFiveCentral ^ 3) ^ 2 := by
            rw [alternatingSixSchurFiveNormalizerElement_sq]
      _ = alternatingSixSchurFiveCentral ^ 6 := by group
      _ = 1 := alternatingSixSchurPresentedK0_pow_six

theorem orderOf_alternatingSixSchurFiveElement_pow_three :
    orderOf (alternatingSixSchurFiveElement ^ 3) = 5 := by
  rw [orderOf_pow,
    orderOf_alternatingSixSchurFiveElement]
  norm_num

@[simp]
theorem orderOf_alternatingSixSchurFiveDicyclicGenerator :
    orderOf alternatingSixSchurFiveDicyclicGenerator = 10 := by
  rw [alternatingSixSchurFiveDicyclicGenerator]
  have hcomm :
      Commute
        (alternatingSixSchurFiveElement ^ 3)
        (alternatingSixSchurFiveCentral ^ 3) :=
    ((alternatingSixSchurFiveCentral_commute
      (alternatingSixSchurFiveElement ^ 3)).pow_left 3).symm
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime]
  · rw [orderOf_alternatingSixSchurFiveElement_pow_three,
      orderOf_alternatingSixSchurFiveCentral_pow_three]
  · rw [orderOf_alternatingSixSchurFiveElement_pow_three,
      orderOf_alternatingSixSchurFiveCentral_pow_three]
    norm_num

theorem alternatingSixSchurFiveDicyclicGenerator_pow_ten :
    alternatingSixSchurFiveDicyclicGenerator ^ 10 = 1 := by
  rw [← orderOf_alternatingSixSchurFiveDicyclicGenerator]
  exact pow_orderOf_eq_one _

theorem alternatingSixSchurFiveDicyclicGenerator_pow_five :
    alternatingSixSchurFiveDicyclicGenerator ^ 5 =
      alternatingSixSchurFiveCentral ^ 3 := by
  rw [alternatingSixSchurFiveDicyclicGenerator]
  have hcomm :
      Commute
        (alternatingSixSchurFiveElement ^ 3)
        (alternatingSixSchurFiveCentral ^ 3) :=
    ((alternatingSixSchurFiveCentral_commute
      (alternatingSixSchurFiveElement ^ 3)).pow_left 3).symm
  rw [Commute.mul_pow hcomm]
  have hpPower :
      (alternatingSixSchurFiveElement ^ 3) ^ 5 =
        alternatingSixSchurFiveElement ^ 15 := by
    rw [← pow_mul]
  have hcPower :
      (alternatingSixSchurFiveCentral ^ 3) ^ 5 =
        alternatingSixSchurFiveCentral ^ 15 := by
    rw [← pow_mul]
  calc
    (alternatingSixSchurFiveElement ^ 3) ^ 5 *
          (alternatingSixSchurFiveCentral ^ 3) ^ 5 =
        alternatingSixSchurFiveElement ^ 15 *
          alternatingSixSchurFiveCentral ^ 15 := by
            rw [hpPower, hcPower]
    _ = alternatingSixSchurFiveCentral ^ 15 := by
      rw [show alternatingSixSchurFiveElement ^ 15 = 1 by
        calc
          alternatingSixSchurFiveElement ^ 15 =
              (alternatingSixSchurFiveElement ^ 5) ^ 3 := by group
          _ = 1 := by
            rw [alternatingSixSchurFiveElement_pow_five]
            simp]
      simp
    _ = alternatingSixSchurFiveCentral ^ 3 := by
      calc
        alternatingSixSchurFiveCentral ^ 15 =
            (alternatingSixSchurFiveCentral ^ 6) ^ 2 *
              alternatingSixSchurFiveCentral ^ 3 := by group
        _ = alternatingSixSchurFiveCentral ^ 3 := by
          rw [alternatingSixSchurPresentedK0_pow_six]
          simp

theorem alternatingSixSchurFiveDicyclicGenerator_conj :
    alternatingSixSchurFiveNormalizerElement *
          alternatingSixSchurFiveDicyclicGenerator *
          alternatingSixSchurFiveNormalizerElement⁻¹ =
      alternatingSixSchurFiveDicyclicGenerator⁻¹ := by
  let x := alternatingSixSchurFiveNormalizerElement
  let p := alternatingSixSchurFiveElement
  let c := alternatingSixSchurFiveCentral
  have hp :
      x * p ^ 3 * x⁻¹ = (p ^ 3)⁻¹ := by
    change
      MulAut.conj x (p ^ 3) = (p ^ 3)⁻¹
    rw [map_pow]
    change
      (x * p * x⁻¹) ^ 3 = (p ^ 3)⁻¹
    rw [alternatingSixSchurFiveNormalizerElement_conj]
    dsimp [p]
    group
  have hc :
      x * c ^ 3 * x⁻¹ = c ^ 3 :=
    ((alternatingSixSchurFiveCentral_commute x).pow_left 3).symm.mul_inv_cancel
  change
    x * (p ^ 3 * c ^ 3) * x⁻¹ =
      (p ^ 3 * c ^ 3)⁻¹
  calc
    x * (p ^ 3 * c ^ 3) * x⁻¹ =
        (x * p ^ 3 * x⁻¹) *
          (x * c ^ 3 * x⁻¹) := by group
    _ = (p ^ 3)⁻¹ * c ^ 3 := by rw [hp, hc]
    _ = (p ^ 3 * c ^ 3)⁻¹ := by
      have hcInv : (c ^ 3)⁻¹ = c ^ 3 := by
        rw [inv_eq_iff_mul_eq_one]
        calc
          c ^ 3 * c ^ 3 = c ^ 6 := by group
          _ = 1 := alternatingSixSchurPresentedK0_pow_six
      rw [mul_inv_rev, hcInv]
      exact
        (((alternatingSixSchurFiveCentral_commute
          ((p ^ 3)⁻¹)).pow_left 3).symm.eq)

theorem alternatingSixSchurFiveDicyclicGenerator_mul_normalizer :
    alternatingSixSchurFiveDicyclicGenerator *
          alternatingSixSchurFiveNormalizerElement =
      alternatingSixSchurFiveNormalizerElement *
        alternatingSixSchurFiveDicyclicGenerator⁻¹ := by
  have hinvConj :
      alternatingSixSchurFiveNormalizerElement *
            alternatingSixSchurFiveDicyclicGenerator⁻¹ *
            alternatingSixSchurFiveNormalizerElement⁻¹ =
        alternatingSixSchurFiveDicyclicGenerator := by
    calc
      alternatingSixSchurFiveNormalizerElement *
            alternatingSixSchurFiveDicyclicGenerator⁻¹ *
            alternatingSixSchurFiveNormalizerElement⁻¹ =
          (alternatingSixSchurFiveNormalizerElement *
            alternatingSixSchurFiveDicyclicGenerator *
            alternatingSixSchurFiveNormalizerElement⁻¹)⁻¹ := by group
      _ = alternatingSixSchurFiveDicyclicGenerator := by
        rw [alternatingSixSchurFiveDicyclicGenerator_conj]
        simp
  calc
    alternatingSixSchurFiveDicyclicGenerator *
          alternatingSixSchurFiveNormalizerElement =
        (alternatingSixSchurFiveNormalizerElement *
            alternatingSixSchurFiveDicyclicGenerator⁻¹ *
            alternatingSixSchurFiveNormalizerElement⁻¹) *
          alternatingSixSchurFiveNormalizerElement := by rw [hinvConj]
    _ =
        alternatingSixSchurFiveNormalizerElement *
          alternatingSixSchurFiveDicyclicGenerator⁻¹ := by group

private theorem alternatingSixSchurFiveDicyclicSquareRelation :
    alternatingSixSchurFiveNormalizerElement *
          alternatingSixSchurFiveNormalizerElement =
      QuaternionGroup.zmodPower
        alternatingSixSchurFiveDicyclicGenerator
        alternatingSixSchurFiveDicyclicGenerator_pow_ten
        (5 : ZMod 10) := by
  calc
    alternatingSixSchurFiveNormalizerElement *
          alternatingSixSchurFiveNormalizerElement =
        alternatingSixSchurFiveCentral ^ 3 := by
          simpa [pow_two] using
            alternatingSixSchurFiveNormalizerElement_sq
    _ = alternatingSixSchurFiveDicyclicGenerator ^ 5 :=
      alternatingSixSchurFiveDicyclicGenerator_pow_five.symm
    _ =
        QuaternionGroup.zmodPower
          alternatingSixSchurFiveDicyclicGenerator
          alternatingSixSchurFiveDicyclicGenerator_pow_ten
          (5 : ZMod 10) := by
      simpa using
        (QuaternionGroup.zmodPower_natCast
          alternatingSixSchurFiveDicyclicGenerator
          alternatingSixSchurFiveDicyclicGenerator_pow_ten 5).symm

/-- The explicit dicyclic homomorphism into the presented cover. -/
def quaternionFiveToAlternatingSixSchur :
    QuaternionGroup 5 →*
      AlternatingSixSchurPresentedGroup :=
  QuaternionGroup.lift
    alternatingSixSchurFiveDicyclicGenerator
    alternatingSixSchurFiveNormalizerElement
    alternatingSixSchurFiveDicyclicGenerator_pow_ten
    alternatingSixSchurFiveDicyclicSquareRelation
    (QuaternionGroup.zmodPower_mul_eq_mul_zmodPower_neg
      alternatingSixSchurFiveDicyclicGenerator
      alternatingSixSchurFiveNormalizerElement
      alternatingSixSchurFiveDicyclicGenerator_pow_ten
      alternatingSixSchurFiveDicyclicGenerator_mul_normalizer)

theorem alternatingSixSchurFiveNormalizerElement_not_mem_dicyclicZpowers :
    alternatingSixSchurFiveNormalizerElement ∉
      Subgroup.zpowers alternatingSixSchurFiveDicyclicGenerator := by
  intro hx
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hcomm :
      Commute alternatingSixSchurFiveDicyclicGenerator
        alternatingSixSchurFiveNormalizerElement := by
    rw [← hz]
    exact
      (Commute.refl
        alternatingSixSchurFiveDicyclicGenerator).zpow_right z
  have hinv :
      alternatingSixSchurFiveDicyclicGenerator =
        alternatingSixSchurFiveDicyclicGenerator⁻¹ := by
    apply mul_left_cancel
      (a := alternatingSixSchurFiveNormalizerElement)
    calc
      alternatingSixSchurFiveNormalizerElement *
            alternatingSixSchurFiveDicyclicGenerator =
          alternatingSixSchurFiveDicyclicGenerator *
            alternatingSixSchurFiveNormalizerElement :=
        hcomm.eq.symm
      _ =
          alternatingSixSchurFiveNormalizerElement *
            alternatingSixSchurFiveDicyclicGenerator⁻¹ :=
        alternatingSixSchurFiveDicyclicGenerator_mul_normalizer
  have hsq :
      alternatingSixSchurFiveDicyclicGenerator ^ 2 = 1 := by
    calc
      alternatingSixSchurFiveDicyclicGenerator ^ 2 =
          alternatingSixSchurFiveDicyclicGenerator *
            alternatingSixSchurFiveDicyclicGenerator := by
              rw [pow_two]
      _ =
          alternatingSixSchurFiveDicyclicGenerator *
            alternatingSixSchurFiveDicyclicGenerator⁻¹ := by
              exact congrArg
                (fun y =>
                  alternatingSixSchurFiveDicyclicGenerator * y)
                hinv
      _ = 1 := mul_inv_cancel _
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rw [orderOf_alternatingSixSchurFiveDicyclicGenerator] at hdvd
  norm_num at hdvd

theorem quaternionFiveToAlternatingSixSchur_injective :
    Function.Injective quaternionFiveToAlternatingSixSchur := by
  apply
    QuaternionGroup.lift_injective_of_orderOf_eq
      alternatingSixSchurFiveDicyclicGenerator
      alternatingSixSchurFiveNormalizerElement
      alternatingSixSchurFiveDicyclicGenerator_pow_ten
      alternatingSixSchurFiveDicyclicSquareRelation
      (QuaternionGroup.zmodPower_mul_eq_mul_zmodPower_neg
        alternatingSixSchurFiveDicyclicGenerator
        alternatingSixSchurFiveNormalizerElement
        alternatingSixSchurFiveDicyclicGenerator_pow_ten
        alternatingSixSchurFiveDicyclicGenerator_mul_normalizer)
      orderOf_alternatingSixSchurFiveDicyclicGenerator
      alternatingSixSchurFiveNormalizerElement_not_mem_dicyclicZpowers

end GroupTheory
end McKayConjecture
