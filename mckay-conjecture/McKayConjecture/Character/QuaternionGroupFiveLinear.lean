/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Linear
import McKayConjecture.GroupTheory.QuaternionGroupHom

/-!
# Linear characters of the order-twenty dicyclic group

For odd dicyclic parameter `5`, the abelianization is cyclic of order four.
This file constructs the four homomorphisms by sending the reflection
generator to each fourth root of unity and the cyclic generator to its
square.
-/

noncomputable section

namespace McKayConjecture
namespace QuaternionGroupFive

/-- A homomorphism from `QuaternionGroup 5` determined by a fourth root
`s`, with the reflection generator sent to `s`. -/
def linearHomOfFourthRoot
    (s : ℂˣ) (hs : s ^ 4 = 1) :
    QuaternionGroup 5 →* ℂˣ := by
  have hA : (s ^ 2) ^ (2 * 5) = 1 := by
    rw [← pow_mul]
    rw [show 2 * (2 * 5) = 4 * 5 by norm_num,
      pow_mul, hs, one_pow]
  have hAself : (s ^ 2)⁻¹ = s ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    calc
      s ^ 2 * s ^ 2 = s ^ 4 := by group
      _ = 1 := hs
  have hXsq :
      s * s =
        QuaternionGroup.zmodPower (s ^ 2) hA 5 := by
    rw [show (5 : ZMod 10) =
      ((5 : ℕ) : ZMod 10) by norm_num]
    rw [QuaternionGroup.zmodPower_natCast]
    calc
      s * s = s ^ 2 := by rw [pow_two]
      _ = s ^ 10 := by
        rw [show s ^ 10 = s ^ 2 * (s ^ 4) ^ 2 by group,
          hs]
        simp
      _ = (s ^ 2) ^ 5 := by
        rw [← pow_mul]
  have hAX : s ^ 2 * s = s * (s ^ 2)⁻¹ := by
    rw [hAself]
    exact mul_comm _ _
  exact
    QuaternionGroup.lift
      (s ^ 2) s hA hXsq
      (QuaternionGroup.zmodPower_mul_eq_mul_zmodPower_neg
        (s ^ 2) s hA hAX)

/-- The complex unit `i`. -/
def imaginaryUnit : ℂˣ :=
  Units.mk0 Complex.I Complex.I_ne_zero

theorem imaginaryUnit_pow_four :
    imaginaryUnit ^ 4 = 1 := by
  apply Units.ext
  norm_num [imaginaryUnit, pow_succ, Complex.I_mul_I]

/-- The four fourth roots `1, i, -1, -i`, indexed cyclically. -/
def fourthRootParameter (j : Fin 4) : ℂˣ :=
  imaginaryUnit ^ j.val

theorem fourthRootParameter_pow_four (j : Fin 4) :
    fourthRootParameter j ^ 4 = 1 := by
  rw [fourthRootParameter, ← pow_mul]
  rw [show j.val * 4 = 4 * j.val by omega,
    pow_mul, imaginaryUnit_pow_four, one_pow]

theorem fourthRootParameter_injective :
    Function.Injective fourthRootParameter := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals
    first
    | rfl
    | apply_fun (fun u : ℂˣ => (u : ℂ)) at h
      norm_num [fourthRootParameter, imaginaryUnit,
        pow_succ, Complex.I_mul_I, Complex.ext_iff] at h

/-- The four multiplicative homomorphisms to `ℂˣ`. -/
def linearHom (j : Fin 4) :
    QuaternionGroup 5 →* ℂˣ :=
  linearHomOfFourthRoot
    (fourthRootParameter j)
    (fourthRootParameter_pow_four j)

@[simp]
theorem linearHom_apply_reflectionGenerator (j : Fin 4) :
    linearHom j (QuaternionGroup.xa 0) =
      fourthRootParameter j := by
  simp [linearHom, linearHomOfFourthRoot]

theorem linearHom_injective :
    Function.Injective linearHom := by
  intro i j h
  apply fourthRootParameter_injective
  rw [← linearHom_apply_reflectionGenerator i,
    ← linearHom_apply_reflectionGenerator j, h]

/-- The four resulting irreducible linear characters. -/
def linearCharacter (j : Fin 4) :
    IrreducibleCharacter (QuaternionGroup 5) :=
  IrreducibleCharacter.linear (linearHom j)

@[simp]
theorem linearCharacter_degree (j : Fin 4) :
    (linearCharacter j).degree = 1 :=
  IrreducibleCharacter.linear_degree _

theorem linearCharacter_injective :
    Function.Injective linearCharacter :=
  IrreducibleCharacter.linear_injective.comp
    linearHom_injective

end QuaternionGroupFive
end McKayConjecture
