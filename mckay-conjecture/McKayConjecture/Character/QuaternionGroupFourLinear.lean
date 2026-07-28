/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Linear
import McKayConjecture.GroupTheory.QuaternionGroupHom

/-!
# Linear characters of the generalized quaternion group of order sixteen

The abelianization of `QuaternionGroup 4` is `C₂ × C₂`.  The four linear
characters below independently choose the signs of the cyclic generator
`a` and reflection generator `x`.
-/

noncomputable section

namespace McKayConjecture
namespace QuaternionGroupFour

/-- The two signs `1` and `-1`, regarded as complex units. -/
def signParameter (j : Fin 2) : ℂˣ :=
  (-1 : ℂˣ) ^ j.val

@[simp]
theorem signParameter_sq (j : Fin 2) :
    signParameter j ^ 2 = 1 := by
  fin_cases j <;> norm_num [signParameter]

theorem signParameter_injective :
    Function.Injective signParameter := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals
    first
    | rfl
    | apply_fun (fun u : ℂˣ => (u : ℂ)) at h
      norm_num [signParameter] at h

/-- A linear homomorphism determined by independent signs for `a` and
`x`. -/
def linearHomOfSigns
    (s t : ℂˣ)
    (hs : s ^ 2 = 1)
    (ht : t ^ 2 = 1) :
    QuaternionGroup 4 →* ℂˣ := by
  have hA : s ^ (2 * 4) = 1 := by
    calc
      s ^ (2 * 4) = (s ^ 2) ^ 4 := by
        rw [← pow_mul]
      _ = 1 := by rw [hs, one_pow]
  have hself : s⁻¹ = s := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using hs
  have hXsq :
      t * t =
        QuaternionGroup.zmodPower s hA 4 := by
    rw [show (4 : ZMod 8) =
      ((4 : ℕ) : ZMod 8) by norm_num]
    rw [QuaternionGroup.zmodPower_natCast]
    calc
      t * t = 1 := by
        simpa only [pow_two] using ht
      _ = s ^ 4 := by
        rw [show s ^ 4 = (s ^ 2) ^ 2 by group, hs]
        simp
  have hAX : s * t = t * s⁻¹ := by
    rw [hself]
    exact mul_comm _ _
  exact
    QuaternionGroup.lift
      s t hA hXsq
      (QuaternionGroup.zmodPower_mul_eq_mul_zmodPower_neg
        s t hA hAX)

/-- The four linear-row indices. -/
abbrev LinearIndex := Fin 2 × Fin 2

/-- The four homomorphisms `QuaternionGroup 4 →* ℂˣ`. -/
def linearHom (r : LinearIndex) :
    QuaternionGroup 4 →* ℂˣ :=
  linearHomOfSigns
    (signParameter r.1)
    (signParameter r.2)
    (signParameter_sq r.1)
    (signParameter_sq r.2)

@[simp]
theorem linearHom_apply_a_natCast
    (r : LinearIndex) (m : ℕ) :
    linearHom r
        (QuaternionGroup.a (m : ZMod 8)) =
      signParameter r.1 ^ m := by
  rw [linearHom, linearHomOfSigns,
    QuaternionGroup.lift_apply_a,
    QuaternionGroup.zmodPower_natCast]

@[simp]
theorem linearHom_apply_xa_natCast
    (r : LinearIndex) (m : ℕ) :
    linearHom r
        (QuaternionGroup.xa (m : ZMod 8)) =
      signParameter r.2 * signParameter r.1 ^ m := by
  rw [linearHom, linearHomOfSigns,
    QuaternionGroup.lift_apply_xa,
    QuaternionGroup.zmodPower_natCast]

@[simp]
theorem linearHom_apply_cyclicGenerator
    (r : LinearIndex) :
    linearHom r (QuaternionGroup.a (1 : ZMod 8)) =
      signParameter r.1 := by
  simpa using linearHom_apply_a_natCast r 1

@[simp]
theorem linearHom_apply_reflectionGenerator
    (r : LinearIndex) :
    linearHom r (QuaternionGroup.xa (0 : ZMod 8)) =
      signParameter r.2 := by
  simpa using linearHom_apply_xa_natCast r 0

theorem linearHom_injective :
    Function.Injective linearHom := by
  intro r s hrs
  apply Prod.ext
  · apply signParameter_injective
    rw [← linearHom_apply_cyclicGenerator r,
      ← linearHom_apply_cyclicGenerator s, hrs]
  · apply signParameter_injective
    rw [← linearHom_apply_reflectionGenerator r,
      ← linearHom_apply_reflectionGenerator s, hrs]

/-- The four irreducible linear characters. -/
def linearCharacter (r : LinearIndex) :
    IrreducibleCharacter (QuaternionGroup 4) :=
  IrreducibleCharacter.linear (linearHom r)

@[simp]
theorem linearCharacter_degree (r : LinearIndex) :
    (linearCharacter r).degree = 1 :=
  IrreducibleCharacter.linear_degree _

theorem linearCharacter_injective :
    Function.Injective linearCharacter :=
  IrreducibleCharacter.linear_injective.comp
    linearHom_injective

@[simp]
theorem linearCharacter_values_a_natCast
    (r : LinearIndex) (m : ℕ) :
    (linearCharacter r).values
        (QuaternionGroup.a (m : ZMod 8)) =
      (signParameter r.1 ^ m : ℂˣ) := by
  rw [linearCharacter, IrreducibleCharacter.linear_values,
    linearHom_apply_a_natCast]

@[simp]
theorem linearCharacter_values_xa_natCast
    (r : LinearIndex) (m : ℕ) :
    (linearCharacter r).values
        (QuaternionGroup.xa (m : ZMod 8)) =
      (signParameter r.2 * signParameter r.1 ^ m : ℂˣ) := by
  rw [linearCharacter, IrreducibleCharacter.linear_values,
    linearHom_apply_xa_natCast]

end QuaternionGroupFour
end McKayConjecture
