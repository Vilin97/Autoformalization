/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic

/-!
# Square roots among complex units

A pair of nonzero complex numbers with the same square differ by a sign.
The units formulation is convenient when normalizing central character
scalars.
-/

namespace McKayConjecture

/-- Complex units with equal squares are equal or differ by the unit `-1`. -/
theorem complexUnit_eq_or_eq_neg_mul_of_sq_eq
    {a b : ℂˣ} (h : a ^ 2 = b ^ 2) :
    a = b ∨ a = -1 * b := by
  have hv : (a : ℂ) ^ 2 = (b : ℂ) ^ 2 :=
    congrArg Units.val h
  have hfactor :
      ((a : ℂ) - (b : ℂ)) * ((a : ℂ) + (b : ℂ)) = 0 := by
    calc
      ((a : ℂ) - (b : ℂ)) * ((a : ℂ) + (b : ℂ)) =
          (a : ℂ) ^ 2 - (b : ℂ) ^ 2 := by ring
      _ = 0 := by rw [hv]; ring
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · left
    apply Units.ext
    linear_combination hminus
  · right
    apply Units.ext
    change (a : ℂ) = (-1 : ℂ) * (b : ℂ)
    linear_combination hplus

end McKayConjecture
