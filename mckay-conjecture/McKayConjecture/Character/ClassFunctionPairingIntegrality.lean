/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.NumberTheory.Niven
import McKayConjecture.Character.ClassFunctionPairing

/-!
# Algebraic integrality around the normalized class-function pairing

The numerator of the normalized pairing is an algebraic integer whenever
both class functions have algebraic-integer values.  This file also
packages the standard fact that a rational algebraic integer is an
ordinary integer.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

universe u

variable {G : Type u} [Group G] [Finite G]

/-- If two class functions have algebraic-integer values, then the
group order times their normalized pairing is an algebraic integer. -/
theorem isIntegral_card_mul_normalizedPairing
    (f k : ClassFunction G)
    (hf : ∀ g : G, IsIntegral ℤ (f g))
    (hk : ∀ g : G, IsIntegral ℤ (k g)) :
    IsIntegral ℤ
      ((Nat.card G : ℂ) * normalizedPairing f k) := by
  letI : Fintype G := Fintype.ofFinite G
  have hcard : (Nat.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [normalizedPairing, LinearMap.mk₂_apply]
  rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  exact IsIntegral.sum _ fun g _ ↦
    (hf g).mul (hk g⁻¹)

/-- A rational complex algebraic integer is the cast of an integer.
The equality orientation matches Fourier-coefficient applications. -/
theorem exists_int_eq_of_isIntegral_of_eq_rat
    {z : ℂ} (hz : IsIntegral ℤ z)
    (hrat : ∃ q : ℚ, z = (q : ℂ)) :
    ∃ n : ℤ, z = (n : ℂ) :=
  (IsIntegral.exists_int_iff_exists_rat hz).mp hrat

end ClassFunction
end McKayConjecture
