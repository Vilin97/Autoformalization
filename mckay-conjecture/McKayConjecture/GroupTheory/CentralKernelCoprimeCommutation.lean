/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Coprime commutation above a central kernel

Suppose two elements commute after applying a homomorphism whose kernel is
central.  Their commutator is then central.  If the two elements have
coprime power exponents, the standard power identities for a central
commutator force that commutator to be trivial.

The final theorem packages the form needed when assembling homomorphic
sections over distinct Sylow factors of a finite abelian quotient: the
images of homomorphisms from finite groups of coprime orders commute
elementwise above any central kernel.
-/

namespace McKayConjecture
namespace GroupTheory

open scoped commutatorElement

variable {E : Type*} [Group E]

/-- A central commutator is multiplicative in powers of its first entry. -/
theorem commutatorElement_pow_left_of_mem_center
    {x y : E}
    (hcentral : ⁅x, y⁆ ∈ Subgroup.center E)
    (n : ℕ) :
    ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, commutatorElement_mul_left_eq_conj_mul, ih]
      rw [(hcentral.comm (x ^ n)).symm.eq]
      simp only [mul_assoc, mul_inv_cancel, mul_one, pow_succ]
      exact (Commute.self_pow _ _).eq

/-- A central commutator is multiplicative in powers of its second entry. -/
theorem commutatorElement_pow_right_of_mem_center
    {x y : E}
    (hcentral : ⁅x, y⁆ ∈ Subgroup.center E)
    (n : ℕ) :
    ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, commutatorElement_mul_right_eq_mul_conj, ih]
      rw [mul_assoc (⁅x, y⁆ ^ n) (y ^ n) ⁅x, y⁆]
      rw [(hcentral.comm (y ^ n)).symm.eq]
      simp only [mul_assoc, mul_inv_cancel, mul_one, pow_succ]

/-- If a central commutator has two coprime annihilating exponents, then it
is trivial and the original elements commute. -/
theorem commute_of_commutator_mem_center_of_coprime_powers
    {x y : E} {m n : ℕ}
    (hcentral : ⁅x, y⁆ ∈ Subgroup.center E)
    (hx : x ^ m = 1)
    (hy : y ^ n = 1)
    (hcoprime : m.Coprime n) :
    Commute x y := by
  rw [← commutatorElement_eq_one_iff_commute]
  apply (pow_eq_one_iff_of_coprime hcoprime).mp
  constructor
  · rw [
      ← commutatorElement_pow_left_of_mem_center hcentral m,
      hx,
      commutatorElement_one_left
    ]
  · rw [
      ← commutatorElement_pow_right_of_mem_center hcentral n,
      hy,
      commutatorElement_one_right
    ]

variable {B P Q : Type*}
variable [CommGroup B] [Group P] [Group Q]

/-- Images of groups with coprime `Nat.card`s commute elementwise above a
central kernel whenever their images commute in the quotient.  In the
intended application the domain groups are finite Sylow factors.  The
quotient-side commutation is automatic here because the target is
commutative. -/
theorem MonoidHom.commute_apply_of_coprime_card_of_ker_le_center
    (projection : E →* B)
    (hkernel : projection.ker ≤ Subgroup.center E)
    (f : P →* E)
    (g : Q →* E)
    (hcoprime : (Nat.card P).Coprime (Nat.card Q))
    (x : P)
    (y : Q) :
    Commute (f x) (g y) := by
  refine
    commute_of_commutator_mem_center_of_coprime_powers
      (m := Nat.card P)
      (n := Nat.card Q)
      (hkernel ?_) ?_ ?_ hcoprime
  · change projection ⁅f x, g y⁆ = 1
    rw [map_commutatorElement]
    exact
      commutatorElement_eq_one_iff_commute.mpr
        (Commute.all _ _)
  · rw [← map_pow, pow_card_eq_one', map_one]
  · rw [← map_pow, pow_card_eq_one', map_one]

end GroupTheory
end McKayConjecture
