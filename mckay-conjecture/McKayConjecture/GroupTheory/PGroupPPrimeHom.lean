/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.PPrimeCore
import Mathlib.GroupTheory.PGroup

/-!
# Homomorphisms from `p'`-groups to `p`-groups

A homomorphism from a finite `p'`-group to a `p`-group is trivial.  The
pointwise proof compares the order of an image element with both a power
of `p` and the order of the source group.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

variable {A D : Type} [Group A] [Finite A] [Group D]
variable {p : ℕ} [Fact p.Prime]

omit [Finite A] [Fact p.Prime] in
/-- Every homomorphism from a finite `p'`-group to a `p`-group is the
trivial homomorphism.  The target need not be finite. -/
theorem MonoidHom.eq_one_of_isPPrimeGroup_of_isPGroup
    (f : A →* D)
    (hA : IsPPrimeGroup p A)
    (hD : IsPGroup p D) :
    f = 1 := by
  ext a
  obtain ⟨k, hk⟩ := hD (f a)
  have hpow : orderOf (f a) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one hk
  have hcard : orderOf (f a) ∣ Nat.card A :=
    (orderOf_map_dvd f a).trans
      (orderOf_dvd_natCard a)
  have hone : orderOf (f a) = 1 :=
    Nat.eq_one_of_dvd_coprimes
      (hA.pow_left k) hpow hcard
  exact orderOf_eq_one_iff.mp hone

omit [Finite A] [Fact p.Prime] in
/-- Pointwise form of triviality for a homomorphism from a finite
`p'`-group to a `p`-group. -/
theorem MonoidHom.apply_eq_one_of_isPPrimeGroup_of_isPGroup
    (f : A →* D)
    (hA : IsPPrimeGroup p A)
    (hD : IsPGroup p D)
    (a : A) :
    f a = 1 := by
  rw [MonoidHom.eq_one_of_isPPrimeGroup_of_isPGroup
    f hA hD]
  rfl

end GroupTheory
end McKayConjecture
