/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import McKayConjecture.GroupTheory.MinimalNormal

/-!
# Abelian minimal normal subgroups

A finite abelian minimal normal subgroup is elementary abelian.  The proofs
here deliberately separate the two ingredients used in reduction arguments:

* a prime divisor of its order makes the entire subgroup a `p`-group; and
* the characteristic subgroup of elements killed by the `p`th-power map is
  the entire minimal normal subgroup.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

open scoped IsMulCommutative

variable {G : Type u} [Group G]

/-- The subgroup of an abelian group consisting of elements whose `p`th
power is one. -/
def primeExponentKernel (A : Type*) [CommGroup A] (p : ℕ) :
    Subgroup A :=
  (powMonoidHom p).ker

namespace primeExponentKernel

variable {A : Type*} [CommGroup A] {p : ℕ}

@[simp]
theorem mem_iff (a : A) :
    a ∈ primeExponentKernel A p ↔ a ^ p = 1 :=
  MonoidHom.mem_ker

/-- The kernel of the `p`th-power map is characteristic. -/
instance characteristic :
    (primeExponentKernel A p).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_le]
  intro e a ha
  change (e a) ^ p = 1 at ha
  change a ^ p = 1
  apply e.injective
  simpa using ha

end primeExponentKernel

namespace IsMinimalNormal

variable {N : Subgroup G}

/-- If a prime `p` divides the order of a finite abelian minimal normal
subgroup, then that subgroup is a `p`-group. -/
theorem isPGroup_of_prime_dvd_natCard
    [Finite G] [IsMulCommutative N]
    (hN : IsMinimalNormal N)
    {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Nat.card N) :
    IsPGroup p N := by
  letI : N.Normal := hN.normal
  letI : CommGroup N := inferInstance
  let P : Sylow p N := Classical.choice inferInstance
  have hPnormal : (P : Subgroup N).Normal := inferInstance
  letI : (P : Subgroup N).Characteristic :=
    Sylow.characteristic_of_normal P hPnormal
  have hmapNormal :
      ((P : Subgroup N).map N.subtype).Normal :=
    inferInstance
  have hmapNe :
      (P : Subgroup N).map N.subtype ≠ ⊥ := by
    intro hbot
    exact P.ne_bot_of_dvd_card hp
      (((P : Subgroup N).map_eq_bot_iff_of_injective
        (f := N.subtype) Subtype.coe_injective).mp hbot)
  have hmapLe :
      (P : Subgroup N).map N.subtype ≤ N := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.property
  have hmapEq :
      (P : Subgroup N).map N.subtype = N :=
    hN.eq_of_normal_le hmapNormal hmapNe hmapLe
  rw [← hmapEq]
  exact P.isPGroup'.map N.subtype

/-- A finite abelian minimal normal `p`-subgroup has exponent `p`. -/
theorem pow_prime_eq_one
    [Finite G] [IsMulCommutative N]
    (hN : IsMinimalNormal N)
    {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Nat.card N) :
    ∀ x : N, x ^ p = 1 := by
  letI : N.Normal := hN.normal
  letI : CommGroup N := inferInstance
  letI : Nontrivial N :=
    N.nontrivial_iff_ne_bot.mpr hN.ne_bot
  have hNp : IsPGroup p N :=
    hN.isPGroup_of_prime_dvd_natCard hp
  obtain ⟨x, hx⟩ := exists_ne (1 : N)
  have hpOrder : p ∣ orderOf x :=
    hNp.dvd_orderOf hx
  have hpCard : p ∣ Nat.card N :=
    hpOrder.trans (orderOf_dvd_natCard x)
  obtain ⟨z, hzOrder⟩ :=
    exists_prime_orderOf_dvd_card' p hpCard
  have hzPow : z ^ p = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hzOrder]
  have hzNe : z ≠ 1 := by
    intro hz
    have : orderOf z = 1 := orderOf_eq_one_iff.mpr hz
    exact (Fact.out : p.Prime).ne_one (hzOrder ▸ this)
  let K : Subgroup N := primeExponentKernel N p
  letI : K.Characteristic :=
    primeExponentKernel.characteristic
  have hKnormal : (K.map N.subtype).Normal :=
    inferInstance
  have hKne : K ≠ ⊥ := by
    intro hbot
    have hzMem : z ∈ K := by
      exact primeExponentKernel.mem_iff z |>.mpr hzPow
    have : z = 1 := by
      simpa [hbot] using hzMem
    exact hzNe this
  have hKmapNe : K.map N.subtype ≠ ⊥ := by
    intro hbot
    exact hKne
      ((K.map_eq_bot_iff_of_injective
        (f := N.subtype) Subtype.coe_injective).mp hbot)
  have hKmapLe : K.map N.subtype ≤ N := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := hg
    exact y.property
  have hKmapEq : K.map N.subtype = N :=
    hN.eq_of_normal_le hKnormal hKmapNe hKmapLe
  intro y
  have hyMap : (y : G) ∈ K.map N.subtype := by
    rw [hKmapEq]
    exact y.property
  obtain ⟨z, hzK, hzEq⟩ := hyMap
  have hzy : z = y :=
    Subtype.ext hzEq
  subst z
  exact primeExponentKernel.mem_iff y |>.mp hzK

/-- Every finite abelian minimal normal subgroup has prime exponent.  This is
the elementary-abelian half of the standard minimal-normal dichotomy. -/
theorem exists_prime_pow_eq_one
    [Finite G] [IsMulCommutative N]
    (hN : IsMinimalNormal N) :
    ∃ p : ℕ, p.Prime ∧ ∀ x : N, x ^ p = 1 := by
  have hcardNe : Nat.card N ≠ 1 :=
    ne_of_gt (N.one_lt_card_iff_ne_bot.mpr hN.ne_bot)
  obtain ⟨p, hpPrime, hpCard⟩ :=
    Nat.exists_prime_and_dvd hcardNe
  letI : Fact p.Prime := ⟨hpPrime⟩
  exact ⟨p, hpPrime, hN.pow_prime_eq_one hpCard⟩

end IsMinimalNormal

end GroupTheory
end McKayConjecture
