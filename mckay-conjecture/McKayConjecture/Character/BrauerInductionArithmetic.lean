/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.DFinsupp.BigOperators

/-!
# Arithmetic separation used in Brauer induction

The standard proof of Brauer induction ends with a lattice argument.  An
element of a finitely generated abelian group which is divisible by every
power of every prime must vanish.  Consequently, if two sublattices agree
modulo every prime power, then they agree.

This file proves the elementwise form needed by the character-ring
argument.  It is independent of representation theory and uses the
structure theorem for finitely generated abelian groups.
-/

noncomputable section

namespace McKayConjecture

/-- An element is universally prime-power divisible when it is divisible
by `p ^ n` for every prime `p` and every exponent `n`. -/
def IsUniversallyPrimePowerDivisible
    {A : Type*} [AddCommGroup A] (x : A) : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ n : ℕ,
    ∃ y : A, p ^ n • y = x

/-- An integer divisible by every power of one fixed prime is zero. -/
theorem int_eq_zero_of_prime_pow_dvd_all
    (p : ℕ) (hp : p.Prime) (z : ℤ)
    (hz : ∀ n : ℕ, (p : ℤ) ^ n ∣ z) :
    z = 0 := by
  by_contra hne
  letI : Fact p.Prime := ⟨hp⟩
  have hdiv :=
    (padicValInt_dvd_iff
      (p := p) (padicValInt p z + 1) z).mp
      (hz (padicValInt p z + 1))
  exact
    (Nat.not_succ_le_self (padicValInt p z))
      (hdiv.resolve_left hne)

/-- In a finitely generated abelian group, universal prime-power
divisibility forces an element to vanish. -/
theorem eq_zero_of_isUniversallyPrimePowerDivisible
    {A : Type*} [AddCommGroup A] [AddGroup.FG A]
    {x : A}
    (hx : IsUniversallyPrimePowerDivisible x) :
    x = 0 := by
  classical
  obtain ⟨r, ι, hι, p, hp, e, ⟨equiv⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod A
  apply equiv.injective
  rw [map_zero]
  apply Prod.ext
  · apply Finsupp.ext
    intro j
    apply int_eq_zero_of_prime_pow_dvd_all 2 Nat.prime_two
    intro n
    obtain ⟨y, hy⟩ := hx 2 Nat.prime_two n
    refine ⟨(equiv y).1 j, ?_⟩
    have hmap :=
      congrArg (fun z => z.1 j)
        (congrArg equiv hy)
    simpa [nsmul_eq_mul] using hmap.symm
  · apply DFinsupp.ext
    intro i
    obtain ⟨y, hy⟩ := hx (p i) (hp i) (e i)
    let coord :
        A →+ ZMod (p i ^ e i) :=
      (DFinsupp.evalAddMonoidHom i).comp
        ((AddMonoidHom.snd
          (Fin r →₀ ℤ)
          (DirectSum ι fun i => ZMod (p i ^ e i))).comp
            equiv.toAddMonoidHom)
    have hmap :
        p i ^ e i • coord y = coord x := by
      simpa only [map_nsmul] using congrArg coord hy
    calc
      (equiv x).2 i = coord x :=
        rfl
      _ = p i ^ e i • coord y :=
        hmap.symm
      _ = 0 := by
        simp [nsmul_eq_mul]

/-- Elementwise prime-power congruence separation for finitely generated
abelian groups.

The hypothesis says that every `x ∈ B` is congruent modulo `p ^ n` to an
element of `A`, for every prime power.  Then `B ≤ A`. -/
theorem addSubgroup_le_of_congruent_mod_prime_powers
    {L : Type*} [AddCommGroup L] [AddGroup.FG L]
    (A B : AddSubgroup L)
    (hcongr :
      ∀ (p : ℕ), p.Prime → ∀ n : ℕ,
        ∀ x ∈ B,
          ∃ a ∈ A, ∃ y : L,
            x = a + p ^ n • y) :
    B ≤ A := by
  intro x hxB
  let q : L →+ L ⧸ A :=
    QuotientAddGroup.mk' A
  have hdiv :
      IsUniversallyPrimePowerDivisible (q x) := by
    intro p hp n
    obtain ⟨a, ha, y, hxy⟩ :=
      hcongr p hp n x hxB
    refine ⟨q y, ?_⟩
    rw [hxy, map_add, map_nsmul]
    have hqa : q a = 0 :=
      (QuotientAddGroup.eq_zero_iff a).mpr ha
    rw [hqa, zero_add]
  have hzero :
      q x = 0 :=
    eq_zero_of_isUniversallyPrimePowerDivisible hdiv
  exact (QuotientAddGroup.eq_zero_iff x).mp hzero

/-- If `A ≤ B` and every element of `B` is congruent to `A` modulo every
prime power, then the two subgroups are equal. -/
theorem addSubgroup_eq_of_congruent_mod_prime_powers
    {L : Type*} [AddCommGroup L] [AddGroup.FG L]
    (A B : AddSubgroup L)
    (hAB : A ≤ B)
    (hcongr :
      ∀ (p : ℕ), p.Prime → ∀ n : ℕ,
        ∀ x ∈ B,
          ∃ a ∈ A, ∃ y : L,
            x = a + p ^ n • y) :
    A = B :=
  le_antisymm hAB
    (addSubgroup_le_of_congruent_mod_prime_powers
      A B hcongr)

end McKayConjecture
