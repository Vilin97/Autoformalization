/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.GroupTheory.OrderOfElement

/-!
# The `p`-part and `p`-regular part of a finite-order element

For a prime `p`, every element of a finite group is a product of two
commuting powers of itself: a `p`-element and a `p`-regular element.  This
file proves that elementary order-theoretic decomposition directly from the
Chinese remainder theorem.

This is the element-level input used when one studies character values on
`p`-elementary subgroups.  It does not use modular character theory.
-/

namespace McKayConjecture

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- An element is a `p`-element when some `p`-power annihilates it.  For
prime `p` and finite-order elements this is equivalent to having
prime-power order. -/
def IsPElement (p : ℕ) (g : G) : Prop :=
  ∃ k : ℕ, g ^ (p ^ k) = 1

/-- An element is `p`-regular when its order is coprime to `p`. -/
def IsPRegular (p : ℕ) (g : G) : Prop :=
  p.Coprime (orderOf g)

namespace IsPElement

/-- The identity is a `p`-element. -/
theorem one (p : ℕ) : IsPElement p (1 : G) :=
  ⟨0, by simp⟩

/-- Homomorphisms preserve `p`-elements. -/
theorem map (p : ℕ) {g : G} (hg : IsPElement p g)
    (φ : G →* H) :
    IsPElement p (φ g) := by
  obtain ⟨k, hk⟩ := hg
  refine ⟨k, ?_⟩
  rw [← map_pow, hk, map_one]

/-- The inverse of a `p`-element is a `p`-element. -/
theorem inv (p : ℕ) {g : G} (hg : IsPElement p g) :
    IsPElement p g⁻¹ := by
  obtain ⟨k, hk⟩ := hg
  refine ⟨k, ?_⟩
  rw [inv_pow, hk, inv_one]

end IsPElement

namespace IsPRegular

/-- The identity is `p`-regular. -/
theorem one (p : ℕ) : IsPRegular p (1 : G) := by
  simp [IsPRegular]

/-- Homomorphisms preserve finite-order `p`-regular elements. -/
theorem map [Finite G]
    (p : ℕ) {g : G} (hg : IsPRegular p g)
    (φ : G →* H) :
    IsPRegular p (φ g) := by
  exact
    Nat.Coprime.of_dvd_right
      (orderOf_map_dvd φ g) hg

/-- Inversion preserves `p`-regularity. -/
theorem inv (p : ℕ) {g : G} (hg : IsPRegular p g) :
    IsPRegular p g⁻¹ := by
  simpa only [IsPRegular, orderOf_inv] using hg

end IsPRegular

/-- A commuting `p`-part/`p`-regular-part factorization of an element. -/
structure PRegularDecomposition (p : ℕ) (g : G) where
  /-- The factor killed by a power of `p`. -/
  pPart : G
  /-- The factor whose order is prime to `p`. -/
  regularPart : G
  /-- Both factors are powers of the original element. -/
  pPart_mem_zpowers : pPart ∈ Subgroup.zpowers g
  /-- Both factors are powers of the original element. -/
  regularPart_mem_zpowers : regularPart ∈ Subgroup.zpowers g
  /-- The two factors commute. -/
  commute : Commute pPart regularPart
  /-- Their product is the original element. -/
  mul_eq : pPart * regularPart = g
  /-- The first factor is a `p`-element. -/
  isPElement : IsPElement p pPart
  /-- The second factor is `p`-regular. -/
  isPRegular : IsPRegular p regularPart

namespace PRegularDecomposition

variable [Finite G]

/-- The `p`-power part and prime-to-`p` part of the order are coprime. -/
theorem coprime_orderProjection_orderComplement
    (p : ℕ) [Fact p.Prime] (g : G) :
    (ordProj[p] (orderOf g)).Coprime
      (ordCompl[p] (orderOf g)) := by
  exact
    (Nat.coprime_ordCompl (n := orderOf g)
      (Fact.out : p.Prime) (orderOf_pos g).ne').pow_left
      (Nat.factorization (orderOf g) p)

/-- Every element of a finite group admits a commuting `p`-part and
`p`-regular-part decomposition.  Both factors are powers of the element. -/
  theorem exists_decomposition
    (p : ℕ) [Fact p.Prime] (g : G) :
    Nonempty (PRegularDecomposition p g) := by
  let q : ℕ := ordProj[p] (orderOf g)
  let m : ℕ := ordCompl[p] (orderOf g)
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hqm : q * m = orderOf g := by
    exact Nat.ordProj_mul_ordCompl_eq_self (orderOf g) p
  have hcop : q.Coprime m := by
    exact coprime_orderProjection_orderComplement p g
  let ep : ℕ := Nat.chineseRemainder hcop 1 0
  let er : ℕ := Nat.chineseRemainder hcop 0 1
  have hepq : ep ≡ 1 [MOD q] :=
    (Nat.chineseRemainder hcop 1 0).prop.1
  have hepm : ep ≡ 0 [MOD m] :=
    (Nat.chineseRemainder hcop 1 0).prop.2
  have herq : er ≡ 0 [MOD q] :=
    (Nat.chineseRemainder hcop 0 1).prop.1
  have herm : er ≡ 1 [MOD m] :=
    (Nat.chineseRemainder hcop 0 1).prop.2
  have hsumq : ep + er ≡ 1 [MOD q] := by
    simpa using hepq.add herq
  have hsumm : ep + er ≡ 1 [MOD m] := by
    simpa using hepm.add herm
  have hsumn : ep + er ≡ 1 [MOD orderOf g] := by
    rw [← hqm]
    exact
      (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
        ⟨hsumq, hsumm⟩
  have hpPow : (g ^ ep) ^ q = 1 := by
    rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one]
    obtain ⟨t, ht⟩ := Nat.modEq_zero_iff_dvd.mp hepm
    rw [ht, ← hqm]
    refine ⟨t, ?_⟩
    ac_rfl
  have hrPow : (g ^ er) ^ m = 1 := by
    rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one]
    obtain ⟨t, ht⟩ := Nat.modEq_zero_iff_dvd.mp herq
    rw [ht, ← hqm]
    refine ⟨t, ?_⟩
    ac_rfl
  have hregularOrder : orderOf (g ^ er) ∣ m :=
    orderOf_dvd_of_pow_eq_one hrPow
  refine ⟨{
    pPart := g ^ ep
    regularPart := g ^ er
    pPart_mem_zpowers :=
      (Subgroup.zpowers g).pow_mem
        (Subgroup.mem_zpowers g) ep
    regularPart_mem_zpowers :=
      (Subgroup.zpowers g).pow_mem
        (Subgroup.mem_zpowers g) er
    commute := (Commute.refl g).pow_pow ep er
    mul_eq := ?_
    isPElement := ?_
    isPRegular := ?_ }⟩
  · rw [← pow_add]
    exact (pow_eq_pow_iff_modEq.mpr hsumn).trans (pow_one g)
  · refine ⟨Nat.factorization (orderOf g) p, ?_⟩
    exact hpPow
  · exact
      Nat.Coprime.of_dvd_right hregularOrder
        (Nat.coprime_ordCompl (n := orderOf g)
          (Fact.out : p.Prime) hn)

/-- A chosen `p`-regular decomposition.  Its public properties are the
fields of `PRegularDecomposition`; downstream arguments need not depend on
the particular Chinese-remainder exponents used in its construction. -/
noncomputable def chosen
    (p : ℕ) [Fact p.Prime] (g : G) :
    PRegularDecomposition p g :=
  Classical.choice (exists_decomposition p g)

end PRegularDecomposition
end McKayConjecture
