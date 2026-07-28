/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PRegularDecomposition
import McKayConjecture.GroupTheory.CoprimeCommutingFactors

/-!
# Uniqueness and functoriality of the `p`-regular decomposition

The commuting `p`-part and `p`-regular part of a finite-order element are
unique.  Consequently the decomposition chosen in
`PRegularDecomposition.chosen` commutes with homomorphisms between finite
groups, and in particular with conjugation.

These facts let one describe supports of class functions by the conjugacy
class of the `p`-regular part without depending on the Chinese-remainder
exponents used to construct that part.
-/

namespace McKayConjecture

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]

namespace IsPElement

/-- A product of commuting `p`-elements is a `p`-element. -/
theorem mul_of_commute
    (p : ℕ) {a b : G}
    (ha : IsPElement p a) (hb : IsPElement p b)
    (hab : Commute a b) :
    IsPElement p (a * b) := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨l, hl⟩ := hb
  refine ⟨k + l, ?_⟩
  have hakl : a ^ (p ^ (k + l)) = 1 := by
    calc
      a ^ (p ^ (k + l)) =
          a ^ (p ^ k * p ^ l) := by rw [pow_add]
      _ = (a ^ (p ^ k)) ^ (p ^ l) := by rw [pow_mul]
      _ = 1 := by rw [hk, one_pow]
  have hbkl : b ^ (p ^ (k + l)) = 1 := by
    calc
      b ^ (p ^ (k + l)) =
          b ^ (p ^ l * p ^ k) := by
            rw [pow_add, Nat.mul_comm]
      _ = (b ^ (p ^ l)) ^ (p ^ k) := by rw [pow_mul]
      _ = 1 := by rw [hl, one_pow]
  rw [hab.mul_pow, hakl, hbkl, one_mul]

/-- An element that is both a `p`-element and `p`-regular is the identity. -/
theorem eq_one_of_isPRegular
    (p : ℕ) {g : G}
    (hp : IsPElement p g) (hr : IsPRegular p g) :
    g = 1 := by
  obtain ⟨k, hk⟩ := hp
  obtain ⟨m, hm⟩ :=
    exists_pow_eq_self_of_coprime (hr.pow_left k)
  rw [hk, one_pow] at hm
  exact hm.symm

end IsPElement

namespace IsPRegular

/-- A product of commuting `p`-regular elements is `p`-regular. -/
theorem mul_of_commute
    (p : ℕ) {a b : G}
    (ha : IsPRegular p a) (hb : IsPRegular p b)
    (hab : Commute a b) :
    IsPRegular p (a * b) := by
  exact
    Nat.Coprime.of_dvd_right
      hab.orderOf_mul_dvd_mul_orderOf
      (ha.mul_right hb)

end IsPRegular

/-- Two elements of the same cyclic subgroup commute. -/
theorem commute_of_mem_zpowers
    {g a b : G}
    (ha : a ∈ Subgroup.zpowers g)
    (hb : b ∈ Subgroup.zpowers g) :
    Commute a b := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← hm, ← hn]
  exact (Commute.refl g).zpow_zpow m n

namespace PRegularDecomposition

/-- A commuting product of a `p`-element and a `p`-regular element has the
displayed factors as its `p`-regular decomposition. -/
noncomputable def of_commute
    {p : ℕ} {t a : G}
    (ht : IsPElement p t)
    (ha : IsPRegular p a)
    (hta : Commute t a) :
    PRegularDecomposition p (t * a) := by
  let k : ℕ := Classical.choose ht
  have htk : t ^ (p ^ k) = 1 :=
    Classical.choose_spec ht
  have htOrder :
      orderOf t ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one htk
  have hcop :
      (orderOf t).Coprime (orderOf a) :=
    Nat.Coprime.of_dvd_left htOrder
      (ha.pow_left k)
  exact
    { pPart := t
      regularPart := a
      pPart_mem_zpowers :=
        (GroupTheory.mem_zpowers_mul_of_commute_coprime_order
          hta hcop).1
      regularPart_mem_zpowers :=
        (GroupTheory.mem_zpowers_mul_of_commute_coprime_order
          hta hcop).2
      commute := hta
      mul_eq := rfl
      isPElement := ht
      isPRegular := ha }

/-- The `p`-part of a decomposition is unique. -/
theorem pPart_eq
    {p : ℕ} {g : G}
    (d e : PRegularDecomposition p g) :
    d.pPart = e.pPart := by
  have hpp :
      IsPElement p (d.pPart⁻¹ * e.pPart) :=
    IsPElement.mul_of_commute p
      (d.isPElement.inv p) e.isPElement
      ((commute_of_mem_zpowers
        d.pPart_mem_zpowers e.pPart_mem_zpowers).inv_left)
  have hrr :
      IsPRegular p (d.regularPart * e.regularPart⁻¹) :=
    IsPRegular.mul_of_commute p
      d.isPRegular (e.isPRegular.inv p)
      ((commute_of_mem_zpowers
        d.regularPart_mem_zpowers
        e.regularPart_mem_zpowers).inv_right)
  have hcross :
      d.pPart⁻¹ * e.pPart =
        d.regularPart * e.regularPart⁻¹ := by
    calc
      d.pPart⁻¹ * e.pPart =
          d.pPart⁻¹ *
            (e.pPart * e.regularPart) *
              e.regularPart⁻¹ := by
                rw [mul_assoc, mul_assoc,
                  mul_inv_cancel, mul_one]
      _ = d.pPart⁻¹ *
            (d.pPart * d.regularPart) *
              e.regularPart⁻¹ := by rw [e.mul_eq, d.mul_eq]
      _ = d.regularPart * e.regularPart⁻¹ := by simp
  have hone :
      d.pPart⁻¹ * e.pPart = 1 :=
    IsPElement.eq_one_of_isPRegular p hpp
      (hcross ▸ hrr)
  exact inv_mul_eq_one.mp hone

/-- The `p`-regular part of a decomposition is unique. -/
theorem regularPart_eq
    {p : ℕ} {g : G}
    (d e : PRegularDecomposition p g) :
    d.regularPart = e.regularPart := by
  have hp := pPart_eq d e
  have hmul := d.mul_eq.trans e.mul_eq.symm
  rw [← hp] at hmul
  exact mul_left_cancel hmul

variable [Finite G]

/-- The chosen regular part of a commuting product `t * a`, with `t` a
`p`-element and `a` `p`-regular, is `a`. -/
theorem chosen_regularPart_mul
    {p : ℕ} [Fact p.Prime] {t a : G}
    (ht : IsPElement p t)
    (ha : IsPRegular p a)
    (hta : Commute t a) :
    (chosen p (t * a)).regularPart = a :=
  by
    simpa only [of_commute] using
      regularPart_eq (chosen p (t * a))
        (of_commute ht ha hta)

/-- The chosen regular part of a commuting product `a * t`, with `a`
`p`-regular and `t` a `p`-element, is `a`. -/
theorem chosen_regularPart_mul_rev
    {p : ℕ} [Fact p.Prime] {t a : G}
    (ht : IsPElement p t)
    (ha : IsPRegular p a)
    (hat : Commute a t) :
    (chosen p (a * t)).regularPart = a := by
  rw [hat.eq]
  exact chosen_regularPart_mul ht ha hat.symm

/-- A homomorphism sends a `p`-regular decomposition to one of the image. -/
def map
    {p : ℕ} {g : G}
    (d : PRegularDecomposition p g)
    (φ : G →* H) :
    PRegularDecomposition p (φ g) where
  pPart := φ d.pPart
  regularPart := φ d.regularPart
  pPart_mem_zpowers := by
    obtain ⟨k, hk⟩ :=
      Subgroup.mem_zpowers_iff.mp d.pPart_mem_zpowers
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← φ.map_zpow, hk]
  regularPart_mem_zpowers := by
    obtain ⟨k, hk⟩ :=
      Subgroup.mem_zpowers_iff.mp d.regularPart_mem_zpowers
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← φ.map_zpow, hk]
  commute := d.commute.map φ
  mul_eq := by rw [← map_mul, d.mul_eq]
  isPElement := d.isPElement.map p φ
  isPRegular := d.isPRegular.map p φ

variable [Finite H]

/-- The chosen `p`-part commutes with homomorphisms of finite groups. -/
theorem chosen_pPart_map
    (p : ℕ) [Fact p.Prime] (g : G)
    (φ : G →* H) :
    (chosen p (φ g)).pPart =
      φ (chosen p g).pPart :=
  pPart_eq (chosen p (φ g)) ((chosen p g).map φ)

/-- The chosen `p`-regular part commutes with homomorphisms of finite
groups. -/
theorem chosen_regularPart_map
    (p : ℕ) [Fact p.Prime] (g : G)
    (φ : G →* H) :
    (chosen p (φ g)).regularPart =
      φ (chosen p g).regularPart :=
  regularPart_eq (chosen p (φ g)) ((chosen p g).map φ)

/-- The chosen `p`-part is equivariant under conjugation. -/
theorem chosen_pPart_conj
    (p : ℕ) [Fact p.Prime] (c g : G) :
    (chosen p (c * g * c⁻¹)).pPart =
      c * (chosen p g).pPart * c⁻¹ := by
  simpa only [MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply] using
    chosen_pPart_map p g (MulAut.conj c).toMonoidHom

/-- The chosen `p`-regular part is equivariant under conjugation. -/
theorem chosen_regularPart_conj
    (p : ℕ) [Fact p.Prime] (c g : G) :
    (chosen p (c * g * c⁻¹)).regularPart =
      c * (chosen p g).regularPart * c⁻¹ := by
  simpa only [MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply] using
    chosen_regularPart_map p g (MulAut.conj c).toMonoidHom

end PRegularDecomposition

end McKayConjecture
