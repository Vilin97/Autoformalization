/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.OkuyamaWajimaQuotient
import McKayConjecture.GroupTheory.QuotientSubgroupPreimage

/-!
# Elementary prime-local Okuyama--Wajima subgroup facts

The intersection `V ∩ KQ = C_K(Q)` is valid for a `p'` local subgroup
`V ≤ N_A(Q)` containing `C_K(Q)`.  It is not asserted for an arbitrary
mixed-prime intermediate subgroup.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {A : Type u} [Group A] [Finite A]
variable {p : ℕ}

/-- An ambient Sylow subgroup remains Sylow in the prime-local product
`K(QV)`.

No coprimality or normalizer hypothesis is needed for this step: it is the
general fact that a Sylow subgroup remains Sylow in every intermediate
subgroup containing it. -/
def okuyamaWajimaSylowInPrimeLocalProduct
    (K V : Subgroup A)
    (Q : Sylow p A) :
    Sylow p (K ⊔ ((Q : Subgroup A) ⊔ V) : Subgroup A) :=
  Q.subtype
    ((show
        (Q : Subgroup A) ≤ (Q : Subgroup A) ⊔ V
      from le_sup_left).trans le_sup_right)

omit [Finite A] in
@[simp, norm_cast]
theorem coe_okuyamaWajimaSylowInPrimeLocalProduct
    (K V : Subgroup A)
    (Q : Sylow p A) :
    (okuyamaWajimaSylowInPrimeLocalProduct K V Q :
        Subgroup
          (K ⊔ ((Q : Subgroup A) ⊔ V) : Subgroup A)) =
      (Q : Subgroup A).subgroupOf
        (K ⊔ ((Q : Subgroup A) ⊔ V)) :=
  rfl

/-- If `V` normalizes `Q`, then the order of `QV` divides
`|V| * |Q|`.

The proof applies the ordinary cardinality bound for a product with a
normal factor internally to `Q ⊔ V`. -/
theorem card_sup_dvd_card_mul_card_of_le_normalizer
    (Q V : Subgroup A)
    (hVN : V ≤ Subgroup.normalizer (Q : Set A)) :
    Nat.card (Q ⊔ V : Subgroup A) ∣
      Nat.card V * Nat.card Q := by
  let L : Subgroup A := Q ⊔ V
  have hQL : Q ≤ L := le_sup_left
  have hVL : V ≤ L := le_sup_right
  let Qi : Subgroup L := Q.subgroupOf L
  let Vi : Subgroup L := V.subgroupOf L
  have hLN :
      L ≤ Subgroup.normalizer (Q : Set A) :=
    sup_le Subgroup.le_normalizer hVN
  letI : Qi.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLN
  have hViQi : Vi ⊔ Qi = ⊤ := by
    change V.subgroupOf L ⊔ Q.subgroupOf L = ⊤
    rw [← Subgroup.subgroupOf_sup hVL hQL]
    simp [L, sup_comm]
  have h :=
    card_sup_dvd_card_mul_card (G := L) Vi Qi
  rw [hViQi] at h
  have hcardVi :
      Nat.card Vi = Nat.card V :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hVL).toEquiv
  have hcardQi :
      Nat.card Qi = Nat.card Q :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
  simpa [L, hcardVi, hcardQi] using h

/-- If `K` and `V` have order prime to `p`, `K` is normal, `Q` is a
`p`-group, and `V` normalizes `Q`, then the internal copy of `Q` is a
Sylow subgroup of `K(QV)`.

This is the Sylow fact used in the prime-away Okuyama--Wajima pieces.  It
does not assume that `Q` is Sylow in the original ambient group. -/
def okuyamaWajimaSylowInPrimeAwayLocalProduct
    (K Q V : Subgroup A) [K.Normal] [Fact p.Prime]
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hV : IsPPrimeGroup p V)
    (hVN : V ≤ Subgroup.normalizer (Q : Set A)) :
    Sylow p (K ⊔ (Q ⊔ V) : Subgroup A) := by
  let L : Subgroup A := Q ⊔ V
  let H : Subgroup A := K ⊔ L
  have hQL : Q ≤ L := le_sup_left
  have hLH : L ≤ H := le_sup_right
  have hQH : Q ≤ H := hQL.trans hLH
  have hLdvd :
      Nat.card L ∣ Nat.card V * Nat.card Q :=
    card_sup_dvd_card_mul_card_of_le_normalizer
      Q V hVN
  have hHdvd :
      Nat.card H ∣ Nat.card L * Nat.card K := by
    have h :=
      card_sup_dvd_card_mul_card L K
    simpa [H, sup_comm] using h
  have hHdvd' :
      Nat.card H ∣
        Nat.card Q * (Nat.card V * Nat.card K) := by
    calc
      Nat.card H ∣ Nat.card L * Nat.card K :=
        hHdvd
      _ ∣ (Nat.card V * Nat.card Q) * Nat.card K :=
        Nat.mul_dvd_mul_right hLdvd _
      _ = Nat.card Q * (Nat.card V * Nat.card K) := by
        ac_rfl
  have hindexDvd :
      (Q.subgroupOf H).index ∣
        Nat.card V * Nat.card K := by
    apply Nat.dvd_of_mul_dvd_mul_left
      (Nat.card_pos (α := Q))
    have hcardQH :
        Nat.card (Q.subgroupOf H) = Nat.card Q :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
    have hmul :
        Nat.card Q * (Q.subgroupOf H).index =
          Nat.card H := by
      rw [← hcardQH]
      exact (Q.subgroupOf H).card_mul_index
    rw [hmul]
    exact hHdvd'
  have hnot :
      ¬p ∣ (Q.subgroupOf H).index :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mp
      ((hV.mul_right hK).coprime_dvd_right
        hindexDvd)
  exact
    (hQ.of_equiv
      (Subgroup.subgroupOfEquivOfLe hQH).symm).toSylow
        hnot

@[simp, norm_cast]
theorem coe_okuyamaWajimaSylowInPrimeAwayLocalProduct
    (K Q V : Subgroup A) [K.Normal] [Fact p.Prime]
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hV : IsPPrimeGroup p V)
    (hVN : V ≤ Subgroup.normalizer (Q : Set A)) :
    (okuyamaWajimaSylowInPrimeAwayLocalProduct
        K Q V hQ hK hV hVN :
      Subgroup (K ⊔ (Q ⊔ V) : Subgroup A)) =
        Q.subgroupOf (K ⊔ (Q ⊔ V)) :=
  rfl

/-- On an explicitly `p'` intermediate subgroup of the normalizer,
intersection with `KQ` is exactly the fixed-point subgroup.

This is the form used for the `r ≠ p` Sylow-preimage pieces. -/
theorem pPrimeNormalizer_inf_normalProduct_eq_fixedPoints
    (K Q V : Subgroup A) [K.Normal]
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hV : IsPPrimeGroup p V)
    (hVN : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV :
      K ⊓ Subgroup.centralizer (Q : Set A) ≤ V) :
    V ⊓ (K ⊔ Q) =
      K ⊓ Subgroup.centralizer (Q : Set A) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨k, hkK, q, hqQ, hkq⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hx.2
    have hxN :
        x ∈ Subgroup.normalizer (Q : Set A) :=
      hVN hx.1
    have hqN :
        q ∈ Subgroup.normalizer (Q : Set A) :=
      Subgroup.le_normalizer hqQ
    have hkEq : k = x * q⁻¹ := by
      rw [← hkq]
      group
    have hkN :
        k ∈ Subgroup.normalizer (Q : Set A) := by
      rw [hkEq]
      exact mul_mem hxN (inv_mem hqN)
    have hkC :
        k ∈ Subgroup.centralizer (Q : Set A) :=
      inf_normalizer_le_centralizer_of_normal_isPPrime
        (p := p) Q K hQ hK ⟨hkK, hkN⟩
    have hkV : k ∈ V :=
      hCV ⟨hkK, hkC⟩
    have hqEq : q = k⁻¹ * x := by
      rw [← hkq]
      group
    have hqV : q ∈ V := by
      rw [hqEq]
      exact mul_mem (inv_mem hkV) hx.1
    have hqOne : q = 1 :=
      Subgroup.disjoint_def.mp
        (IsPGroup.disjoint_of_isPPrimeGroup hQ hV)
        hqQ hqV
    rw [← hkq, hqOne, mul_one]
    exact ⟨hkK, hkC⟩
  · intro x hx
    exact
      ⟨hCV hx,
        (show K ≤ K ⊔ Q from le_sup_left) hx.1⟩

/-- In the local product `K(QV)`, the ambient normalizer intersection is
exactly `QV`.

Unlike the intersection theorem above, this identity does not need `V` to
be a `p'`-group.  The `p'` hypothesis is needed separately when promoting
the internal copy of `Q` to a Sylow subgroup of the local product. -/
theorem normalizer_inf_pPrimeKernel_sup_normalizing_eq
    (K Q V : Subgroup A) [K.Normal]
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hVN : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV :
      K ⊓ Subgroup.centralizer (Q : Set A) ≤ V) :
    Subgroup.normalizer (Q : Set A) ⊓
        (K ⊔ (Q ⊔ V)) =
      Q ⊔ V := by
  apply le_antisymm
  · intro g hg
    obtain ⟨k, hkK, x, hxQV, hkx⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hg.2
    have hQVN :
        Q ⊔ V ≤ Subgroup.normalizer (Q : Set A) :=
      sup_le Subgroup.le_normalizer hVN
    have hxN :
        x ∈ Subgroup.normalizer (Q : Set A) :=
      hQVN hxQV
    have hkEq : k = g * x⁻¹ := by
      rw [← hkx]
      group
    have hkN :
        k ∈ Subgroup.normalizer (Q : Set A) := by
      rw [hkEq]
      exact mul_mem hg.1 (inv_mem hxN)
    have hkC :
        k ∈ Subgroup.centralizer (Q : Set A) :=
      inf_normalizer_le_centralizer_of_normal_isPPrime
        (p := p) Q K hQ hK ⟨hkK, hkN⟩
    have hkV : k ∈ V :=
      hCV ⟨hkK, hkC⟩
    rw [← hkx]
    exact
      (Q ⊔ V).mul_mem
        ((show V ≤ Q ⊔ V from le_sup_right) hkV)
        hxQV
  · exact le_inf
      (sup_le Subgroup.le_normalizer hVN)
      le_sup_right

end GroupTheory
end McKayConjecture
