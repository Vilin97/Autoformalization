/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaFullFixedOuterCoordinates

/-!
# The outer index in the full-fixed Okuyama--Wajima branch

Let `K ◁ G` be a normal `p'`-subgroup, let `P` be a Sylow
`p`-subgroup, and assume that `K P` is normal.  For the canonical
Okuyama--Wajima complement

`M = okuyamaWajimaProperBranchComplement K P hK hKP`,

the middle group in the printed full-fixed argument is `M K`.  This
file records the exact product and intersection coordinates

`P (M K) = G` and `P ∩ (M K) = 1`.

The subgroup-product coset equivalence therefore gives the exact index
formula

`[G : M K] = |P|`.

In particular, the outer index is a power of `p`, which is the input
needed for the final prime-power extension ascent.
-/

noncomputable section

namespace McKayConjecture
namespace OkuyamaWajimaFullFixedOuterIndex

open GroupTheory
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable
  (hK : IsPPrimeGroup p K)
  (hKP : (K ⊔ (P : Subgroup G)).Normal)

/-- The canonical middle subgroup `M K` in the full-fixed branch. -/
abbrev okuyamaWajimaFullFixedMiddle : Subgroup G :=
  okuyamaWajimaProperBranchComplement K P hK hKP ⊔ K

/-- Every ambient element has a literal factorization `p h`, where
`p ∈ P` and `h ∈ M K`.

The normal-product theorem first writes an element as a product from
`K P` and `M K`.  Normality of `K` reorders the first factor into
`P K`, after which its `K`-factor can be absorbed into `M K`. -/
theorem sylow_mul_okuyamaWajimaFullFixedMiddle_eq_top :
    ((P : Subgroup G) : Set G) *
        (okuyamaWajimaFullFixedMiddle K P hK hKP : Set G) =
      (⊤ : Subgroup G) := by
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  let H : Subgroup G := M ⊔ K
  change
    ((P : Subgroup G) : Set G) * (H : Set G) =
      (⊤ : Subgroup G)
  apply Set.Subset.antisymm
  · intro x _hx
    trivial
  · intro g _hg
    have htop :
        (K ⊔ (P : Subgroup G)) ⊔ H =
          (⊤ : Subgroup G) := by
      simpa only [H, M] using
        normalProduct_sup_ambientComplement_sup_kernel_eq_top
          P K hK hKP
    have hgJoin :
        g ∈ (K ⊔ (P : Subgroup G)) ⊔ H := by
      rw [htop]
      trivial
    letI : (K ⊔ (P : Subgroup G)).Normal := hKP
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hgJoin
    have ha' : a ∈ (P : Subgroup G) ⊔ K := by
      simpa only [sup_comm] using ha
    obtain ⟨x, hxP, k, hkK, hxk⟩ :=
      Subgroup.mem_sup_of_normal_right.mp ha'
    have hkH : k ∈ H :=
      (show K ≤ H from le_sup_right) hkK
    refine ⟨x, hxP, k * b, H.mul_mem hkH hb, ?_⟩
    rw [← hab, ← hxk]
    group

/-- The Sylow subgroup meets the canonical full-fixed middle subgroup
trivially. -/
theorem sylow_inf_okuyamaWajimaFullFixedMiddle_eq_bot :
    (P : Subgroup G) ⊓
        okuyamaWajimaFullFixedMiddle K P hK hKP =
      ⊥ := by
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  let H : Subgroup G := M ⊔ K
  change (P : Subgroup G) ⊓ H = ⊥
  have hnormalProductInf :
      (K ⊔ (P : Subgroup G)) ⊓ H = K := by
    simpa only [H, M] using
      normalProduct_inf_ambientComplement_sup_kernel_eq_kernel
        P K hK hKP
  have hleK :
      (P : Subgroup G) ⊓ H ≤ K := by
    intro x hx
    have hx' :
        x ∈ (K ⊔ (P : Subgroup G)) ⊓ H :=
      ⟨(show (P : Subgroup G) ≤
          K ⊔ (P : Subgroup G) from le_sup_right) hx.1,
        hx.2⟩
    rwa [hnormalProductInf] at hx'
  apply le_antisymm
  · calc
      (P : Subgroup G) ⊓ H ≤
          (P : Subgroup G) ⊓ K :=
        le_inf inf_le_left hleK
      _ = ⊥ :=
        IsPGroup.inf_eq_bot_of_isPPrimeGroup
          P.isPGroup' hK
  · exact bot_le

/-- Internally in `P`, the copy of the full-fixed middle subgroup is
the bottom subgroup. -/
theorem okuyamaWajimaFullFixedMiddle_subgroupOf_sylow_eq_bot :
    (okuyamaWajimaFullFixedMiddle K P hK hKP).subgroupOf
        (P : Subgroup G) =
      ⊥ := by
  apply le_antisymm
  · intro x hx
    have hxInf :
        (x : G) ∈
          (P : Subgroup G) ⊓
            okuyamaWajimaFullFixedMiddle K P hK hKP :=
      ⟨x.property, hx⟩
    rw [sylow_inf_okuyamaWajimaFullFixedMiddle_eq_bot
      K P hK hKP] at hxInf
    have hxOneG : (x : G) = 1 :=
      Subgroup.mem_bot.mp hxInf
    exact
      Subgroup.mem_bot.mpr
        (Subtype.ext hxOneG)
  · exact bot_le

/-- Exact outer-index formula for the full-fixed middle subgroup:
`[G : M K] = |P|`. -/
theorem okuyamaWajimaFullFixedMiddle_index_eq_card_sylow :
    (okuyamaWajimaFullFixedMiddle K P hK hKP).index =
      Nat.card P := by
  calc
    (okuyamaWajimaFullFixedMiddle K P hK hKP).index =
        (okuyamaWajimaFullFixedMiddle K P hK hKP).relIndex
          (P : Subgroup G) :=
      index_eq_relIndex_of_mul_eq_top
        (okuyamaWajimaFullFixedMiddle K P hK hKP)
        (P : Subgroup G)
        (sylow_mul_okuyamaWajimaFullFixedMiddle_eq_top
          K P hK hKP)
    _ = Nat.card P := by
      rw [Subgroup.relIndex,
        okuyamaWajimaFullFixedMiddle_subgroupOf_sylow_eq_bot
          K P hK hKP,
        Subgroup.index_bot]

/-- The canonical full-fixed middle subgroup has ambient index exactly
a power of `p`. -/
theorem okuyamaWajimaFullFixedMiddle_index_eq_prime_power :
    ∃ n : ℕ,
      (okuyamaWajimaFullFixedMiddle K P hK hKP).index =
        p ^ n := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  exact
    ⟨n,
      (okuyamaWajimaFullFixedMiddle_index_eq_card_sylow
        K P hK hKP).trans hn⟩

/-- Divisibility form of the full-fixed outer prime-power index,
matching the input shape used by prime-power ascent theorems. -/
theorem okuyamaWajimaFullFixedMiddle_index_dvd_prime_power :
    ∃ n : ℕ,
      (okuyamaWajimaFullFixedMiddle K P hK hKP).index ∣
        p ^ n := by
  obtain ⟨n, hn⟩ :=
    okuyamaWajimaFullFixedMiddle_index_eq_prime_power
      K P hK hKP
  exact ⟨n, hn ▸ dvd_refl _⟩

end OkuyamaWajimaFullFixedOuterIndex
end McKayConjecture
