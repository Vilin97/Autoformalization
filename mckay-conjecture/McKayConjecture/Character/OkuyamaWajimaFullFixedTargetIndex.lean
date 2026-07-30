/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaFullFixedCoordinates
import McKayConjecture.GroupTheory.SubgroupProductIndex

/-!
# The target complement index in the full-fixed branch

The canonical Okuyama--Wajima complement inside `N_G(P)` has index
exactly `|P|`.  This is the target-side counterpart of the ambient
middle-index calculation.

Internally in the normalizer, write `D = C_K(P)`, let `S` be the copy
of `P`, and let `M` be the lifted complement.  The complement
coordinates give `(D ⊔ S) ⊔ M = ⊤` and `D ≤ M`; hence every element is
a product from `S M`.  Moreover `S ∩ M = 1`, since `S` is a `p`-group
and `M` is a `p'`-group.  The product-index formula then gives
`[N_G(P) : M] = |P|`.
-/

noncomputable section

namespace McKayConjecture
namespace OkuyamaWajimaFullFixedTargetIndex

open GroupTheory
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable
  (hK : IsPPrimeGroup p K)
  (hKP : (K ⊔ (P : Subgroup G)).Normal)

/-- The canonical complement, retained in its native subgroup of the
Sylow normalizer. -/
abbrev targetComplement :
    Subgroup
      (Subgroup.normalizer ((P : Subgroup G) : Set G)) :=
  okuyamaWajimaComplement P K hK hKP

/-- The internal Sylow subgroup and target complement generate the
whole normalizer as a product set. -/
theorem internalSylow_mul_targetComplement_eq_top :
    ((okuyamaWajimaInternalSylow
        (P : Subgroup G) :
          Subgroup
            (Subgroup.normalizer
              ((P : Subgroup G) : Set G))) : Set
                (Subgroup.normalizer
                  ((P : Subgroup G) : Set G))) *
        (targetComplement K P hK hKP : Set
          (Subgroup.normalizer
            ((P : Subgroup G) : Set G))) =
      (⊤ : Subgroup
        (Subgroup.normalizer
          ((P : Subgroup G) : Set G))) := by
  let N :=
    Subgroup.normalizer ((P : Subgroup G) : Set G)
  let D : Subgroup N :=
    okuyamaWajimaInternalFixedPoints K (P : Subgroup G)
  let S : Subgroup N :=
    okuyamaWajimaInternalSylow (P : Subgroup G)
  let M : Subgroup N :=
    targetComplement K P hK hKP
  letI : D.Normal :=
    internalFixedPoints_normal K (P : Subgroup G)
  have htop :
      (D ⊔ S) ⊔ M = (⊤ : Subgroup N) := by
    simpa only [D, S, M, targetComplement] using
      internalFixedPoints_sup_sylow_sup_complement_eq_top
        P K hK hKP
  have hDM : D ≤ M := by
    simpa only [D, M, targetComplement] using
      internalFixedPoints_le_okuyamaWajimaComplement
        P K hK hKP
  apply Set.Subset.antisymm
  · intro x _hx
    trivial
  · intro g _hg
    have hgJoin : g ∈ (D ⊔ S) ⊔ M := by
      rw [htop]
      trivial
    letI : (D ⊔ S).Normal :=
      internalFixedPoints_sup_sylow_normal P K hK hKP
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hgJoin
    have ha' : a ∈ S ⊔ D := by
      simpa only [sup_comm] using ha
    obtain ⟨s, hs, d, hd, hsd⟩ :=
      Subgroup.mem_sup_of_normal_right.mp ha'
    refine ⟨s, hs, d * b, M.mul_mem (hDM hd) hb, ?_⟩
    rw [← hab, ← hsd]
    group

/-- The internal Sylow subgroup meets the target complement trivially. -/
theorem internalSylow_inf_targetComplement_eq_bot :
    okuyamaWajimaInternalSylow (P : Subgroup G) ⊓
        targetComplement K P hK hKP =
      ⊥ := by
  have hMambient :
      IsPPrimeGroup p
        (okuyamaWajimaAmbientComplement P K hK hKP) :=
    OkuyamaWajimaFullFixedCoordinates.ambientComplement_isPPrime
      P K hK hKP
  have hM :
      IsPPrimeGroup p
        (targetComplement K P hK hKP) :=
    hMambient.of_equiv
      (okuyamaWajimaComplementEquivAmbientComplement
        P K hK hKP).symm
  exact
    IsPGroup.inf_eq_bot_of_isPPrimeGroup
      (okuyamaWajimaSylowInNormalizer P).isPGroup' hM

/-- Internally in `P`, the copy of the target complement is bottom. -/
theorem targetComplement_subgroupOf_internalSylow_eq_bot :
    (targetComplement K P hK hKP).subgroupOf
        (okuyamaWajimaInternalSylow (P : Subgroup G)) =
      ⊥ := by
  apply le_antisymm
  · intro x hx
    have hxInf :
        (x :
          Subgroup.normalizer
            ((P : Subgroup G) : Set G)) ∈
          okuyamaWajimaInternalSylow (P : Subgroup G) ⊓
            targetComplement K P hK hKP :=
      ⟨x.property, hx⟩
    rw [internalSylow_inf_targetComplement_eq_bot
      K P hK hKP] at hxInf
    exact
      Subgroup.mem_bot.mpr
        (Subtype.ext (Subgroup.mem_bot.mp hxInf))
  · exact bot_le

/-- Exact target-side index formula:
`[N_G(P) : M] = |P|`. -/
theorem targetComplement_index_eq_card_sylow :
    (targetComplement K P hK hKP).index =
      Nat.card P := by
  let S :=
    okuyamaWajimaInternalSylow (P : Subgroup G)
  calc
    (targetComplement K P hK hKP).index =
        (targetComplement K P hK hKP).relIndex S :=
      index_eq_relIndex_of_mul_eq_top
        (targetComplement K P hK hKP) S
        (internalSylow_mul_targetComplement_eq_top
          K P hK hKP)
    _ = Nat.card S := by
      rw [Subgroup.relIndex,
        targetComplement_subgroupOf_internalSylow_eq_bot
          K P hK hKP,
        Subgroup.index_bot]
    _ = Nat.card P :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (show
            (P : Subgroup G) ≤
              Subgroup.normalizer ((P : Subgroup G) : Set G)
            from Subgroup.le_normalizer))

/-- The target complement has prime-power index in the Sylow
normalizer, in the divisibility form consumed by Navarro's theorem. -/
theorem targetComplement_index_dvd_prime_power :
    ∃ n : ℕ,
      (targetComplement K P hK hKP).index ∣ p ^ n := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  exact
    ⟨n,
      (targetComplement_index_eq_card_sylow
        K P hK hKP).trans hn ▸ dvd_refl _⟩

end OkuyamaWajimaFullFixedTargetIndex
end McKayConjecture
