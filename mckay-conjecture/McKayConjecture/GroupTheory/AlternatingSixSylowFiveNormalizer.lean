/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import McKayConjecture.GroupTheory.AlternatingSixSylowStructure
import McKayConjecture.GroupTheory.CentralExtensionSylowNormalizer

/-!
# The Sylow-five normalizer in `A₆`

This file computes the first target normalizer needed for the local
`A₆` calculation.  A nontrivial element of a Sylow `5`-subgroup is a
five-cycle.  Its full symmetric-group centralizer has order five and is
already contained in the alternating group.  It follows that the
centralizer of the Sylow subgroup has order five.  The conjugation map from
the normalizer to its automorphism group then bounds the normalizer order;
the Sylow congruence determines it exactly.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

open Equiv

local instance alternatingSixNormalizerFactPrimeFive :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- An element of order five in `A₆`, viewed as a permutation, has cycle
type consisting of one five-cycle. -/
theorem alternatingSix_cycleType_eq_five_of_orderOf_eq_five
    (g : AlternatingSix)
    (hg : orderOf g = 5) :
    (g : Equiv.Perm (Fin 6)).cycleType = {5} := by
  have hgPerm :
      orderOf (g : Equiv.Perm (Fin 6)) = 5 :=
    (Subgroup.orderOf_coe g).trans hg
  obtain ⟨n, hn⟩ :=
    Equiv.Perm.cycleType_prime_order
      (show
        (orderOf (g : Equiv.Perm (Fin 6))).Prime by
          rw [hgPerm]
          exact Nat.prime_five)
  rw [hgPerm] at hn
  have hsum :
      ((g : Equiv.Perm (Fin 6)).cycleType).sum ≤ 6 := by
    simpa using
      (g : Equiv.Perm (Fin 6)).sum_cycleType_le
  rw [hn, Multiset.sum_replicate] at hsum
  simp only [nsmul_eq_mul, Nat.cast_id] at hsum
  have hnZero : n = 0 := by omega
  subst n
  simpa using hn

/-- The full symmetric-group centralizer of an order-five element of
`A₆` is contained in `A₆`. -/
theorem perm_centralizer_le_alternatingSix_of_orderOf_eq_five
    (g : AlternatingSix)
    (hg : orderOf g = 5) :
    Subgroup.centralizer
        ({(g : Equiv.Perm (Fin 6))} :
          Set (Equiv.Perm (Fin 6))) ≤
      alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.centralizer_le_alternating_iff,
    alternatingSix_cycleType_eq_five_of_orderOf_eq_five g hg]
  constructor
  · intro c hc
    simp only [Multiset.mem_singleton] at hc
    subst c
    exact ⟨2, by norm_num⟩
  constructor
  · norm_num
  · intro i
    simpa using
      Multiset.count_le_card i ({5} : Multiset ℕ)

/-- The full symmetric-group centralizer of an order-five element of
`A₆` has order five. -/
theorem natCard_perm_centralizer_orderFive
    (g : AlternatingSix)
    (hg : orderOf g = 5) :
    Nat.card
        (Subgroup.centralizer
          ({(g : Equiv.Perm (Fin 6))} :
            Set (Equiv.Perm (Fin 6)))) =
      5 := by
  rw [Equiv.Perm.nat_card_centralizer,
    alternatingSix_cycleType_eq_five_of_orderOf_eq_five g hg]
  norm_num

/-- If the full permutation centralizer of an alternating permutation is
alternating, then its centralizer computed inside the alternating group is
canonically the same group. -/
def alternatingCentralizerEquivPermCentralizer
    (g : AlternatingSix)
    (hcentralizer :
      Subgroup.centralizer
          ({(g : Equiv.Perm (Fin 6))} :
            Set (Equiv.Perm (Fin 6))) ≤
        alternatingGroup (Fin 6)) :
    Subgroup.centralizer ({g} : Set AlternatingSix) ≃*
      Subgroup.centralizer
        ({(g : Equiv.Perm (Fin 6))} :
          Set (Equiv.Perm (Fin 6))) where
  toFun x :=
    ⟨x.1.1, by
      have hx := x.2
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      exact congr_arg Subtype.val hx⟩
  invFun x :=
    ⟨⟨x.1, hcentralizer x.2⟩, by
      have hx := x.2
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      exact Subtype.ext hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The centralizer inside `A₆` of an element of order five has order
five. -/
theorem natCard_alternatingSix_centralizer_orderFive
    (g : AlternatingSix)
    (hg : orderOf g = 5) :
    Nat.card
        (Subgroup.centralizer ({g} : Set AlternatingSix)) =
      5 := by
  rw [Nat.card_congr
      (alternatingCentralizerEquivPermCentralizer g
        (perm_centralizer_le_alternatingSix_of_orderOf_eq_five
          g hg)).toEquiv,
    natCard_perm_centralizer_orderFive g hg]

/-- The centralizer of a cyclic subgroup is already the centralizer of
any chosen generator. -/
theorem centralizer_eq_centralizer_singleton_of_generator
    {G : Type*} [Group G]
    (P : Subgroup G)
    (g : P)
    (hgenerator : ∀ x : P, x ∈ Subgroup.zpowers g) :
    Subgroup.centralizer (P : Set G) =
      Subgroup.centralizer ({(g : G)} : Set G) := by
  apply le_antisymm
  · apply Subgroup.centralizer_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact g.2
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, hn⟩ :=
      Subgroup.mem_zpowers_iff.mp
        (hgenerator ⟨y, hy⟩)
    have hcommute : Commute (g : G) x :=
      hx.symm
    have hcommutePower :
        Commute ((g : G) ^ n) x :=
      hcommute.zpow_left n
    have hnCoe : (g : G) ^ n = y := by
      exact congr_arg Subtype.val hn
    rw [hnCoe] at hcommutePower
    exact hcommutePower.eq

/-- The centralizer in `A₆` of a Sylow `5`-subgroup has order five. -/
theorem natCard_centralizer_sylowFive_alternatingSix
    (P : Sylow 5 AlternatingSix) :
    Nat.card
        (Subgroup.centralizer
          ((P : Subgroup AlternatingSix) : Set AlternatingSix)) =
      5 := by
  letI : IsCyclic P :=
    sylowFive_alternatingSix_isCyclic P
  obtain ⟨g, hgenerator⟩ :=
    IsCyclic.exists_generator (α := P)
  have hg :
      orderOf g = 5 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgenerator,
      natCard_sylowFive_alternatingSix]
  change
    Nat.card
        (Subgroup.centralizer
          ((P : Subgroup AlternatingSix) : Set AlternatingSix)) =
      5
  rw [centralizer_eq_centralizer_singleton_of_generator
      (P : Subgroup AlternatingSix) g hgenerator,
    natCard_alternatingSix_centralizer_orderFive
      g ((Subgroup.orderOf_coe g).trans hg)]

/-- The order of the Sylow `5`-normalizer divides twenty. -/
theorem natCard_normalizer_sylowFive_alternatingSix_dvd_twenty
    (P : Sylow 5 AlternatingSix) :
    Nat.card
        (Subgroup.normalizer
          ((P : Subgroup AlternatingSix) : Set AlternatingSix)) ∣
      20 := by
  letI : IsCyclic P :=
    sylowFive_alternatingSix_isCyclic P
  let f :=
    (P : Subgroup AlternatingSix).normalizerMonoidHom
  have hker :
      Nat.card f.ker = 5 := by
    rw [Subgroup.normalizerMonoidHom_ker,
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (Subgroup.centralizer_le_normalizer
            ((P : Subgroup AlternatingSix) :
              Set AlternatingSix))).toEquiv,
      natCard_centralizer_sylowFive_alternatingSix P]
  have hAut :
      Nat.card (MulAut P) = 4 := by
    rw [IsCyclic.card_mulAut,
      natCard_sylowFive_alternatingSix,
      Nat.totient_prime Nat.prime_five]
  have hrange :
      Nat.card f.range ∣ 4 := by
    rw [← hAut]
    exact f.range.card_subgroup_dvd_card
  have hnormalizer :
      Nat.card
        (Subgroup.normalizer
            ((P : Subgroup AlternatingSix) : Set AlternatingSix)) =
        5 * Nat.card f.range := by
    calc
      Nat.card
          (Subgroup.normalizer
            ((P : Subgroup AlternatingSix) : Set AlternatingSix)) =
        Nat.card f.ker * f.ker.index :=
          f.ker.card_mul_index.symm
      _ = 5 * Nat.card f.range := by
        rw [Subgroup.index_ker, hker]
  rw [hnormalizer]
  exact Nat.mul_dvd_mul_left 5 hrange

/-- The Sylow `5`-normalizer in `A₆` has order ten. -/
@[simp]
theorem natCard_normalizer_sylowFive_alternatingSix
    (P : Sylow 5 AlternatingSix) :
    Nat.card
        (Subgroup.normalizer
          ((P : Subgroup AlternatingSix) : Set AlternatingSix)) =
      10 := by
  have hdvd :=
    natCard_normalizer_sylowFive_alternatingSix_dvd_twenty P
  have hle :
      Nat.card
          (Subgroup.normalizer
            ((P : Subgroup AlternatingSix) : Set AlternatingSix)) ≤
        20 :=
    Nat.le_of_dvd (by norm_num) hdvd
  have hproduct :
      Nat.card
          (Subgroup.normalizer
            ((P : Subgroup AlternatingSix) : Set AlternatingSix)) *
          Nat.card (Sylow 5 AlternatingSix) =
        360 := by
    have hindex :
        (Subgroup.normalizer
          ((P : Subgroup AlternatingSix) :
            Set AlternatingSix)).index =
          Nat.card (Sylow 5 AlternatingSix) := by
      have h :=
        P.card_eq_index_normalizer
      change
        Nat.card (Sylow 5 AlternatingSix) =
          (Subgroup.normalizer
            ((P : Subgroup AlternatingSix) :
              Set AlternatingSix)).index at h
      exact h.symm
    rw [← hindex,
      Subgroup.card_mul_index,
      natCard_alternatingSix]
  have hmod :
      Nat.card (Sylow 5 AlternatingSix) % 5 = 1 := by
    exact
      card_sylow_modEq_one 5 AlternatingSix
  interval_cases hnormalizer :
    Nat.card
      (Subgroup.normalizer
        ((P : Subgroup AlternatingSix) : Set AlternatingSix))
  all_goals norm_num at hdvd
  all_goals omega

/-- There are exactly thirty-six Sylow `5`-subgroups in `A₆`. -/
@[simp]
theorem natCard_sylowFive_subgroups_alternatingSix :
    Nat.card (Sylow 5 AlternatingSix) = 36 := by
  let P : Sylow 5 AlternatingSix :=
    default
  have hproduct :
      Nat.card
          (Subgroup.normalizer
            ((P : Subgroup AlternatingSix) : Set AlternatingSix)) *
          Nat.card (Sylow 5 AlternatingSix) =
        360 := by
    have hindex :
        (Subgroup.normalizer
          ((P : Subgroup AlternatingSix) :
            Set AlternatingSix)).index =
          Nat.card (Sylow 5 AlternatingSix) := by
      have h :=
        P.card_eq_index_normalizer
      change
        Nat.card (Sylow 5 AlternatingSix) =
          (Subgroup.normalizer
            ((P : Subgroup AlternatingSix) :
              Set AlternatingSix)).index at h
      exact h.symm
    rw [← hindex,
      Subgroup.card_mul_index,
      natCard_alternatingSix]
  rw [natCard_normalizer_sylowFive_alternatingSix] at hproduct
  omega

/-- The image of the Sylow `5`-normalizer in the automorphism group of
the Sylow subgroup has order two. -/
theorem natCard_sylowFive_normalizerMonoidHom_range
    (P : Sylow 5 AlternatingSix) :
    Nat.card
        (P : Subgroup AlternatingSix).normalizerMonoidHom.range =
      2 := by
  let f :=
    (P : Subgroup AlternatingSix).normalizerMonoidHom
  change Nat.card f.range = 2
  have hker :
      Nat.card f.ker = 5 := by
    rw [Subgroup.normalizerMonoidHom_ker,
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (Subgroup.centralizer_le_normalizer
            ((P : Subgroup AlternatingSix) :
              Set AlternatingSix))).toEquiv,
      natCard_centralizer_sylowFive_alternatingSix P]
  have hproduct :
      Nat.card f.ker * Nat.card f.range =
        Nat.card
          (Subgroup.normalizer
            ((P : Subgroup AlternatingSix) : Set AlternatingSix)) := by
    calc
      Nat.card f.ker * Nat.card f.range =
          Nat.card f.ker * f.ker.index := by
            rw [Subgroup.index_ker]
      _ = Nat.card
          (Subgroup.normalizer
            ((P : Subgroup AlternatingSix) :
              Set AlternatingSix)) :=
        f.ker.card_mul_index
  have hfive :
      5 * Nat.card f.range = 10 := by
    calc
      5 * Nat.card f.range =
          Nat.card f.ker * Nat.card f.range := by
            rw [hker]
      _ =
          Nat.card
            (Subgroup.normalizer
              ((P : Subgroup AlternatingSix) :
                Set AlternatingSix)) :=
        hproduct
      _ = 10 :=
        natCard_normalizer_sylowFive_alternatingSix P
  omega

/-- A Sylow `5`-subgroup has relative index two in its normalizer. -/
theorem relIndex_sylowFive_normalizer_alternatingSix
    (P : Sylow 5 AlternatingSix) :
    (P : Subgroup AlternatingSix).relIndex
        (Subgroup.normalizer
          ((P : Subgroup AlternatingSix) :
            Set AlternatingSix)) =
      2 := by
  let N :=
    Subgroup.normalizer
      ((P : Subgroup AlternatingSix) :
        Set AlternatingSix)
  change (P : Subgroup AlternatingSix).relIndex N = 2
  have hcardSubgroup :
      Nat.card
          ((P : Subgroup AlternatingSix).subgroupOf N) =
        5 := by
    rw [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (P : Subgroup AlternatingSix).le_normalizer).toEquiv,
      natCard_sylowFive_alternatingSix]
  have hcard :=
    ((P : Subgroup AlternatingSix).subgroupOf N).card_mul_index
  change
    Nat.card
        ((P : Subgroup AlternatingSix).subgroupOf N) *
        (P : Subgroup AlternatingSix).relIndex N =
      Nat.card N at hcard
  rw [hcardSubgroup,
    natCard_normalizer_sylowFive_alternatingSix] at hcard
  omega

/-- The Sylow `5`-normalizer in `A₆` is noncommutative. -/
theorem sylowFive_normalizer_alternatingSix_not_isMulCommutative
    (P : Sylow 5 AlternatingSix) :
    ¬IsMulCommutative
      (Subgroup.normalizer
        ((P : Subgroup AlternatingSix) :
          Set AlternatingSix)) := by
  intro hcomm
  let N :=
    Subgroup.normalizer
      ((P : Subgroup AlternatingSix) :
        Set AlternatingSix)
  let f :=
    (P : Subgroup AlternatingSix).normalizerMonoidHom
  have hf : f = 1 := by
    apply MonoidHom.ext
    intro x
    apply DFunLike.ext _ _
    intro y
    apply Subtype.ext
    change
      (x : AlternatingSix) * (y : AlternatingSix) *
          (x : AlternatingSix)⁻¹ =
        (y : AlternatingSix)
    have hxy :
        x *
            (⟨y, (P : Subgroup AlternatingSix).le_normalizer y.2⟩ :
              N) =
          (⟨y, (P : Subgroup AlternatingSix).le_normalizer y.2⟩ :
              N) *
            x :=
      hcomm.is_comm.comm _ _
    have hxyCoe :=
      congrArg Subtype.val hxy
    change
      (x : AlternatingSix) * (y : AlternatingSix) =
        (y : AlternatingSix) * (x : AlternatingSix) at hxyCoe
    rw [hxyCoe]
    simp
  have hrange :=
    natCard_sylowFive_normalizerMonoidHom_range P
  change Nat.card f.range = 2 at hrange
  rw [hf] at hrange
  norm_num at hrange

/-! ### Lifting the normalizer to the universal cover -/

/-- The fixed Sylow `5`-subgroup of the canonical cover is the canonical
central-extension lift of its target image. -/
theorem alternatingSixUniversalCoverSylowFive_eq_sylowLift :
    alternatingSixUniversalCoverSylow 5 =
      alternatingSixUniversalCentralExtension.toCentralExtension.sylowLift
        (alternatingSixUniversalCoverTargetSylow 5) := by
  apply
    (CentralExtension.eq_sylowLift_iff_mapSurjective_eq
      alternatingSixUniversalCentralExtension.toCentralExtension
        (alternatingSixUniversalCoverTargetSylow 5)
        (alternatingSixUniversalCoverSylow 5)).mpr
  rfl

/-- The normalizer of the fixed cover Sylow `5`-subgroup has order ten
times the order of the center. -/
theorem natCard_normalizer_alternatingSixUniversalCoverSylowFive :
    Nat.card
        (Subgroup.normalizer
          (alternatingSixUniversalCoverSylow 5 :
            Set AlternatingSixUniversalCover)) =
      Nat.card (Subgroup.center AlternatingSixUniversalCover) *
        10 := by
  have h :=
    CentralExtension.sylowNormalizer_card_eq
      alternatingSixUniversalCentralExtension.toCentralExtension
        (alternatingSixUniversalCoverTargetSylow 5)
  have htarget :=
    natCard_normalizer_sylowFive_alternatingSix
      (alternatingSixUniversalCoverTargetSylow 5)
  change
    Nat.card
        (Subgroup.normalizer
          (alternatingSixUniversalCoverTargetSylow 5 :
            Set AlternatingSix)) =
      10 at htarget
  rw [← alternatingSixUniversalCoverSylowFive_eq_sylowLift,
    alternatingSixUniversalCentralExtension_ker_eq_center,
    htarget] at h
  exact h

/-- Under the classical order-six Schur-multiplier calculation, the fixed
cover Sylow `5`-normalizer has order sixty. -/
theorem natCard_normalizer_alternatingSixUniversalCoverSylowFive_of_center_eq_six
    (hcenter :
      Nat.card (Subgroup.center AlternatingSixUniversalCover) = 6) :
    Nat.card
        (Subgroup.normalizer
          (alternatingSixUniversalCoverSylow 5 :
            Set AlternatingSixUniversalCover)) =
      60 := by
  rw [natCard_normalizer_alternatingSixUniversalCoverSylowFive,
    hcenter]

end GroupTheory
end McKayConjecture
