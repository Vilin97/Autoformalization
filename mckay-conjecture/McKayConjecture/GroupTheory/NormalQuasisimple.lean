/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.IsSubnormal
import McKayConjecture.GroupTheory.Quasisimple

/-!
# Normal quasisimple subgroups

The elementary component argument needed by the generalized Fitting theory
starts with a normal quasisimple subgroup.  Such a subgroup is either
contained in a second normal subgroup or centralizes it.  The proof uses
quasisimplicity to make the intersection central and the three-subgroups
lemma to exploit perfectness.
-/

noncomputable section

universe u

namespace McKayConjecture.GroupTheory

open scoped commutatorElement

variable {G : Type u} [Group G]

namespace IsQuasisimple

/-- Every proper subnormal subgroup of a quasisimple group is central. -/
theorem subnormal_le_center
    {H : Subgroup G}
    (hGq : IsQuasisimple G)
    (hH : H.IsSubnormal) (hHtop : H ≠ ⊤) :
    H ≤ Subgroup.center G := by
  obtain ⟨N, hNnormal, hHN, hNproper⟩ :=
    hH.exists_normal_and_le_and_lt_top_of_ne hHtop
  exact hHN.trans
    (hGq.normal_le_center hNnormal hNproper.ne)

/-- A proper subnormal subgroup of a quasisimple group commutes with the
whole group. -/
theorem commutator_top_subnormal_eq_bot
    {H : Subgroup G}
    (hGq : IsQuasisimple G)
    (hH : H.IsSubnormal) (hHtop : H ≠ ⊤) :
    ⁅(⊤ : Subgroup G), H⁆ = ⊥ := by
  rw [Subgroup.commutator_top_left_eq_bot_iff_le_center]
  exact hGq.subnormal_le_center hH hHtop

/-- If a quasisimple normal subgroup is not contained in another normal
subgroup, their intersection is central in the quasisimple subgroup. -/
theorem inf_le_centralizer_of_normal
    {K N : Subgroup G}
    (hKq : IsQuasisimple K)
    (hKn : K.Normal) (hNn : N.Normal)
    (hnle : ¬K ≤ N) :
    K ⊓ N ≤ Subgroup.centralizer (K : Set G) := by
  let I : Subgroup K := (K ⊓ N).subgroupOf K
  letI : (K ⊓ N).Normal := inferInstance
  letI : I.Normal := inferInstance
  have hIne : I ≠ ⊤ := by
    intro htop
    apply hnle
    intro k hk
    let x : K := ⟨k, hk⟩
    have hxI : x ∈ I := by
      rw [htop]
      exact Subgroup.mem_top x
    exact hxI.2
  have hIcenter : I ≤ Subgroup.center K :=
    hKq.normal_le_center inferInstance hIne
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  let zK : K := ⟨z, hz.1⟩
  have hzI : zK ∈ I := hz
  have hzcenter : zK ∈ Subgroup.center K :=
    hIcenter hzI
  have hcomm :
      (⟨k, hk⟩ : K) * zK =
        zK * (⟨k, hk⟩ : K) := by
    exact (Subgroup.mem_center_iff.mp hzcenter
      ⟨k, hk⟩)
  exact congrArg Subtype.val hcomm

/-- A normal quasisimple subgroup is either contained in a normal subgroup
or centralizes it. -/
theorem commutator_eq_bot_of_normal
    {K N : Subgroup G}
    (hKq : IsQuasisimple K)
    (hKn : K.Normal) (hNn : N.Normal)
    (hnle : ¬K ≤ N) :
    ⁅K, N⁆ = ⊥ := by
  letI : K.Normal := hKn
  letI : N.Normal := hNn
  have hcentral :
      K ⊓ N ≤ Subgroup.centralizer (K : Set G) :=
    hKq.inf_le_centralizer_of_normal hKn hNn hnle
  have hKNcentral :
      ⁅K, N⁆ ≤ Subgroup.centralizer (K : Set G) :=
    (Subgroup.commutator_le_inf (H₁ := K) (H₂ := N)).trans
      hcentral
  have hfirst : ⁅⁅K, N⁆, K⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      hKNcentral
  have hsecond : ⁅⁅N, K⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_comm N K]
    exact hfirst
  have hperfect : Group.IsPerfect K := hKq.isPerfect
  have hthree : ⁅⁅K, K⁆, N⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate
      (H₁ := K) (H₂ := K) (H₃ := N) hfirst hsecond
  rwa [@Subgroup.commutator_eq_self G _ K hperfect] at hthree

/-- Elementwise form: a normal quasisimple subgroup not contained in a
normal subgroup commutes with it. -/
theorem commute_of_normal
    {K N : Subgroup G}
    (hKq : IsQuasisimple K)
    (hKn : K.Normal) (hNn : N.Normal)
    (hnle : ¬K ≤ N)
    {k n : G} (hk : k ∈ K) (hn : n ∈ N) :
    Commute k n := by
  change k * n = n * k
  rw [← commutatorElement_eq_one_iff_mul_comm]
  have hmem :
      ⁅k, n⁆ ∈ ⁅K, N⁆ :=
    Subgroup.commutator_mem_commutator hk hn
  rw [hKq.commutator_eq_bot_of_normal hKn hNn hnle,
    Subgroup.mem_bot] at hmem
  exact hmem

end IsQuasisimple
end McKayConjecture.GroupTheory
