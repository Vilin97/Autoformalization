/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.Atoms.Finite

/-!
# A cyclic chief step in a finite `p`-group

Every nontrivial finite `p`-group has a maximal subgroup.  Nilpotence
makes every maximal subgroup normal, and the corresponding quotient is
a simple `p`-group.  A simple nilpotent group is cyclic, so this gives a
normal proper subgroup with cyclic `p`-group quotient.

This is the induction step needed to iterate cyclic-quotient character
constructions through an arbitrary finite `p`-group.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- A normal subgroup bundled so that its quotient group is available in
dependent outputs. -/
structure NormalSubgroupData (G : Type u) [Group G] where
  /-- The underlying subgroup. -/
  toSubgroup : Subgroup G
  /-- Normality of the underlying subgroup. -/
  normal : toSubgroup.Normal

instance (N : NormalSubgroupData G) :
    N.toSubgroup.Normal :=
  N.normal

omit [Finite G] in
/-- The quotient by a normal maximal subgroup is simple. -/
theorem isSimpleGroup_quotient_of_isCoatom
    (N : Subgroup G) [N.Normal]
    (hN : IsCoatom N) :
    IsSimpleGroup (G ⧸ N) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hq : Function.Surjective q :=
    QuotientGroup.mk'_surjective N
  letI : Nontrivial (G ⧸ N) :=
    QuotientGroup.nontrivial_iff.mpr hN.ne_top
  exact
    { eq_bot_or_eq_top_of_normal := fun H _hH ↦ by
        have hNcomap : N ≤ H.comap q := by
          intro x hx
          change q x ∈ H
          have hxOne : q x = 1 :=
            (QuotientGroup.eq_one_iff x).mpr hx
          rw [hxOne]
          exact H.one_mem
        rcases hN.le_iff.mp hNcomap with htop | hNself
        · right
          rw [← Subgroup.map_comap_eq_self_of_surjective
            hq H, htop,
            Subgroup.map_top_of_surjective q hq]
        · left
          rw [← Subgroup.map_comap_eq_self_of_surjective
            hq H, hNself,
            QuotientGroup.map_mk'_self N] }

/-- A nontrivial finite `p`-group has a normal maximal subgroup whose
quotient is again a `p`-group and is cyclic. -/
theorem IsPGroup.exists_normal_isCoatom_cyclic_quotient
    (hG : IsPGroup p G)
    [Nontrivial G] :
    ∃ N : NormalSubgroupData G,
      IsCoatom N.toSubgroup ∧
        IsPGroup p (G ⧸ N.toSubgroup) ∧
          IsCyclic (G ⧸ N.toSubgroup) := by
  haveI : Nontrivial (Subgroup G) := by
    exact ⟨⊥, ⊤, bot_ne_top⟩
  obtain ⟨N, hNcoatom⟩ :=
    IsCoatomic.exists_coatom (Subgroup G)
  letI : Group.IsNilpotent G :=
    hG.isNilpotent
  have hNnormal : N.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom
      N Group.normalizerCondition_of_isNilpotent hNcoatom
  letI : N.Normal := hNnormal
  have hquotientP :
      IsPGroup p (G ⧸ N) :=
    hG.of_surjective
      (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
  letI : Nontrivial (G ⧸ N) :=
    QuotientGroup.nontrivial_iff.mpr hNcoatom.ne_top
  letI : IsSimpleGroup (G ⧸ N) :=
    isSimpleGroup_quotient_of_isCoatom N hNcoatom
  letI : Group.IsNilpotent (G ⧸ N) :=
    hquotientP.isNilpotent
  let bundled : NormalSubgroupData G :=
    ⟨N, hNnormal⟩
  exact
    ⟨bundled, hNcoatom, hquotientP,
      inferInstance⟩

/-- Convenient properness form of the cyclic quotient step. -/
theorem IsPGroup.exists_normal_lt_top_cyclic_quotient
    (hG : IsPGroup p G)
    [Nontrivial G] :
    ∃ N : NormalSubgroupData G,
      N.toSubgroup < ⊤ ∧
        IsPGroup p (G ⧸ N.toSubgroup) ∧
          IsCyclic (G ⧸ N.toSubgroup) := by
  obtain ⟨N, hNcoatom, hNP, hNcyclic⟩ :=
    McKayConjecture.GroupTheory.IsPGroup.exists_normal_isCoatom_cyclic_quotient
      hG
  exact
    ⟨N, hNcoatom.lt_top,
      hNP, hNcyclic⟩

/-- The cyclic quotient step is strictly smaller on the kernel side, and
the kernel remains a `p`-group.  This is the form suited to strong
induction on group order. -/
theorem IsPGroup.exists_normal_card_lt_cyclic_quotient
    (hG : IsPGroup p G)
    [Nontrivial G] :
    ∃ N : NormalSubgroupData G,
      Nat.card N.toSubgroup < Nat.card G ∧
        IsPGroup p N.toSubgroup ∧
          IsPGroup p (G ⧸ N.toSubgroup) ∧
            IsCyclic (G ⧸ N.toSubgroup) := by
  obtain ⟨N, hNlt, hNquotientP, hNcyclic⟩ :=
    McKayConjecture.GroupTheory.IsPGroup.exists_normal_lt_top_cyclic_quotient
      hG
  obtain ⟨x, _hxTop, hxN⟩ :=
    SetLike.exists_of_lt hNlt
  have hcard :
      Nat.card N.toSubgroup < Nat.card G :=
    Finite.card_subtype_lt hxN
  exact
    ⟨N, hcard, hG.to_subgroup N.toSubgroup,
      hNquotientP, hNcyclic⟩

end GroupTheory
end McKayConjecture
