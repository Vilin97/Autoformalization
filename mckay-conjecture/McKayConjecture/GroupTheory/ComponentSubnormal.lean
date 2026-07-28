/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.Component

/-!
# Components inside subnormal subgroups

Components are stable when passing between a subnormal subgroup and the
ambient group.  More precisely, the components of a subnormal subgroup are
exactly the ambient components contained in it.  These transport lemmas are
the bookkeeping core of the standard proof that distinct components commute.
-/

noncomputable section

universe u

namespace McKayConjecture.GroupTheory

variable {G : Type u} [Group G]

/-- A proper subnormal subgroup has a proper normal closure. -/
theorem normalClosure_lt_top_of_isSubnormal
    {K : Subgroup G} (hK : K.IsSubnormal)
    (hKtop : K ≠ ⊤) :
    Subgroup.normalClosure (K : Set G) < ⊤ := by
  obtain ⟨N, hNnormal, hKN, hNproper⟩ :=
    hK.exists_normal_and_le_and_lt_top_of_ne hKtop
  have hclosure :
      Subgroup.normalClosure (K : Set G) ≤ N :=
    Subgroup.normalClosure_le_normal hKN
  exact hclosure.trans_lt hNproper

namespace IsComponent

/-- A component of a subnormal subgroup is a component of the ambient
group. -/
theorem map_subtype
    {H : Subgroup G} {K : Subgroup H}
    (hK : IsComponent K) (hH : H.IsSubnormal) :
    IsComponent (K.map H.subtype) := by
  refine ⟨hK.isSubnormal.trans' hH, ?_⟩
  exact IsQuasisimple.of_mulEquiv
    (K.equivMapOfInjective H.subtype H.subtype_injective)
    hK.isQuasisimple

/-- An ambient component contained in a subgroup remains a component when
viewed inside that subgroup. -/
theorem subgroupOf
    {K H : Subgroup G} (hK : IsComponent K)
    (hKH : K ≤ H) :
    IsComponent (K.subgroupOf H) := by
  refine ⟨hK.isSubnormal.subgroupOf, ?_⟩
  exact IsQuasisimple.of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hKH).symm
    hK.isQuasisimple

/-- A component contained in a subnormal subgroup is one of that
subgroup's components. -/
theorem componentOf_subnormal_iff
    {H : Subgroup G} (hH : H.IsSubnormal)
    (K : Subgroup H) :
    IsComponent K ↔
      IsComponent (K.map H.subtype) := by
  constructor
  · intro hK
    exact hK.map_subtype hH
  · intro hK
    have hle :
        K.map H.subtype ≤ H :=
      Subgroup.map_subtype_le K
    have hsub :
        IsComponent
          ((K.map H.subtype).subgroupOf H) :=
      hK.subgroupOf hle
    have heq :
        (K.map H.subtype).subgroupOf H = K := by
      ext x
      constructor
      · intro hx
        change (x : G) ∈ K.map H.subtype at hx
        obtain ⟨y, hy, hxy⟩ := hx
        have hyx : y = x := Subtype.ext hxy
        rwa [hyx] at hy
      · intro hx
        change (x : G) ∈ K.map H.subtype
        exact ⟨x, hx, rfl⟩
    rwa [heq] at hsub

/-- A proper component has a proper normal closure. -/
theorem normalClosure_lt_top
    {K : Subgroup G} (hK : IsComponent K)
    (hKtop : K ≠ ⊤) :
    Subgroup.normalClosure (K : Set G) < ⊤ :=
  normalClosure_lt_top_of_isSubnormal hK.isSubnormal hKtop

/-- Every subgroup is contained in its normal closure. -/
theorem le_normalClosure_self
    {K : Subgroup G} :
    K ≤ Subgroup.normalClosure (K : Set G) :=
  Subgroup.subset_normalClosure

/-- A component remains a component inside its normal closure. -/
theorem component_normalClosure
    {K : Subgroup G} (hK : IsComponent K) :
    IsComponent
      (K.subgroupOf (Subgroup.normalClosure (K : Set G))) :=
  hK.subgroupOf le_normalClosure_self

end IsComponent
end McKayConjecture.GroupTheory
