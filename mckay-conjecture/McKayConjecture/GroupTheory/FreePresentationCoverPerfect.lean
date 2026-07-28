/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.FreePresentationCentralExtension

/-!
# Perfectness of the free-presentation central cover

If `S` is perfect, then `[F,F]/[F,R]` is perfect.  The key subgroup
calculation is

`[F,F] ≤ [F,R] ⊔ [[F,F],[F,F]]`.
-/

noncomputable section

open scoped commutatorElement

universe u

namespace McKayConjecture
namespace GroupTheory
namespace FreePresentation

variable (S : Type u) [Group S]

/-- The subgroup used to prove that the free-presentation cover is
perfect. -/
def perfectnessRelators : Subgroup (Free S) :=
  centralRelators S ⊔
    ⁅derived S, derived S⁆

instance perfectnessRelators_normal :
    (perfectnessRelators S).Normal := by
  unfold perfectnessRelators
  infer_instance

/-- The central relators are contained in the perfectness relators. -/
theorem centralRelators_le_perfectnessRelators :
    centralRelators S ≤ perfectnessRelators S := by
  rw [perfectnessRelators]
  exact le_sup_left

/-- The second derived subgroup is contained in the perfectness
relators. -/
theorem secondDerived_le_perfectnessRelators :
    ⁅derived S, derived S⁆ ≤
      perfectnessRelators S := by
  rw [perfectnessRelators]
  exact le_sup_right

/-- For a perfect target, the relation subgroup and the derived subgroup
generate the free group. -/
theorem relations_sup_derived_eq_top
    (hperfect : Group.IsPerfect S) :
    relations S ⊔ derived S = ⊤ := by
  have hmap :
      (derived S).map (evaluation S) =
        (evaluation S).range := by
    rw [derived, map_commutator_eq,
      MonoidHom.range_eq_top.2
        (evaluation_surjective S)]
    change _root_.commutator S = ⊤
    exact hperfect.commutator_eq_top
  have hcodisjoint :
      Codisjoint (derived S) (relations S) := by
    change
      Codisjoint (derived S)
        (evaluation S).ker
    exact
      Subgroup.map_eq_range_iff.mp hmap
  rw [codisjoint_iff] at hcodisjoint
  simpa [sup_comm] using hcodisjoint

/-- The central relators together with the second derived subgroup
contain the first derived subgroup. -/
theorem derived_le_perfectnessRelators
    (hperfect : Group.IsPerfect S) :
    derived S ≤ perfectnessRelators S := by
  have htop :=
    relations_sup_derived_eq_top S hperfect
  apply
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
  refine ⟨⟨?_⟩⟩
  intro x y
  obtain ⟨f, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (perfectnessRelators S) x
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (perfectnessRelators S) y
  have hf :
      f ∈ relations S ⊔ derived S := by
    rw [htop]
    exact Subgroup.mem_top f
  have hg :
      g ∈ relations S ⊔ derived S := by
    rw [htop]
    exact Subgroup.mem_top g
  obtain ⟨r, hr, d, hd, rfl⟩ :=
    Subgroup.mem_sup_of_normal_right.mp hf
  obtain ⟨s, hs, e, he, rfl⟩ :=
    Subgroup.mem_sup_of_normal_right.mp hg
  let π :=
    QuotientGroup.mk'
      (perfectnessRelators S)
  have hrr :
      Commute (π r) (π s) := by
    apply
      commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    apply
      (QuotientGroup.eq_one_iff
        (⁅r, s⁆ : Free S)).2
    apply
      centralRelators_le_perfectnessRelators S
    exact
      Subgroup.commutator_mem_commutator
        (Subgroup.mem_top _) hs
  have hre :
      Commute (π r) (π e) := by
    apply
      commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    apply
      (QuotientGroup.eq_one_iff
        (⁅r, e⁆ : Free S)).2
    apply
      centralRelators_le_perfectnessRelators S
    rw [centralRelators,
      Subgroup.commutator_comm
        (⊤ : Subgroup (Free S))
        (relations S)]
    exact
      Subgroup.commutator_mem_commutator
        hr (Subgroup.mem_top _)
  have hds :
      Commute (π d) (π s) := by
    apply
      commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    apply
      (QuotientGroup.eq_one_iff
        (⁅d, s⁆ : Free S)).2
    apply
      centralRelators_le_perfectnessRelators S
    exact
      Subgroup.commutator_mem_commutator
        (Subgroup.mem_top _) hs
  have hde :
      Commute (π d) (π e) := by
    apply
      commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    apply
      (QuotientGroup.eq_one_iff
        (⁅d, e⁆ : Free S)).2
    apply
      secondDerived_le_perfectnessRelators S
    exact
      Subgroup.commutator_mem_commutator
        hd he
  change
    Commute (π (r * d)) (π (s * e))
  rw [map_mul, map_mul]
  exact
    (hrr.mul_right hre).mul_left
      (hds.mul_right hde)

/-- The group `[F,F]/[F,R]` is perfect whenever the target is
perfect. -/
theorem cover_isPerfect
    (hperfect : Group.IsPerfect S) :
    Group.IsPerfect (Cover S) := by
  rw [Group.isPerfect_def]
  apply top_unique
  intro u _
  obtain ⟨d, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (centralRelatorsInDerived S) u
  have hdRelators :
      (d : Free S) ∈ perfectnessRelators S :=
    derived_le_perfectnessRelators S hperfect d.2
  obtain ⟨c, hc, k, hk, hck⟩ :=
    Subgroup.mem_sup_of_normal_right.mp hdRelators
  have hcDerived :
      c ∈ derived S :=
    centralRelators_le_derived S hc
  have hkDerived :
      k ∈ derived S :=
    (Subgroup.commutator_le_left
      (derived S) (derived S)) hk
  let cD : derived S := ⟨c, hcDerived⟩
  let kD : derived S := ⟨k, hkDerived⟩
  have hd :
      d = cD * kD := by
    apply Subtype.ext
    exact hck.symm
  rw [hd, map_mul]
  have hcOne :
      QuotientGroup.mk'
          (centralRelatorsInDerived S) cD =
        1 := by
    apply
      (QuotientGroup.eq_one_iff cD).2
    exact hc
  rw [hcOne, one_mul]
  have hkMap :
      k ∈
        (_root_.commutator (derived S)).map
          (derived S).subtype := by
    rw [Subgroup.map_subtype_commutator]
    exact hk
  obtain ⟨k', hk', hk'eq⟩ := hkMap
  have hkDEq : kD = k' := by
    apply Subtype.ext
    exact hk'eq.symm
  rw [hkDEq]
  have hkImage :
      QuotientGroup.mk'
          (centralRelatorsInDerived S) k' ∈
        (_root_.commutator (derived S)).map
          (QuotientGroup.mk'
            (centralRelatorsInDerived S)) :=
    Subgroup.mem_map_of_mem
      (QuotientGroup.mk'
        (centralRelatorsInDerived S)) hk'
  have hmapCommutator :
      (_root_.commutator (derived S)).map
          (QuotientGroup.mk'
            (centralRelatorsInDerived S)) =
        _root_.commutator (Cover S) := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.2
        (QuotientGroup.mk'_surjective
          (centralRelatorsInDerived S))]
    rfl
  rw [hmapCommutator] at hkImage
  exact hkImage

end FreePresentation
end GroupTheory
end McKayConjecture
