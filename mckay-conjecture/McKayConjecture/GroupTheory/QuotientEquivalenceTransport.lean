/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Quotient equivalences from commuting subgroup equivalences

An equivalence of ambient groups together with an equivalence of normal
subgroups in a commuting square induces the expected equivalence of quotient
groups.  The formula on quotient classes is recorded explicitly for use in
character-transport calculations.
-/

namespace McKayConjecture
namespace GroupTheory

universe u₁ u₂

variable {G : Type u₁} {G' : Type u₂}
variable [Group G] [Group G']
variable {N : Subgroup G} {N' : Subgroup G'}
variable [N.Normal] [N'.Normal]

omit [N.Normal] [N'.Normal] in
private theorem subgroup_le_comap_of_commuting_equiv
    (eG : G' ≃* G)
    (eN : N' ≃* N)
    (hcomm :
      eG.toMonoidHom.comp N'.subtype =
        N.subtype.comp eN.toMonoidHom) :
    N' ≤ N.comap eG.toMonoidHom := by
  intro g hg
  let n' : N' := ⟨g, hg⟩
  have hpoint :=
    congrArg (fun f : N' →* G ↦ f n') hcomm
  change eG g = (eN n' : N) at hpoint
  change eG g ∈ N
  rw [hpoint]
  exact (eN n').property

omit [N.Normal] [N'.Normal] in
private theorem subgroup_le_comap_symm_of_commuting_equiv
    (eG : G' ≃* G)
    (eN : N' ≃* N)
    (hcomm :
      eG.toMonoidHom.comp N'.subtype =
        N.subtype.comp eN.toMonoidHom) :
    N ≤ N'.comap eG.symm.toMonoidHom := by
  intro g hg
  let n : N := ⟨g, hg⟩
  let n' : N' := eN.symm n
  have hpoint :=
    congrArg (fun f : N' →* G ↦ f n') hcomm
  have hpoint' :
      eG (n' : G') = (eN n' : N) :=
    hpoint
  have hen : eN n' = n :=
    eN.apply_symm_apply n
  have hpoint'' : eG (n' : G') = g := by
    rw [hpoint', hen]
  change eG.symm g ∈ N'
  have heq : eG.symm g = (n' : G') := by
    apply eG.injective
    rw [eG.apply_symm_apply, hpoint'']
  rw [heq]
  exact n'.property

/-- A commuting equivalence of ambient groups and normal subgroups induces
an equivalence of quotient groups. -/
def quotientMulEquivOfSubgroupEquiv
    (eG : G' ≃* G)
    (eN : N' ≃* N)
    (hcomm :
      eG.toMonoidHom.comp N'.subtype =
        N.subtype.comp eN.toMonoidHom) :
    (G' ⧸ N') ≃* (G ⧸ N) where
  toFun :=
    QuotientGroup.map N' N eG.toMonoidHom
      (subgroup_le_comap_of_commuting_equiv
        eG eN hcomm)
  invFun :=
    QuotientGroup.map N N' eG.symm.toMonoidHom
      (subgroup_le_comap_symm_of_commuting_equiv
        eG eN hcomm)
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro g
    change
      QuotientGroup.mk' N' (eG.symm (eG g)) =
        QuotientGroup.mk' N' g
    rw [eG.symm_apply_apply]
  right_inv q := by
    refine Quotient.inductionOn' q ?_
    intro g
    change
      QuotientGroup.mk' N (eG (eG.symm g)) =
        QuotientGroup.mk' N g
    rw [eG.apply_symm_apply]
  map_mul' x y :=
    map_mul
      (QuotientGroup.map N' N eG.toMonoidHom
        (subgroup_le_comap_of_commuting_equiv
          eG eN hcomm)) x y

@[simp]
theorem quotientMulEquivOfSubgroupEquiv_mk
    (eG : G' ≃* G)
    (eN : N' ≃* N)
    (hcomm :
      eG.toMonoidHom.comp N'.subtype =
        N.subtype.comp eN.toMonoidHom)
    (g : G') :
    quotientMulEquivOfSubgroupEquiv eG eN hcomm
        (QuotientGroup.mk' N' g) =
      QuotientGroup.mk' N (eG g) :=
  rfl

end GroupTheory
end McKayConjecture
