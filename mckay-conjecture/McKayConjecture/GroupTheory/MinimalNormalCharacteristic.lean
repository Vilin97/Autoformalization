/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Subgroup.Center
import McKayConjecture.GroupTheory.MinimalNormal

/-!
# Characteristic simplicity of minimal normal subgroups

A minimal normal subgroup has no proper nontrivial characteristic subgroup.
Consequently its nonabelian branch is both perfect and centerless.  These are
the first intrinsic structural facts used when the reduction passes from a
minimal normal subgroup to its nonabelian simple factors.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

open scoped IsMulCommutative

variable {G : Type u} [Group G]

namespace IsMinimalNormal

variable {N : Subgroup G}

/-- Every characteristic subgroup of a minimal normal subgroup is trivial or
the whole subgroup. -/
theorem characteristic_eq_bot_or_top
    (hN : IsMinimalNormal N)
    (K : Subgroup N) [K.Characteristic] :
    K = ⊥ ∨ K = ⊤ := by
  letI : N.Normal := hN.normal
  have hmapNormal : (K.map N.subtype).Normal :=
    inferInstance
  have hmapLe : K.map N.subtype ≤ N := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := hg
    exact x.property
  rcases hN.eq_bot_or_eq hmapNormal hmapLe with hbot | htop
  · exact Or.inl
      ((K.map_eq_bot_iff_of_injective
        (f := N.subtype) Subtype.coe_injective).mp hbot)
  · right
    apply Subgroup.map_injective
      (f := N.subtype) Subtype.coe_injective
    calc
      K.map N.subtype = N := htop
      _ = (⊤ : Subgroup N).map N.subtype := by
        rw [← MonoidHom.range_eq_map, N.range_subtype]

/-- A subgroup of a minimal normal subgroup which is invariant under every
ambient conjugation is trivial or the whole subgroup. -/
theorem eq_bot_or_top_of_conj_invariant
    [N.Normal]
    (hN : IsMinimalNormal N)
    (K : Subgroup N)
    (hinvariant :
      ∀ (g : G) (x : N), x ∈ K →
        MulAut.conjNormal g x ∈ K) :
    K = ⊥ ∨ K = ⊤ := by
  have hmapNormal : (K.map N.subtype).Normal := by
    constructor
    intro x hx g
    obtain ⟨y, hy, rfl⟩ := hx
    let z : N := MulAut.conjNormal g y
    refine ⟨z, hinvariant g y hy, ?_⟩
    rfl
  have hmapLe : K.map N.subtype ≤ N := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := hg
    exact x.property
  rcases hN.eq_bot_or_eq hmapNormal hmapLe with hbot | htop
  · exact Or.inl
      ((K.map_eq_bot_iff_of_injective
        (f := N.subtype) Subtype.coe_injective).mp hbot)
  · right
    apply Subgroup.map_injective
      (f := N.subtype) Subtype.coe_injective
    calc
      K.map N.subtype = N := htop
      _ = (⊤ : Subgroup N).map N.subtype := by
        rw [← MonoidHom.range_eq_map, N.range_subtype]

/-- A nonabelian minimal normal subgroup has trivial center. -/
theorem center_eq_bot_of_not_isMulCommutative
    (hN : IsMinimalNormal N)
    (hnoncomm : ¬ IsMulCommutative N) :
    Subgroup.center N = ⊥ := by
  rcases hN.characteristic_eq_bot_or_top
      (Subgroup.center N) with hbot | htop
  · exact hbot
  · exact (hnoncomm
      (Subgroup.center_eq_top_iff.mp htop)).elim

/-- A nonabelian minimal normal subgroup is perfect. -/
theorem isPerfect_of_not_isMulCommutative
    (hN : IsMinimalNormal N)
    (hnoncomm : ¬ IsMulCommutative N) :
    Group.IsPerfect N := by
  rcases hN.characteristic_eq_bot_or_top
      (commutator N) with hbot | htop
  · exact (hnoncomm
      ((commutator_eq_bot_iff N).mp hbot)).elim
  · exact Group.isPerfect_def.mpr htop

end IsMinimalNormal

end GroupTheory
end McKayConjecture
