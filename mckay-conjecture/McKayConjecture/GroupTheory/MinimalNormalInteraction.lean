/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Subgroup.Centralizer
import McKayConjecture.GroupTheory.MinimalNormal
import McKayConjecture.GroupTheory.PCore

/-!
# Interactions of minimal normal subgroups with normal subgroups

A minimal normal subgroup is either contained in a given normal subgroup or
is disjoint from it.  In the disjoint branch the two normal subgroups
centralize one another.  The specialization to `O_p(G)` is used repeatedly
in minimal-counterexample reductions.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G]

namespace IsMinimalNormal

variable {N K : Subgroup G}

/-- A minimal normal subgroup is either contained in a normal subgroup or
disjoint from it. -/
theorem le_or_disjoint_of_normal
    (hN : IsMinimalNormal N)
    (hK : K.Normal) :
    N ≤ K ∨ Disjoint N K := by
  letI : N.Normal := hN.normal
  letI : K.Normal := hK
  rcases hN.eq_bot_or_eq
      (M := N ⊓ K) inferInstance inf_le_left with
    hbot | hwhole
  · exact Or.inr (by
      rw [disjoint_iff]
      exact hbot)
  · exact Or.inl
      (hwhole ▸ inf_le_right)

/-- If a minimal normal subgroup is not contained in a normal subgroup, then
the two subgroups are disjoint. -/
theorem disjoint_of_normal_of_not_le
    (hN : IsMinimalNormal N)
    (hK : K.Normal)
    (hnle : ¬ N ≤ K) :
    Disjoint N K :=
  (hN.le_or_disjoint_of_normal hK).resolve_left hnle

/-- If a minimal normal subgroup is not contained in a normal subgroup, then
it centralizes that subgroup. -/
theorem le_centralizer_of_normal_of_not_le
    (hN : IsMinimalNormal N)
    (hK : K.Normal)
    (hnle : ¬ N ≤ K) :
    N ≤ Subgroup.centralizer (K : Set G) := by
  have hdis : Disjoint N K :=
    hN.disjoint_of_normal_of_not_le hK hnle
  intro x hx y hy
  exact (Subgroup.commute_of_normal_of_disjoint
    N K hN.normal hK hdis x y hx hy).eq.symm

/-- A minimal normal `p`-subgroup lies in `O_p(G)`. -/
theorem le_pCore
    (hN : IsMinimalNormal N)
    {p : ℕ}
    (hpN : IsPGroup p N) :
    N ≤ pCore p G :=
  GroupTheory.le_pCore hpN hN.normal

/-- A minimal normal subgroup which is not a `p`-group is disjoint from
`O_p(G)`. -/
theorem disjoint_pCore_of_not_isPGroup
    (hN : IsMinimalNormal N)
    {p : ℕ}
    (hpN : ¬ IsPGroup p N) :
    Disjoint N (pCore p G) := by
  apply hN.disjoint_of_normal_of_not_le inferInstance
  intro hle
  exact hpN (pCore_isPGroup.to_le hle)

/-- A minimal normal subgroup which is not a `p`-group centralizes
`O_p(G)`. -/
theorem le_centralizer_pCore_of_not_isPGroup
    (hN : IsMinimalNormal N)
    {p : ℕ}
    (hpN : ¬ IsPGroup p N) :
    N ≤ Subgroup.centralizer (pCore p G : Set G) := by
  apply hN.le_centralizer_of_normal_of_not_le inferInstance
  intro hle
  exact hpN (pCore_isPGroup.to_le hle)

end IsMinimalNormal

end GroupTheory
end McKayConjecture
