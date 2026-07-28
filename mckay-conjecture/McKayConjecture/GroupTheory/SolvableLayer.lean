/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.Component

/-!
# The layer of a solvable group

A component is nontrivial and perfect, whereas every subgroup of a
solvable group is solvable.  Consequently a solvable group has no
components and its layer is trivial.

No finiteness assumption is needed for these statements.
-/

noncomputable section

universe u

namespace McKayConjecture.GroupTheory

variable {G : Type u} [Group G] [Group.IsSolvable G]

/-- A solvable group has no components. -/
theorem not_isComponent_of_isSolvable
    (K : Subgroup G) :
    ¬IsComponent K := by
  intro hK
  letI : Nontrivial K :=
    hK.isQuasisimple.nontrivial
  letI : Group.IsPerfect K :=
    hK.isQuasisimple.isPerfect
  exact
    Group.IsPerfect.not_isSolvable K
      (inferInstance : Group.IsSolvable K)

/-- The layer of a solvable group is trivial. -/
theorem layer_eq_bot_of_isSolvable :
    layer G = ⊥ := by
  apply le_bot_iff.mp
  apply layer_le
  intro K hK
  exact False.elim
    (not_isComponent_of_isSolvable K hK)

end McKayConjecture.GroupTheory
