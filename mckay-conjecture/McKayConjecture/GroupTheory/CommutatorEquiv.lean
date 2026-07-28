/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-!
# Centers and commutator subgroups under group equivalences

This file packages the elementary transport facts for the two characteristic
subgroups used in extraspecial-group arguments.  A multiplicative
equivalence maps the center onto the center and the commutator subgroup onto
the commutator subgroup, hence restricts to equivalences on both.
-/

noncomputable section

universe u v

namespace MulEquiv

variable {G : Type u} {H : Type v}
variable [Group G] [Group H]

/-- A group equivalence maps the center onto the center. -/
theorem map_center_eq (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom =
      Subgroup.center H := by
  ext y
  rw [Subgroup.mem_map_equiv]
  exact MulEquivClass.apply_mem_center_iff e.symm

/-- A group equivalence maps the commutator subgroup onto the commutator
subgroup. -/
theorem map_commutator_eq (e : G ≃* H) :
    (_root_.commutator G).map e.toMonoidHom =
      _root_.commutator H := by
  rw [_root_.map_commutator_eq,
    MonoidHom.range_eq_top.mpr e.surjective]
  rfl

/-- The commutator subgroups of equivalent groups are equivalent. -/
def commutatorCongr (e : G ≃* H) :
    _root_.commutator G ≃*
      _root_.commutator H :=
  (e.subgroupMap (_root_.commutator G)).trans
    (MulEquiv.subgroupCongr e.map_commutator_eq)

/-- Equality of the commutator subgroup and center is invariant under group
equivalence. -/
theorem commutator_eq_center_iff (e : G ≃* H) :
    _root_.commutator G = Subgroup.center G ↔
      _root_.commutator H = Subgroup.center H := by
  constructor
  · intro h
    rw [← e.map_commutator_eq, ← e.map_center_eq, h]
  · intro h
    rw [← e.symm.map_commutator_eq,
      ← e.symm.map_center_eq, h]

end MulEquiv
