/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Nilpotent
import McKayConjecture.Proof.NormalSylow

/-!
# The McKay statement for finite nilpotent groups

Sylow subgroups of a finite nilpotent group are normal, so the normal-Sylow
correspondence applies.
-/

noncomputable section

universe u

namespace McKayConjecture

/-- The McKay statement holds for every finite nilpotent group. -/
theorem Statement.of_nilpotentGroup
    {G : Type u} [Group G] [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    Statement G p P :=
  Statement.of_normal_sylow P

end McKayConjecture
