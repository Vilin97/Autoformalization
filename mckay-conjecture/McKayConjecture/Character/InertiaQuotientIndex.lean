/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordEquivalence

/-!
# The quotient index of an inertia group

For `N ◁ G` and `θ ∈ Irr(N)`, the canonical copy of `N` in
`I_G(θ)` has quotient cardinality at most that of `G / N`.  This is the
elementary index estimate used to bound the finite factor extension
attached to the inertia triple.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordEquivalence

variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal]
variable (θ : IrreducibleCharacter N)

/-- The quotient of an inertia group by the canonical normal copy has
cardinality at most the ambient quotient. -/
theorem card_inertia_quotient_le_card_ambient_quotient :
    Nat.card
        (IrreducibleCharacter.inertia N θ ⧸
          inertiaNormalCopy N θ) ≤
      Nat.card (G ⧸ N) := by
  change
    N.relIndex (IrreducibleCharacter.inertia N θ) ≤
      N.index
  exact
    Nat.le_of_dvd
      (Nat.pos_of_ne_zero N.index_ne_zero_of_finite)
      (Subgroup.relIndex_dvd_index_of_le
        (IrreducibleCharacter.subgroup_le_inertia N θ))

end CliffordEquivalence
end McKayConjecture
