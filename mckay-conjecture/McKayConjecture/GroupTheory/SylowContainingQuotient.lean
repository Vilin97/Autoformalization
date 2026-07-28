/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.PPrimeCore

/-!
# Quotients by subgroups containing a Sylow subgroup

A quotient by a normal subgroup containing a Sylow `p`-subgroup has order
prime to `p`.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- If a normal subgroup contains a Sylow `p`-subgroup, its ambient
quotient is a `p′`-group. -/
theorem quotient_isPPrimeGroup_of_sylow_le
    (P : Sylow p G)
    (N : Subgroup G) [N.Normal]
    (hPN : (P : Subgroup G) ≤ N) :
    IsPPrimeGroup p (G ⧸ N) := by
  rw [isPPrimeGroup_iff_not_dvd Fact.out]
  change ¬p ∣ N.index
  intro hp
  exact
    P.not_dvd_index
      (hp.trans (Subgroup.index_dvd_of_le hPN))

end GroupTheory
end McKayConjecture
