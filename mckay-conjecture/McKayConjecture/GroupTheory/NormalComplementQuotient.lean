/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Complement

/-!
# Quotients by a normal factor with a chosen complement

If a normal subgroup `N` and a disjoint subgroup `H` generate a group,
multiplication makes `H` a complement of `N`; hence the quotient by `N`
is canonically isomorphic to `H`.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

variable {G : Type} [Group G]

/-- A disjoint generating subgroup is a complement to a normal subgroup. -/
theorem isComplement'_of_normal_disjoint_sup_eq_top
    (N H : Subgroup G) [N.Normal]
    (hdisjoint : Disjoint H N)
    (hsup : N ⊔ H = ⊤) :
    H.IsComplement' N := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjoint
  rw [← Subgroup.mul_normal H N]
  rw [sup_comm, hsup]
  rfl

/-- The quotient by a normal factor is the chosen disjoint generating
complement. -/
def normalComplementQuotientEquiv
    (N H : Subgroup G) [N.Normal]
    (hdisjoint : Disjoint H N)
    (hsup : N ⊔ H = ⊤) :
    G ⧸ N ≃* H :=
  (isComplement'_of_normal_disjoint_sup_eq_top
    N H hdisjoint hsup).QuotientMulEquiv

end GroupTheory
end McKayConjecture
