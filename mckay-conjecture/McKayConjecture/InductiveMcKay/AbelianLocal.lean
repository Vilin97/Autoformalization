/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NumericalReduction

/-!
# Local correspondences for finite abelian groups

Every subgroup of an abelian group is normal.  In particular every Sylow
subgroup is normal, so the full group is a valid (base-case) intermediate
subgroup for the numerical local correspondence.
-/

noncomputable section

open scoped IsMulCommutative

universe u

namespace McKayConjecture
namespace InductiveMcKay
namespace LocalCorrespondence

variable {G : Type u} [Group G] {p : ℕ}

/-- The canonical local correspondence for a group whose multiplication is
commutative. -/
def of_isMulCommutative
    (hG : IsMulCommutative G)
    (P : Sylow p G) :
    LocalCorrespondence P := by
  letI : IsMulCommutative G := hG
  letI : (P : Subgroup G).Normal := inferInstance
  exact LocalCorrespondence.of_normal_sylow P

/-- Specialization to a `CommGroup`. -/
def of_commGroup
    {G : Type u} [CommGroup G]
    (P : Sylow p G) :
    LocalCorrespondence P :=
  of_isMulCommutative inferInstance P

end LocalCorrespondence
end InductiveMcKay
end McKayConjecture
