/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.Quasisimple

/-!
# Nonabelian simple groups are quasisimple

This file supplies the elementary bridge from the simple factors of a
minimal normal subgroup to the quasisimple groups occurring in the
inductive McKay hypothesis.
-/

noncomputable section

open scoped IsMulCommutative

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G]

/-- A nonabelian simple group is centerless. -/
theorem center_eq_bot_of_isSimpleGroup
    (hs : IsSimpleGroup G)
    (hnoncomm : ¬ IsMulCommutative G) :
    Subgroup.center G = ⊥ := by
  letI := hs
  rcases
      (inferInstance :
        (Subgroup.center G).Normal).eq_bot_or_eq_top with
    hbot | htop
  · exact hbot
  · exact
      (hnoncomm
        (Subgroup.center_eq_top_iff.mp htop)).elim

/-- A nonabelian simple group is perfect. -/
theorem isPerfect_of_isSimpleGroup
    (hs : IsSimpleGroup G)
    (hnoncomm : ¬ IsMulCommutative G) :
    Group.IsPerfect G := by
  letI := hs
  rcases
      (inferInstance :
        (_root_.commutator G).Normal).eq_bot_or_eq_top with
    hbot | htop
  · exact
      (hnoncomm
        ((_root_.commutator_eq_bot_iff G).mp hbot)).elim
  · exact Group.isPerfect_def.mpr htop

/-- Every nonabelian simple group is quasisimple. -/
theorem isQuasisimple_of_isSimpleGroup
    (hs : IsSimpleGroup G)
    (hnoncomm : ¬ IsMulCommutative G) :
    IsQuasisimple G where
  isPerfect :=
    isPerfect_of_isSimpleGroup hs hnoncomm
  isSimpleGroup_quotient := by
    letI := hs
    let hcenter :
        Subgroup.center G = ⊥ :=
      center_eq_bot_of_isSimpleGroup hs hnoncomm
    exact
      ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
        QuotientGroup.quotientBot).isSimpleGroup

end GroupTheory
end McKayConjecture
