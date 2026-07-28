/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetCentralExtension

/-!
# Solvability of factor-set central extensions

A normalized factor set with solvable base and coefficient groups produces
a solvable central extension.  This is the closure fact needed when the
canonical factor-extension construction is used inside a solvable-group
central-index induction.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet
namespace CentralExtensionGroup

variable {G : Type u} {A : Type v}
variable [Group G] [CommGroup A]
variable [Group.IsSolvable G] [Group.IsSolvable A]
variable (α : FactorSet G A) (hα : α.IsNormalized)

/-- A factor-set central extension of solvable groups is solvable. -/
instance instIsSolvable :
    Group.IsSolvable (CentralExtensionGroup α hα) :=
  Group.isSolvable_of_ker_le_range
    (coefficientEmbedding α hα)
    (projection α hα)
    (by
      rw [projection_ker_eq_coefficientEmbedding_range])

end CentralExtensionGroup
end FactorSet
end CharacterTriple
end McKayConjecture
