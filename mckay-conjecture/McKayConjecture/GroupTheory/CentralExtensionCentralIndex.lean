/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralIndex
import McKayConjecture.GroupTheory.UniversalCentralExtension

/-!
# Central index of a central extension

If `U → S` is a finite central extension, then

`|U : Z(U)| ≤ |S|`.

Indeed, the extension kernel lies in `Z(U)`, so its index is at least the
central index, while the first isomorphism theorem identifies
`U / ker` with `S`.

The strict corollary compares the source with an unrelated ambient finite
group.  This is the central-index descent used for projective central
extensions in Rossi's Lemma 4.1.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace GroupTheory
namespace CentralExtension

variable {U : Type u} {S : Type v}
variable [Group U]
variable [Group S] [Finite S]

/-- The central index of the source of a finite central extension is at
most the cardinality of its target. -/
theorem centralIndex_le_card_target
    (E : CentralExtension U S) :
    centralIndex U ≤ Nat.card S := by
  calc
    centralIndex U =
        (Subgroup.center U).index :=
      centralIndex_eq_center_index U
    _ ≤ E.projection.ker.index :=
      Subgroup.index_antitone E.ker_le_center
    _ = Nat.card (U ⧸ E.projection.ker) :=
      rfl
    _ = Nat.card S :=
      Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective
          E.projection E.surjective).toEquiv

/-- If the finite target is already smaller than the central index of an
unrelated finite ambient group, then so is the source central index. -/
theorem centralIndex_lt_of_card_target_lt
    {G : Type w} [Group G] [Finite G]
    (E : CentralExtension U S)
    (hsmall : Nat.card S < centralIndex G) :
    centralIndex U < centralIndex G :=
  lt_of_le_of_lt E.centralIndex_le_card_target hsmall

end CentralExtension
end GroupTheory
end McKayConjecture
