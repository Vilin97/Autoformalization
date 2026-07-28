/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import McKayConjecture.GroupTheory.CentralIndex

/-!
# Central index of a quotient

For a normal subgroup `K ⫳ G`, the image of `Z(G)` is contained in
`Z(G/K)`.  It follows that the central index of `G/K` is bounded above
by `|G/(K Z(G))|`.  When `K` is noncentral, this is strictly smaller
than the central index of `G`.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G]

/-- The image of the ambient center in a quotient is central. -/
theorem map_center_quotient_le_center
    (K : Subgroup G) [K.Normal] :
    (Subgroup.center G).map
        (QuotientGroup.mk' K) ≤
      Subgroup.center (G ⧸ K) := by
  rintro q ⟨z, hz, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro x
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective K x
  simpa only [map_mul] using
    congrArg (QuotientGroup.mk' K)
      (Subgroup.mem_center_iff.mp hz g)

/-- The index of the image of `Z(G)` in `G/K` is the index of
`K Z(G)` in `G`. -/
theorem index_map_center_quotient
    (K : Subgroup G) [K.Normal] :
    ((Subgroup.center G).map
        (QuotientGroup.mk' K)).index =
      (K ⊔ Subgroup.center G).index := by
  rw [Subgroup.index_map,
    QuotientGroup.ker_mk',
    QuotientGroup.range_mk',
    Subgroup.index_top,
    mul_one,
    sup_comm]

/-- The central index of a quotient is at most the cardinality of
`G/(K Z(G))`. -/
theorem centralIndex_quotient_le_card_quotient_sup_center
    [Finite G]
    (K : Subgroup G) [K.Normal] :
    centralIndex (G ⧸ K) ≤
      Nat.card
        (G ⧸ (K ⊔ Subgroup.center G)) := by
  calc
    centralIndex (G ⧸ K) =
        (Subgroup.center (G ⧸ K)).index :=
      centralIndex_eq_center_index (G ⧸ K)
    _ ≤
        ((Subgroup.center G).map
          (QuotientGroup.mk' K)).index :=
      Subgroup.index_antitone
        (map_center_quotient_le_center K)
    _ = (K ⊔ Subgroup.center G).index :=
      index_map_center_quotient K
    _ =
        Nat.card
          (G ⧸ (K ⊔ Subgroup.center G)) :=
      rfl

/-- Quotienting by a noncentral normal subgroup strictly decreases the
central index. -/
theorem centralIndex_quotient_lt
    [Finite G]
    (K : Subgroup G) [K.Normal]
    (hK : ¬K ≤ Subgroup.center G) :
    centralIndex (G ⧸ K) <
      centralIndex G := by
  exact
    lt_of_le_of_lt
      (centralIndex_quotient_le_card_quotient_sup_center K)
      ((card_quotient_sup_center_lt_centralIndex_iff
        (G := G) K).mpr hK)

end GroupTheory
end McKayConjecture
