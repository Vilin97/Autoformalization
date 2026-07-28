/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralIndex

/-!
# Central index decreases on proper subgroups containing the ambient center

The minimal-counterexample argument in the McKay reduction uses
`|H : Z(H)| < |G : Z(G)|` whenever `H < G` and `Z(G) ≤ H`.
This file proves that comparison directly from subgroup indices.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G]

/-- If a subgroup contains the ambient center, then the ambient center
is contained in the image of the subgroup's own center. -/
theorem center_le_map_center_subgroup
    (H : Subgroup G)
    (hZH : Subgroup.center G ≤ H) :
    Subgroup.center G ≤
      (Subgroup.center H).map H.subtype := by
  intro z hz
  refine ⟨⟨z, hZH hz⟩, ?_, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp hz y.1

/-- The index in `G` of the image of `Z(H)` factors as the central
index of `H` times the index of `H` in `G`. -/
theorem index_map_center_subgroup
    (H : Subgroup G) :
    ((Subgroup.center H).map H.subtype).index =
      centralIndex H * H.index := by
  rw [Subgroup.index_map_subtype]
  rfl

/-- A proper subgroup containing the ambient center has strictly
smaller central index. -/
theorem centralIndex_lt_of_center_le_of_lt_top
    [Finite G]
    (H : Subgroup G)
    (hZH : Subgroup.center G ≤ H)
    (hH : H < ⊤) :
    centralIndex H < centralIndex G := by
  have himage :
      Subgroup.center G ≤
        (Subgroup.center H).map H.subtype :=
    center_le_map_center_subgroup H hZH
  have hindex :
      ((Subgroup.center H).map H.subtype).index ≤
        (Subgroup.center G).index :=
    Subgroup.index_antitone himage
  rw [index_map_center_subgroup,
    ← centralIndex_eq_center_index] at hindex
  have hone : 1 < H.index :=
    Subgroup.one_lt_index_of_ne_top hH.ne
  have hpositive : 0 < centralIndex H :=
    centralIndex_pos H
  exact
    lt_of_lt_of_le
      (lt_mul_of_one_lt_right hpositive hone)
      hindex

end GroupTheory
end McKayConjecture
