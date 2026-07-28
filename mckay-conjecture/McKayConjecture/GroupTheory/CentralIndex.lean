/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Center

/-!
# Central index of a finite group

The central index of `G` is the order of `G / Z(G)`, equivalently the
index of the center.  For finite groups it is positive, and it is one
exactly when `G` is commutative.

The subgroup comparison results in this file deliberately state the
needed containment hypotheses.  In particular, strict containment of
the center in a subgroup gives a strict decrease of quotient
cardinality.  The same applies canonically to `K ⊔ Z(G)`.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory

variable (G : Type u) [Group G]

/-- The central index `|G / Z(G)|`.  It is intended primarily for
finite groups. -/
def centralIndex : ℕ :=
  Nat.card (G ⧸ Subgroup.center G)

/-- The central index is the subgroup index of the center. -/
theorem centralIndex_eq_center_index :
    centralIndex G =
      (Subgroup.center G).index :=
  rfl

/-- The order of the center times the central index is the order of the
group. -/
theorem card_center_mul_centralIndex :
    Nat.card (Subgroup.center G) *
        centralIndex G =
      Nat.card G := by
  rw [centralIndex_eq_center_index]
  exact (Subgroup.center G).card_mul_index

/-- The central index of a finite group is positive. -/
theorem centralIndex_pos [Finite G] :
    0 < centralIndex G :=
  Nat.card_pos

/-- The central index of a finite group is nonzero. -/
theorem centralIndex_ne_zero [Finite G] :
    centralIndex G ≠ 0 :=
  (centralIndex_pos G).ne'

/-- The central index is one exactly when the group is commutative. -/
theorem centralIndex_eq_one_iff :
    centralIndex G = 1 ↔
      IsMulCommutative G := by
  rw [centralIndex_eq_center_index,
    Subgroup.index_eq_one,
    Subgroup.center_eq_top_iff]

/-- A commutative group has central index one. -/
theorem centralIndex_eq_one
    [IsMulCommutative G] :
    centralIndex G = 1 :=
  (centralIndex_eq_one_iff G).mpr
    inferInstance

/-- A finite noncommutative group has central index greater than one. -/
theorem one_lt_centralIndex
    [Finite G] (hG : ¬IsMulCommutative G) :
    1 < centralIndex G := by
  rw [centralIndex_eq_center_index]
  apply Subgroup.one_lt_index_of_ne_top
  exact
    mt Subgroup.center_eq_top_iff.mp hG

variable {G}

/-- A group equivalence maps the center onto the center. -/
theorem map_center_equiv
    {H : Type v} [Group H]
    (e : G ≃* H) :
    (Subgroup.center G).map
        e.toMonoidHom =
      Subgroup.center H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact
      MulEquivClass.apply_mem_center e hx
  · intro hy
    exact
      ⟨e.symm y,
        MulEquivClass.apply_mem_center
          e.symm hy,
        e.apply_symm_apply y⟩

/-- The central index is invariant under group equivalence. -/
theorem centralIndex_congr
    {H : Type v} [Group H]
    (e : G ≃* H) :
    centralIndex G = centralIndex H := by
  calc
    centralIndex G =
        (Subgroup.center G).index :=
      centralIndex_eq_center_index G
    _ =
        ((Subgroup.center G).map
          e.toMonoidHom).index :=
      (Subgroup.index_map_equiv
        (Subgroup.center G) e).symm
    _ = (Subgroup.center H).index := by
      rw [map_center_equiv e]
    _ = centralIndex H :=
      (centralIndex_eq_center_index H).symm

variable [Finite G]

omit [Finite G] in
/-- If the center is contained in `K`, the relative index of the center
in `K` times the quotient cardinality by `K` equals the central
index. -/
theorem center_relIndex_mul_card_quotient
    {K : Subgroup G}
    (hZK : Subgroup.center G ≤ K) :
    (Subgroup.center G).relIndex K *
        Nat.card (G ⧸ K) =
      centralIndex G := by
  change
    (Subgroup.center G).relIndex K *
        K.index =
      (Subgroup.center G).index
  exact
    Subgroup.relIndex_mul_index hZK

/-- Quotient cardinality is antitone among subgroups known to contain
the center. -/
theorem card_quotient_le_centralIndex
    {K : Subgroup G}
    (hZK : Subgroup.center G ≤ K) :
    Nat.card (G ⧸ K) ≤
      centralIndex G := by
  change
    K.index ≤
      (Subgroup.center G).index
  exact Subgroup.index_antitone hZK

/-- Safe strict form: a subgroup strictly containing the center has
strictly smaller quotient cardinality than the central index. -/
theorem card_quotient_lt_centralIndex_of_center_lt
    {K : Subgroup G}
    (hZK : Subgroup.center G < K) :
    Nat.card (G ⧸ K) <
      centralIndex G := by
  change
    K.index <
      (Subgroup.center G).index
  exact Subgroup.index_strictAnti hZK

/-- Among subgroups containing the center, equality of quotient
cardinality with the central index characterizes the center itself. -/
theorem card_quotient_eq_centralIndex_iff
    {K : Subgroup G}
    (hZK : Subgroup.center G ≤ K) :
    Nat.card (G ⧸ K) =
        centralIndex G ↔
      K = Subgroup.center G := by
  change
    K.index =
        (Subgroup.center G).index ↔
      K = Subgroup.center G
  constructor
  · intro hindex
    rcases hZK.eq_or_lt with hEq | hLt
    · exact hEq.symm
    · have hstrict :=
        Subgroup.index_strictAnti hLt
      rw [hindex] at hstrict
      exact (lt_irrefl _ hstrict).elim
  · rintro rfl
    rfl

omit [Finite G] in
/-- Exact index factorization for adjoining the center to an arbitrary
subgroup. -/
theorem center_relIndex_mul_card_quotient_sup_center
    (K : Subgroup G) :
    (Subgroup.center G).relIndex K *
        Nat.card
          (G ⧸
            (K ⊔ Subgroup.center G)) =
      centralIndex G := by
  simpa only [Subgroup.relIndex_sup_right]
    using
      center_relIndex_mul_card_quotient
        (G := G)
        (K := K ⊔ Subgroup.center G)
        le_sup_right

/-- Adjoining the center always gives a quotient whose cardinality is
at most the central index. -/
theorem card_quotient_sup_center_le_centralIndex
    (K : Subgroup G) :
    Nat.card
        (G ⧸
          (K ⊔ Subgroup.center G)) ≤
      centralIndex G :=
  card_quotient_le_centralIndex
    (G := G) le_sup_right

/-- Adjoining the center leaves the central index unchanged exactly
when the original subgroup was already central. -/
theorem card_quotient_sup_center_eq_centralIndex_iff
    (K : Subgroup G) :
    Nat.card
          (G ⧸
            (K ⊔ Subgroup.center G)) =
        centralIndex G ↔
      K ≤ Subgroup.center G := by
  rw [card_quotient_eq_centralIndex_iff
      (G := G) le_sup_right,
    sup_eq_right]

/-- Adjoining a noncentral subgroup to the center strictly lowers the
quotient cardinality. -/
theorem card_quotient_sup_center_lt_centralIndex_iff
    (K : Subgroup G) :
    Nat.card
          (G ⧸
            (K ⊔ Subgroup.center G)) <
        centralIndex G ↔
      ¬K ≤ Subgroup.center G := by
  constructor
  · intro hlt hK
    exact
      hlt.ne
        ((card_quotient_sup_center_eq_centralIndex_iff
          (G := G) K).mpr hK)
  · intro hK
    have hle :=
      card_quotient_sup_center_le_centralIndex
        (G := G) K
    have hne :
        Nat.card
            (G ⧸
              (K ⊔ Subgroup.center G)) ≠
          centralIndex G := by
      intro heq
      exact
        hK
          ((card_quotient_sup_center_eq_centralIndex_iff
            (G := G) K).mp heq)
    exact lt_of_le_of_ne hle hne

end GroupTheory
end McKayConjecture
