/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic

/-!
# Generation in groups of order four

Two distinct nonidentity elements generate any finite group of order four.
The proof only uses Lagrange's theorem: their closure has at least three
elements, while its cardinality divides four.
-/

namespace McKayConjecture
namespace GroupTheory

universe u

variable {Q : Type u} [Group Q] [Finite Q]

/-- Two distinct nonidentity elements whose product is nonidentity exhibit
four distinct elements of the ambient group. -/
theorem four_le_natCard_of_ne_one_of_ne_of_mul_ne_one
    {x y : Q}
    (hx : x ≠ 1)
    (hy : y ≠ 1)
    (hxy : x ≠ y)
    (hmul : x * y ≠ 1) :
    4 ≤ Nat.card Q := by
  let fourElements : Fin 4 → Q :=
    ![1, x, y, x * y]
  have hfourElements :
      Function.Injective fourElements := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [fourElements, hx, hy, hxy, hmul, hx.symm,
        hy.symm, hxy.symm, hmul.symm] at hij ⊢
  rw [← Nat.card_fin 4]
  exact
    Nat.card_le_card_of_injective
      fourElements hfourElements

/-- Two distinct nonidentity elements generate a group of cardinality four. -/
theorem closure_pair_eq_top_of_natCard_eq_four
    {x y : Q}
    (hcard : Nat.card Q = 4)
    (hx : x ≠ 1)
    (hy : y ≠ 1)
    (hxy : x ≠ y) :
    Subgroup.closure ({x, y} : Set Q) = ⊤ := by
  let H : Subgroup Q :=
    Subgroup.closure ({x, y} : Set Q)
  have hxH : x ∈ H :=
    Subgroup.subset_closure (Set.mem_insert x {y})
  have hyH : y ∈ H :=
    Subgroup.subset_closure
      (Set.mem_insert_of_mem x (Set.mem_singleton y))
  let threeElements : Fin 3 → H :=
    ![⟨1, H.one_mem⟩, ⟨x, hxH⟩, ⟨y, hyH⟩]
  have hthreeElements :
      Function.Injective threeElements := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [threeElements, hx, hy, hxy, hx.symm, hy.symm,
        hxy.symm] at hij ⊢
  have hthree : 3 ≤ Nat.card H := by
    rw [← Nat.card_fin 3]
    exact
      Nat.card_le_card_of_injective
        threeElements hthreeElements
  have hdivides : Nat.card H ∣ 4 := by
    rw [← hcard]
    exact H.card_subgroup_dvd_card
  have hHcard : Nat.card H = 4 := by
    have hle : Nat.card H ≤ 4 :=
      Nat.le_of_dvd (by norm_num) hdivides
    have hcases :
        Nat.card H = 3 ∨ Nat.card H = 4 := by
      omega
    rcases hcases with hHcard | hHcard
    · rw [hHcard] at hdivides
      norm_num at hdivides
    · exact hHcard
  exact H.eq_top_of_card_eq (hHcard.trans hcard.symm)

end GroupTheory
end McKayConjecture
