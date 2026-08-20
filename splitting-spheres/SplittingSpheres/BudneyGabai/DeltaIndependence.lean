/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# A triangular family in a free abelian group

This file records only a combinatorial calculation in the free abelian group on ordered pairs
of integers.  It defines an explicit family `budneyGabaiDelta` and proves its linear independence
by a triangular pivot-coordinate argument.

Nothing here constructs or identifies a geometric invariant, proves invariance, realizes these
formal sums by embeddings, or makes a mapping-class-group assertion.
-/

@[expose] public section

noncomputable section

namespace SplittingSpheres

/-- The free abelian group on formal symbols indexed by ordered pairs of integers. -/
abbrev BudneyGabaiSymbolGroup := (ℤ × ℤ) →₀ ℤ

/-- The basis symbol at `(p, q)`. -/
def budneyGabaiGenerator (p q : ℤ) : BudneyGabaiSymbolGroup :=
  Finsupp.single (p, q) 1

/-- The coordinate used to distinguish the `k`th formal delta from all earlier deltas. -/
def budneyGabaiPivot (k : ℤ) : ℤ × ℤ :=
  (k - 1, k - 2)

/-- The formal delta sum, defined purely inside the free abelian group on `ℤ × ℤ`. -/
def budneyGabaiDelta (k : ℤ) : BudneyGabaiSymbolGroup :=
  (k - 1 : ℤ) •
      (budneyGabaiGenerator (k - 2) (k - 1) -
        budneyGabaiGenerator (k - 1) (k - 2) +
        budneyGabaiGenerator (1 - k) (2 - k) -
        budneyGabaiGenerator (2 - k) (1 - k)) -
    (-budneyGabaiGenerator (k - 2) (-1) +
      budneyGabaiGenerator (-(k - 2)) 1 -
      budneyGabaiGenerator 1 (-(k - 2)) +
      budneyGabaiGenerator (-1) (k - 2))

/-- At its pivot, the `k`th delta has coefficient `-(k - 1)`. -/
theorem budneyGabaiDelta_apply_pivot {k : ℤ} (hk : 4 ≤ k) :
    budneyGabaiDelta k (budneyGabaiPivot k) = -(k - 1) := by
  simp only [budneyGabaiDelta, budneyGabaiPivot, budneyGabaiGenerator,
    Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.neg_apply,
    Finsupp.single_apply, smul_eq_mul]
  simp only [Prod.mk.injEq]
  split_ifs <;> omega

/-- Every earlier delta has coefficient zero at the `k`th pivot. -/
theorem budneyGabaiDelta_apply_later_pivot {m k : ℤ} (hm : 4 ≤ m) (hmk : m < k) :
    budneyGabaiDelta m (budneyGabaiPivot k) = 0 := by
  simp only [budneyGabaiDelta, budneyGabaiPivot, budneyGabaiGenerator,
    Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.neg_apply,
    Finsupp.single_apply, smul_eq_mul]
  simp only [Prod.mk.injEq]
  split_ifs <;> omega

/-- The natural-number enumeration of all formal deltas with integer index at least four. -/
def budneyGabaiDeltaFamily (n : ℕ) : BudneyGabaiSymbolGroup :=
  budneyGabaiDelta ((n : ℤ) + 4)

/-- The `n`th enumerated delta has coefficient `-(n + 3)` at its pivot. -/
theorem budneyGabaiDeltaFamily_apply_pivot (n : ℕ) :
    budneyGabaiDeltaFamily n (budneyGabaiPivot ((n : ℤ) + 4)) =
      -((n : ℤ) + 3) := by
  rw [budneyGabaiDeltaFamily,
    budneyGabaiDelta_apply_pivot (k := (n : ℤ) + 4) (by omega)]
  omega

/-- At the pivot of a later member, an earlier enumerated delta has coefficient zero. -/
theorem budneyGabaiDeltaFamily_apply_later_pivot {i n : ℕ} (hin : i < n) :
    budneyGabaiDeltaFamily i (budneyGabaiPivot ((n : ℤ) + 4)) = 0 := by
  apply budneyGabaiDelta_apply_later_pivot
  · omega
  · exact_mod_cast (Nat.add_lt_add_right hin 4)

/-- The complete family of formal deltas with index at least four is linearly independent over
`ℤ`.  This is only linear independence of explicit normal forms in a free abelian group. -/
theorem linearIndependent_budneyGabaiDeltaFamily :
    LinearIndependent ℤ budneyGabaiDeltaFamily := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  let t := s.filter fun j => g j ≠ 0
  have ht : t.Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  let n := t.max' ht
  have hnmemt : n ∈ t := t.max'_mem ht
  have hnmem : n ∈ s := (Finset.mem_filter.mp hnmemt).1
  have hgn : g n ≠ 0 := (Finset.mem_filter.mp hnmemt).2
  have hnmax {j : ℕ} (hj : j ∈ s) (hgj : g j ≠ 0) : j ≤ n := by
    exact t.le_max' j (Finset.mem_filter.mpr ⟨hj, hgj⟩)
  have heval := congrArg
    (fun x : BudneyGabaiSymbolGroup => x (budneyGabaiPivot ((n : ℤ) + 4))) hsum
  rw [Finset.sum_apply'] at heval
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply] at heval
  have hsum_pivot :
      (∑ j ∈ s,
          g j * budneyGabaiDeltaFamily j (budneyGabaiPivot ((n : ℤ) + 4))) =
        g n * (-((n : ℤ) + 3)) := by
    rw [Finset.sum_eq_single n]
    · rw [budneyGabaiDeltaFamily_apply_pivot]
    · intro j hj hne
      by_cases hgj : g j = 0
      · simp [hgj]
      · have hjlt : j < n := lt_of_le_of_ne (hnmax hj hgj) hne
        rw [budneyGabaiDeltaFamily_apply_later_pivot hjlt, mul_zero]
    · exact fun hnnot => (hnnot hnmem).elim
  rw [hsum_pivot] at heval
  have hfactor : -((n : ℤ) + 3) ≠ 0 := by omega
  exact hgn ((mul_eq_zero.mp heval).resolve_right hfactor)

/-- Every enumerated formal delta is nonzero. -/
theorem budneyGabaiDeltaFamily_ne_zero (n : ℕ) :
    budneyGabaiDeltaFamily n ≠ 0 :=
  linearIndependent_budneyGabaiDeltaFamily.ne_zero n

/-- Distinct indices give distinct formal delta sums. -/
theorem injective_budneyGabaiDeltaFamily :
    Function.Injective budneyGabaiDeltaFamily :=
  linearIndependent_budneyGabaiDeltaFamily.injective

/-- The formal delta sums are pairwise distinct. -/
theorem pairwise_ne_budneyGabaiDeltaFamily :
    Pairwise fun i j => budneyGabaiDeltaFamily i ≠ budneyGabaiDeltaFamily j :=
  injective_budneyGabaiDeltaFamily.pairwise_ne

/-- The difference of two distinctly indexed formal delta sums is nonzero. -/
theorem budneyGabaiDeltaFamily_sub_ne_zero {i j : ℕ} (hij : i ≠ j) :
    budneyGabaiDeltaFamily i - budneyGabaiDeltaFamily j ≠ 0 :=
  sub_ne_zero.mpr (injective_budneyGabaiDeltaFamily.ne hij)

end SplittingSpheres
