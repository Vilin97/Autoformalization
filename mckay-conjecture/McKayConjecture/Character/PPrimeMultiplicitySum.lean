/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Prime-to-`p` terms in finite multiplicity sums

The transitivity formula for restriction multiplicities is a finite sum of
products.  If exactly one summand is prime to a prime `p`, then the whole
sum is prime to `p`.  This file packages the elementary divisibility
argument independently of character theory.
-/

open scoped BigOperators

namespace McKayConjecture

variable {ι : Type} [DecidableEq ι]

/-- If every term except `i` is divisible by `p`, divisibility of the whole
sum is equivalent to divisibility of the distinguished term. -/
theorem dvd_finset_sum_iff_dvd_single
    (p : ℕ) (s : Finset ι) (f : ι → ℕ)
    {i : ι} (hi : i ∈ s)
    (hother :
      ∀ j ∈ s, j ≠ i → p ∣ f j) :
    p ∣ ∑ j ∈ s, f j ↔ p ∣ f i := by
  have hrest :
      p ∣ ∑ j ∈ s.erase i, f j := by
    apply Finset.dvd_sum
    intro j hj
    exact hother j (Finset.mem_of_mem_erase hj)
      (Finset.ne_of_mem_erase hj)
  have hsum :
      (∑ j ∈ s, f j) =
        f i + ∑ j ∈ s.erase i, f j := by
    rw [add_comm]
    exact (Finset.sum_erase_add s f hi).symm
  rw [hsum]
  exact (Nat.dvd_add_iff_left hrest).symm

/-- Negated form of `dvd_finset_sum_iff_dvd_single`. -/
theorem not_dvd_finset_sum_iff_not_dvd_single
    (p : ℕ) (s : Finset ι) (f : ι → ℕ)
    {i : ι} (hi : i ∈ s)
    (hother :
      ∀ j ∈ s, j ≠ i → p ∣ f j) :
    (¬p ∣ ∑ j ∈ s, f j) ↔
      ¬p ∣ f i := by
  rw [dvd_finset_sum_iff_dvd_single p s f hi hother]

/-- For prime `p`, a product is prime to `p` exactly when both factors are
prime to `p`. -/
theorem not_dvd_mul_iff
    {p a b : ℕ} (hp : p.Prime) :
    (¬p ∣ a * b) ↔ (¬p ∣ a) ∧ (¬p ∣ b) := by
  rw [hp.dvd_mul]
  tauto

/-- A finite sum of products is prime to `p` when one distinguished
product has both factors prime to `p` and every other product has a
divisible factor. -/
theorem not_dvd_sum_mul_of_unique
    {p : ℕ} (hp : p.Prime)
    (s : Finset ι) (a b : ι → ℕ)
    {i : ι} (hi : i ∈ s)
    (hai : ¬p ∣ a i) (hbi : ¬p ∣ b i)
    (hother :
      ∀ j ∈ s, j ≠ i →
        p ∣ a j ∨ p ∣ b j) :
    ¬p ∣ ∑ j ∈ s, a j * b j := by
  apply
    (not_dvd_finset_sum_iff_not_dvd_single
      p s (fun j ↦ a j * b j) hi ?_).2
  · exact (not_dvd_mul_iff hp).2 ⟨hai, hbi⟩
  · intro j hj hji
    exact (hp.dvd_mul).2 (hother j hj hji)

/-- If a finite sum of products is prime to a prime `p`, at least one
summand has both factors prime to `p`. -/
theorem exists_not_dvd_both_of_not_dvd_sum_mul
    {p : ℕ} (hp : p.Prime)
    (s : Finset ι) (a b : ι → ℕ)
    (hsum : ¬p ∣ ∑ i ∈ s, a i * b i) :
    ∃ i ∈ s, (¬p ∣ a i) ∧ (¬p ∣ b i) := by
  by_contra hexists
  apply hsum
  apply Finset.dvd_sum
  intro i hi
  apply (hp.dvd_mul).2
  by_contra hterm
  push_neg at hterm
  exact hexists ⟨i, hi, hterm⟩

end McKayConjecture
