/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Sum

/-!
# Finite sums grouped by fibers

This small utility rewrites a finite sum of a fiberwise-constant function as
a weighted sum over the target labels.  Character-norm computations can then
use conjugacy-class representatives and checked class sizes without expanding
one summand per group element.
-/

open scoped BigOperators

namespace McKayConjecture

/-- A finite sum of a function constant on the fibers of `label` is the
fiber cardinality weighted sum of its representative values. -/
theorem sum_eq_sum_card_fiber_nsmul
    {α ι M : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M]
    (label : α → ι)
    (representative : ι → α)
    (f : α → M)
    (hf : ∀ x, f x = f (representative (label x))) :
    (∑ x : α, f x) =
      ∑ i : ι,
        Fintype.card {x : α // label x = i} •
          f (representative i) := by
  classical
  calc
    (∑ x : α, f x) =
        ∑ z : Σ i : ι, {x : α // label x = i},
          f z.2 := by
      exact
        (Equiv.sum_comp
          (Equiv.sigmaFiberEquiv label) f).symm
    _ =
        ∑ i : ι,
          ∑ x : {x : α // label x = i}, f x := by
      exact
        Fintype.sum_sigma
          (fun z : Σ i : ι, {x : α // label x = i} ↦
            f z.2)
    _ =
        ∑ i : ι,
          ∑ _x : {x : α // label x = i},
            f (representative i) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro x _
      calc
        f x = f (representative (label x)) := hf x
        _ = f (representative i) := by rw [x.property]
    _ = _ := by simp

end McKayConjecture
