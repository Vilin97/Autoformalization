/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.CardCommute
import McKayConjecture.GroupTheory.AlternatingSixThreeNormalizerConjugacyInvariants

/-!
# Commuting pairs in the three-normalizer coordinate model

The conjugacy-class count of the order-`216` group
`3^(1+2) ⋊ C₈` can be certified by counting commuting pairs.  A direct
enumeration of all `216²` pairs exceeds Lean's default recursion depth.
Here the count is split first by the two `C₈` coordinates and then by
one Heisenberg coordinate.  Every individual kernel reduction therefore
ranges over only `27 × 27` elements and uses the default resource limits.
-/

namespace McKayConjecture
namespace GroupTheory

open scoped BigOperators

/-- For fixed cyclic coordinates `c,d`, the Heisenberg-coordinate
solutions of the commutation equation. -/
abbrev AlternatingSixThreeNormalizerCommuteFiber
    (c d : AlternatingSixThreeCyclicEight) :=
  Σ p : AlternatingSixThreeHeisenbergCoordinates,
    {q : AlternatingSixThreeHeisenbergCoordinates //
      p * alternatingSixThreeHeisenbergCoordinateAction c q =
        q * alternatingSixThreeHeisenbergCoordinateAction d p}

/-- A recursion-depth-friendly computation of the cardinality of a
fixed cyclic-coordinate commuting fiber. -/
def alternatingSixThreeNormalizerCommuteFiberCard
    (c d : AlternatingSixThreeCyclicEight) : ℕ :=
  ∑ p : AlternatingSixThreeHeisenbergCoordinates,
    (Finset.univ.filter
      fun q : AlternatingSixThreeHeisenbergCoordinates =>
        p * alternatingSixThreeHeisenbergCoordinateAction c q =
          q * alternatingSixThreeHeisenbergCoordinateAction d p).card

/-- The sigma-type fiber cardinal is the nested finite sum used for
kernel computation. -/
theorem natCard_alternatingSixThreeNormalizerCommuteFiber
    (c d : AlternatingSixThreeCyclicEight) :
    Nat.card (AlternatingSixThreeNormalizerCommuteFiber c d) =
      alternatingSixThreeNormalizerCommuteFiberCard c d := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro p _
  rw [Fintype.card_subtype]

/-- Commuting pairs, written with their defining equality so that their
finite structure is computable. -/
abbrev AlternatingSixThreeNormalizerCommutingPairs :=
  {p : AlternatingSixThreeNormalizerCoordinates ×
      AlternatingSixThreeNormalizerCoordinates //
    p.1 * p.2 = p.2 * p.1}

/-- Splitting both semidirect-product elements into their Heisenberg and
cyclic coordinates splits the commuting-pair type into the `64` small
fibers above. -/
def alternatingSixThreeNormalizerCommutingPairsEquiv :
    AlternatingSixThreeNormalizerCommutingPairs ≃
      Σ c : AlternatingSixThreeCyclicEight,
        Σ d : AlternatingSixThreeCyclicEight,
          AlternatingSixThreeNormalizerCommuteFiber c d where
  toFun p :=
    ⟨p.1.1.right, p.1.2.right, p.1.1.left,
      ⟨p.1.2.left, by
        exact congrArg SemidirectProduct.left p.2⟩⟩
  invFun p :=
    ⟨(⟨p.2.2.1, p.1⟩, ⟨p.2.2.2.1, p.2.1⟩), by
      apply SemidirectProduct.ext
      · exact p.2.2.2.2
      · exact mul_comm _ _⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply SemidirectProduct.ext <;> rfl
  right_inv p := by
    rcases p with ⟨c, d, p, q, h⟩
    rfl

/-- Total size of the row with first cyclic coordinate zero. -/
theorem alternatingSixThreeNormalizerCommuteRowCard_zero :
    (∑ d : AlternatingSixThreeCyclicEight,
      alternatingSixThreeNormalizerCommuteFiberCard
        (Multiplicative.ofAdd (0 : ZMod 8)) d) =
      1080 := by
  decide

/-- Total size of the row with first cyclic coordinate one. -/
theorem alternatingSixThreeNormalizerCommuteRowCard_one :
    (∑ d : AlternatingSixThreeCyclicEight,
      alternatingSixThreeNormalizerCommuteFiberCard
        (Multiplicative.ofAdd (1 : ZMod 8)) d) =
      648 := by
  decide

/-- Total size of the row with first cyclic coordinate two. -/
theorem alternatingSixThreeNormalizerCommuteRowCard_two :
    (∑ d : AlternatingSixThreeCyclicEight,
      alternatingSixThreeNormalizerCommuteFiberCard
        (Multiplicative.ofAdd (2 : ZMod 8)) d) =
      648 := by
  decide

/-- Total size of the row with first cyclic coordinate three. -/
theorem alternatingSixThreeNormalizerCommuteRowCard_three :
    (∑ d : AlternatingSixThreeCyclicEight,
      alternatingSixThreeNormalizerCommuteFiberCard
        (Multiplicative.ofAdd (3 : ZMod 8)) d) =
      648 := by
  decide

/-- Total size of the row with first cyclic coordinate four. -/
theorem alternatingSixThreeNormalizerCommuteRowCard_four :
    (∑ d : AlternatingSixThreeCyclicEight,
      alternatingSixThreeNormalizerCommuteFiberCard
        (Multiplicative.ofAdd (4 : ZMod 8)) d) =
      1080 := by
  decide

/-- Total size of the row with first cyclic coordinate five. -/
theorem alternatingSixThreeNormalizerCommuteRowCard_five :
    (∑ d : AlternatingSixThreeCyclicEight,
      alternatingSixThreeNormalizerCommuteFiberCard
        (Multiplicative.ofAdd (5 : ZMod 8)) d) =
      648 := by
  decide

/-- Total size of the row with first cyclic coordinate six. -/
theorem alternatingSixThreeNormalizerCommuteRowCard_six :
    (∑ d : AlternatingSixThreeCyclicEight,
      alternatingSixThreeNormalizerCommuteFiberCard
        (Multiplicative.ofAdd (6 : ZMod 8)) d) =
      648 := by
  decide

/-- Total size of the row with first cyclic coordinate seven. -/
theorem alternatingSixThreeNormalizerCommuteRowCard_seven :
    (∑ d : AlternatingSixThreeCyclicEight,
      alternatingSixThreeNormalizerCommuteFiberCard
        (Multiplicative.ofAdd (7 : ZMod 8)) d) =
      648 := by
  decide

/-- The row total is `1080` for the two cyclic coordinates on which the
action is trivial, and `648` for the other six coordinates. -/
theorem alternatingSixThreeNormalizerCommuteRowCard
    (c : AlternatingSixThreeCyclicEight) :
    (∑ d : AlternatingSixThreeCyclicEight,
      alternatingSixThreeNormalizerCommuteFiberCard c d) =
      if (Multiplicative.toAdd c).val = 0 ∨
          (Multiplicative.toAdd c).val = 4 then
        1080
      else
        648 := by
  apply alternatingSixThreeCyclicEight_cases (c := c)
  · exact alternatingSixThreeNormalizerCommuteRowCard_zero
  · exact alternatingSixThreeNormalizerCommuteRowCard_one
  · exact alternatingSixThreeNormalizerCommuteRowCard_two
  · exact alternatingSixThreeNormalizerCommuteRowCard_three
  · exact alternatingSixThreeNormalizerCommuteRowCard_four
  · exact alternatingSixThreeNormalizerCommuteRowCard_five
  · exact alternatingSixThreeNormalizerCommuteRowCard_six
  · exact alternatingSixThreeNormalizerCommuteRowCard_seven

/-- The sum of all `64` fixed-cyclic-coordinate fibers is `6048`. -/
theorem alternatingSixThreeNormalizerCommuteFiberCard_sum :
    (∑ c : AlternatingSixThreeCyclicEight,
      ∑ d : AlternatingSixThreeCyclicEight,
        alternatingSixThreeNormalizerCommuteFiberCard c d) =
      6048 := by
  simp_rw [alternatingSixThreeNormalizerCommuteRowCard]
  decide

/-- The coordinate normalizer has exactly `6048` commuting ordered
pairs. -/
theorem natCard_alternatingSixThreeNormalizerCommutingPairs :
    Nat.card AlternatingSixThreeNormalizerCommutingPairs = 6048 := by
  calc
    Nat.card AlternatingSixThreeNormalizerCommutingPairs =
        Nat.card
          (Σ c : AlternatingSixThreeCyclicEight,
            Σ d : AlternatingSixThreeCyclicEight,
              AlternatingSixThreeNormalizerCommuteFiber c d) :=
      Nat.card_congr
        alternatingSixThreeNormalizerCommutingPairsEquiv
    _ =
        ∑ c : AlternatingSixThreeCyclicEight,
          ∑ d : AlternatingSixThreeCyclicEight,
            Nat.card
              (AlternatingSixThreeNormalizerCommuteFiber c d) := by
      simp only [Nat.card_sigma]
    _ =
        ∑ c : AlternatingSixThreeCyclicEight,
          ∑ d : AlternatingSixThreeCyclicEight,
            alternatingSixThreeNormalizerCommuteFiberCard c d := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      exact natCard_alternatingSixThreeNormalizerCommuteFiber c d
    _ = 6048 :=
      alternatingSixThreeNormalizerCommuteFiberCard_sum

end GroupTheory
end McKayConjecture
