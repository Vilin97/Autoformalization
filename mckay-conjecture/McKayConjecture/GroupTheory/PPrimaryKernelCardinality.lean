/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index

/-!
# Detecting `p`-group kernels by cardinality

For a homomorphism of finite groups, the order of the source is the
product of the orders of its kernel and range.  Consequently, if the
source-to-range order ratio is a power of `p`, the kernel is a
`p`-group.  A surjective specialization replaces the range order by the
target order.

These lemmas isolate the group-theoretic part of proving that a
coefficient-reduction kernel consists of `p`-power roots of unity.
-/

noncomputable section

namespace MonoidHom

variable {p n : ℕ}
variable {G H : Type} [Group G] [Group H]
variable [Finite H]

/-- If the order of a finite group is a `p`-power times the order of the
range of a homomorphism, then its kernel is a `p`-group. -/
theorem ker_isPGroup_of_card_eq_pow_mul_card_range
    [Finite G]
    (f : G →* H)
    (hcard :
      Nat.card G =
        p ^ n * Nat.card f.range) :
    IsPGroup p f.ker := by
  refine IsPGroup.of_card (n := n) ?_
  exact
    mul_right_cancel₀
      (Nat.card_pos (α := f.range)).ne'
      (by
        calc
          Nat.card f.ker * Nat.card f.range =
              Nat.card f.ker * f.ker.index := by
            rw [Subgroup.index_ker f]
          _ = Nat.card G :=
            f.ker.card_mul_index
          _ = p ^ n * Nat.card f.range :=
            hcard)

/-- Surjective form: if the source order is a `p`-power times the target
order, then the kernel is a `p`-group. -/
theorem ker_isPGroup_of_surjective_card_eq_pow_mul
    [Finite G]
    (f : G →* H)
    (hsurjective : Function.Surjective f)
    (hcard :
      Nat.card G =
        p ^ n * Nat.card H) :
    IsPGroup p f.ker := by
  refine
    f.ker_isPGroup_of_card_eq_pow_mul_card_range (n := n) ?_
  rw [f.range_eq_top.mpr hsurjective]
  simpa using hcard

end MonoidHom
