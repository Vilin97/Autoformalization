/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.OfQuotient

/-!
# Iterated fixed points

For a normal subgroup `Q ◁ P` acting on a group `A`, the quotient `P / Q`
acts canonically on `A^Q`.  Taking fixed points once more recovers `A^P`.
This is the group-theoretic coordinate used in the transitivity step of
the Glauberman correspondence.
-/

namespace McKayConjecture
namespace GroupTheory

variable (P A : Type*)
variable [Group P] [Group A]
variable [MulDistribMulAction P A]

/-- Fixed points under a normal subgroup followed by fixed points under
the quotient are canonically the fixed points under the whole group. -/
def iteratedFixedPointsEquiv
    (Q : Subgroup P) [Q.Normal] :
    FixedPoints.subgroup (P ⧸ Q)
        (FixedPoints.subgroup Q A) ≃*
      FixedPoints.subgroup P A where
  toFun x :=
    ⟨x.1.1, fun p ↦ by
      have hp := x.2 (p : P ⧸ Q)
      exact congrArg Subtype.val hp⟩
  invFun x :=
    ⟨⟨x.1, fun q ↦ x.2 q.1⟩, fun g ↦ by
      refine Quotient.inductionOn' g ?_
      intro p
      apply Subtype.ext
      exact x.2 p⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

@[simp]
theorem iteratedFixedPointsEquiv_apply_coe
    (Q : Subgroup P) [Q.Normal]
    (x :
      FixedPoints.subgroup (P ⧸ Q)
        (FixedPoints.subgroup Q A)) :
    ((iteratedFixedPointsEquiv P A Q x :
        FixedPoints.subgroup P A) : A) =
      ((x :
        FixedPoints.subgroup Q A) : A) :=
  rfl

@[simp]
theorem iteratedFixedPointsEquiv_symm_apply_coe
    (Q : Subgroup P) [Q.Normal]
    (x : FixedPoints.subgroup P A) :
    (((iteratedFixedPointsEquiv P A Q).symm x :
        FixedPoints.subgroup Q A) : A) =
      (x : A) :=
  rfl

end GroupTheory
end McKayConjecture
