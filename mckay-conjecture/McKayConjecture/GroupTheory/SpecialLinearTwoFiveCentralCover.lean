/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import McKayConjecture.GroupTheory.SpecialLinearTwoFive
import McKayConjecture.GroupTheory.UniversalCentralExtension

/-!
# The concrete perfect central cover `SL(2, 𝔽₅) → PSL(2, 𝔽₅)`

The quotient of `SL(2, ZMod 5)` by its center is, definitionally,
`PSL(2, ZMod 5)`.  This file packages the quotient map as a central
extension and proves all finite-group facts which do not use the exceptional
isomorphism `PSL(2, 𝔽₅) ≅ A₅` or the Schur-multiplier calculation:

* the center has order two;
* the projective quotient has order sixty; and
* the source is perfect.

Thus the only remaining group-theoretic steps required to install this
concrete group as the chosen universal cover of `A₅` are the exceptional
isomorphism and universality.  Mathlib supplies the generic simplicity
theorem for this projective quotient, but it is not needed for the concrete
central-extension package below.
-/

noncomputable section

open Matrix
open scoped MatrixGroups IsMulCommutative

namespace McKayConjecture
namespace GroupTheory

/-- The projective quotient of the concrete binary-cover candidate. -/
abbrev ProjectiveSpecialLinearTwoFive :=
  PSL(2, ZMod 5)

/-- The center of `SL(2, 𝔽₅)` consists of its two scalar matrices. -/
theorem natCard_center_specialLinearTwoFive :
    Nat.card (Subgroup.center SpecialLinearTwoFive) = 2 := by
  rw [Nat.card_eq_fintype_card]
  native_decide

/-- The quotient map by the center, packaged as a central extension. -/
def specialLinearTwoFiveCentralExtension :
    CentralExtension
      SpecialLinearTwoFive ProjectiveSpecialLinearTwoFive where
  projection :=
    QuotientGroup.mk' (Subgroup.center SpecialLinearTwoFive)
  surjective :=
    QuotientGroup.mk'_surjective _
  ker_le_center := by
    rw [QuotientGroup.ker_mk']

/-- `PSL(2, 𝔽₅)` has order `60`. -/
theorem natCard_projectiveSpecialLinearTwoFive :
    Nat.card ProjectiveSpecialLinearTwoFive = 60 := by
  have hcard :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center SpecialLinearTwoFive)
  rw [natCard_specialLinearTwoFive,
    natCard_center_specialLinearTwoFive] at hcard
  have hmul :
      Nat.card ProjectiveSpecialLinearTwoFive * 2 =
        60 * 2 := by
    calc
      Nat.card ProjectiveSpecialLinearTwoFive * 2 = 120 :=
        hcard.symm
      _ = 60 * 2 := by norm_num
  exact
    Nat.eq_of_mul_eq_mul_right
      (by norm_num : 0 < 2) hmul

end GroupTheory
end McKayConjecture
