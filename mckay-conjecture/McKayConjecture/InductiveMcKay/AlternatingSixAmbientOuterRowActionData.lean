/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryRows

/-!
# Outer row-action data for the canonical sixfold cover of `A₆`

The two permutations in this file are written in the project's named
ordinary-row coordinates.  They were derived by evaluating each of the 31
constructed matrix characters on the 31 checked conjugacy-class
representatives, applying the independently checked class permutations, and
matching the resulting vectors.

This file records only the finite permutations and their elementary
degree/scalar properties.  The separate character-action bridge proves that
the canonical outer automorphisms induce these permutations.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Inversion of the central scalar induced by either canonical outer
automorphism. -/
def alternatingSixAmbientOuterScalarPattern :
    AlternatingSixAmbientScalarPattern →
      AlternatingSixAmbientScalarPattern
  | .trivial => .trivial
  | .orderThreePositive => .orderThreeNegative
  | .orderThreeNegative => .orderThreePositive
  | .orderTwo => .orderTwo
  | .orderSixPositive => .orderSixNegative
  | .orderSixNegative => .orderSixPositive

/-- The outer scalar-pattern involution sends the first central scalar to
its multiplicative inverse. -/
theorem alternatingSixAmbientOuterScalarPattern_firstScalar
    (pattern : AlternatingSixAmbientScalarPattern) :
    alternatingSixComplexCyclotomicRoot ^
        (alternatingSixAmbientOuterScalarPattern pattern).exponent 0 =
      (alternatingSixComplexCyclotomicRoot ^
        pattern.exponent 0)⁻¹ := by
  let ζ := alternatingSixComplexCyclotomicRoot
  have hroot : ζ ^ 120 = 1 :=
    alternatingSixComplexCyclotomicRoot_isPrimitive.pow_eq_one
  have hinv (m n : ℕ) (hadd : m + n = 120) :
      ζ ^ m = (ζ ^ n)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add, hadd, hroot]
  cases pattern
  · simp [alternatingSixAmbientOuterScalarPattern,
      AlternatingSixAmbientScalarPattern.exponent]
  · exact hinv 40 80 (by norm_num)
  · exact hinv 80 40 (by norm_num)
  · exact hinv 60 60 (by norm_num)
  · exact hinv 100 20 (by norm_num)
  · exact hinv 20 100 (by norm_num)

/-- The other named row, when one exists, with the same degree and central
scalar pattern.  Rows whose two signatures already determine them are fixed.
-/
def alternatingSixAmbientOrdinaryRowSignatureMate :
    AlternatingSixAmbientOrdinaryRow →
      AlternatingSixAmbientOrdinaryRow
  | .row02 => .row03
  | .row03 => .row02
  | .row04 => .row05
  | .row05 => .row04
  | .row06 => .row07
  | .row07 => .row06
  | .row08 => .row09
  | .row09 => .row08
  | .row12 => .row13
  | .row13 => .row12
  | .row14 => .row15
  | .row15 => .row14
  | .row16 => .row17
  | .row17 => .row16
  | .row18 => .row19
  | .row19 => .row18
  | .row24 => .row25
  | .row25 => .row24
  | .atlasTwelvePowerOne => .atlasTwelvePowerSeven
  | .atlasTwelvePowerSeven => .atlasTwelvePowerOne
  | .atlasTwelvePowerTwo => .atlasTwelvePowerEleven
  | .atlasTwelvePowerEleven => .atlasTwelvePowerTwo
  | row => row

/-- Degree and central scalar determine a named ordinary row up to its
explicit signature mate. -/
theorem alternatingSixAmbientOrdinaryRow_eq_or_eq_signatureMate
    (row target : AlternatingSixAmbientOrdinaryRow)
    (hdimension : target.dimension = row.dimension)
    (hscalar : target.scalarPattern = row.scalarPattern) :
    target = row ∨
      target = alternatingSixAmbientOrdinaryRowSignatureMate row := by
  cases row <;> cases target <;>
    simp_all [
      AlternatingSixAmbientOrdinaryRow.dimension,
      AlternatingSixAmbientOrdinaryRow.scalarPattern,
      alternatingSixAmbientOrdinaryRowSignatureMate
    ]

/-- Row permutation induced by the first canonical outer automorphism.

In named one-based row notation its nontrivial cycles are
`(2 5)(3 4)(10 11)(12 15)(13 14)(16 17)(18 19)
(21 22)(24 25)(30 31)` together with
`(atlas1 atlas2)(atlas7 atlas11)`. -/
def alternatingSixAmbientAlphaOneOrdinaryRowAction :
    Equiv.Perm AlternatingSixAmbientOrdinaryRow where
  toFun
    | .row01 => .row01
    | .row02 => .row05
    | .row03 => .row04
    | .row04 => .row03
    | .row05 => .row02
    | .row06 => .row06
    | .row07 => .row07
    | .row08 => .row08
    | .row09 => .row09
    | .row10 => .row11
    | .row11 => .row10
    | .row12 => .row15
    | .row13 => .row14
    | .row14 => .row13
    | .row15 => .row12
    | .row16 => .row17
    | .row17 => .row16
    | .row18 => .row19
    | .row19 => .row18
    | .row20 => .row20
    | .row21 => .row22
    | .row22 => .row21
    | .row23 => .row23
    | .row24 => .row25
    | .row25 => .row24
    | .row30 => .row31
    | .row31 => .row30
    | .atlasTwelvePowerOne => .atlasTwelvePowerTwo
    | .atlasTwelvePowerTwo => .atlasTwelvePowerOne
    | .atlasTwelvePowerSeven => .atlasTwelvePowerEleven
    | .atlasTwelvePowerEleven => .atlasTwelvePowerSeven
  invFun
    | .row01 => .row01
    | .row02 => .row05
    | .row03 => .row04
    | .row04 => .row03
    | .row05 => .row02
    | .row06 => .row06
    | .row07 => .row07
    | .row08 => .row08
    | .row09 => .row09
    | .row10 => .row11
    | .row11 => .row10
    | .row12 => .row15
    | .row13 => .row14
    | .row14 => .row13
    | .row15 => .row12
    | .row16 => .row17
    | .row17 => .row16
    | .row18 => .row19
    | .row19 => .row18
    | .row20 => .row20
    | .row21 => .row22
    | .row22 => .row21
    | .row23 => .row23
    | .row24 => .row25
    | .row25 => .row24
    | .row30 => .row31
    | .row31 => .row30
    | .atlasTwelvePowerOne => .atlasTwelvePowerTwo
    | .atlasTwelvePowerTwo => .atlasTwelvePowerOne
    | .atlasTwelvePowerSeven => .atlasTwelvePowerEleven
    | .atlasTwelvePowerEleven => .atlasTwelvePowerSeven
  left_inv row := by cases row <;> rfl
  right_inv row := by cases row <;> rfl

/-- Row permutation induced by the second canonical outer automorphism.

Its nontrivial cycles are
`(2 4)(3 5)(6 7)(8 9)(10 11)(12 14)(13 15)(21 22)
(30 31)` together with
`(atlas1 atlas11)(atlas2 atlas7)`. -/
def alternatingSixAmbientAlphaTwoOrdinaryRowAction :
    Equiv.Perm AlternatingSixAmbientOrdinaryRow where
  toFun
    | .row01 => .row01
    | .row02 => .row04
    | .row03 => .row05
    | .row04 => .row02
    | .row05 => .row03
    | .row06 => .row07
    | .row07 => .row06
    | .row08 => .row09
    | .row09 => .row08
    | .row10 => .row11
    | .row11 => .row10
    | .row12 => .row14
    | .row13 => .row15
    | .row14 => .row12
    | .row15 => .row13
    | .row16 => .row16
    | .row17 => .row17
    | .row18 => .row18
    | .row19 => .row19
    | .row20 => .row20
    | .row21 => .row22
    | .row22 => .row21
    | .row23 => .row23
    | .row24 => .row24
    | .row25 => .row25
    | .row30 => .row31
    | .row31 => .row30
    | .atlasTwelvePowerOne => .atlasTwelvePowerEleven
    | .atlasTwelvePowerTwo => .atlasTwelvePowerSeven
    | .atlasTwelvePowerSeven => .atlasTwelvePowerTwo
    | .atlasTwelvePowerEleven => .atlasTwelvePowerOne
  invFun
    | .row01 => .row01
    | .row02 => .row04
    | .row03 => .row05
    | .row04 => .row02
    | .row05 => .row03
    | .row06 => .row07
    | .row07 => .row06
    | .row08 => .row09
    | .row09 => .row08
    | .row10 => .row11
    | .row11 => .row10
    | .row12 => .row14
    | .row13 => .row15
    | .row14 => .row12
    | .row15 => .row13
    | .row16 => .row16
    | .row17 => .row17
    | .row18 => .row18
    | .row19 => .row19
    | .row20 => .row20
    | .row21 => .row22
    | .row22 => .row21
    | .row23 => .row23
    | .row24 => .row24
    | .row25 => .row25
    | .row30 => .row31
    | .row31 => .row30
    | .atlasTwelvePowerOne => .atlasTwelvePowerEleven
    | .atlasTwelvePowerTwo => .atlasTwelvePowerSeven
    | .atlasTwelvePowerSeven => .atlasTwelvePowerTwo
    | .atlasTwelvePowerEleven => .atlasTwelvePowerOne
  left_inv row := by cases row <;> rfl
  right_inv row := by cases row <;> rfl

@[simp]
theorem alternatingSixAmbientAlphaOneOrdinaryRowAction_dimension
    (row : AlternatingSixAmbientOrdinaryRow) :
    (alternatingSixAmbientAlphaOneOrdinaryRowAction row).dimension =
      row.dimension := by
  cases row <;> rfl

@[simp]
theorem alternatingSixAmbientAlphaTwoOrdinaryRowAction_dimension
    (row : AlternatingSixAmbientOrdinaryRow) :
    (alternatingSixAmbientAlphaTwoOrdinaryRowAction row).dimension =
      row.dimension := by
  cases row <;> rfl

@[simp]
theorem alternatingSixAmbientAlphaOneOrdinaryRowAction_scalarPattern
    (row : AlternatingSixAmbientOrdinaryRow) :
    (alternatingSixAmbientAlphaOneOrdinaryRowAction row).scalarPattern =
      alternatingSixAmbientOuterScalarPattern row.scalarPattern := by
  cases row <;> rfl

@[simp]
theorem alternatingSixAmbientAlphaTwoOrdinaryRowAction_scalarPattern
    (row : AlternatingSixAmbientOrdinaryRow) :
    (alternatingSixAmbientAlphaTwoOrdinaryRowAction row).scalarPattern =
      alternatingSixAmbientOuterScalarPattern row.scalarPattern := by
  cases row <;> rfl

end InductiveMcKay
end McKayConjecture
