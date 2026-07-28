/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

/-!
# Explicit finite permutation data for two covers of `A₆`

We realize `F_{p²}` as pairs `(a,b)`, denoting `a + b z` with
`z² = z + 1`.  The four permutations below are the actions on `F₉²`
and `F₄³` of corrected ATLAS matrices.  Writing the permutations in
coordinates avoids any dependence on a finite-field or matrix library
in the final certificate.

The raw matrices and the correction are independently checked by
`scripts/a6_cover_permutations.py`.
-/

namespace McKayConjecture
namespace GroupTheory

/-- The coordinate model `F_{p²} = F_p[z]/(z²-z-1)`. -/
abbrev AlternatingSixQuadraticFieldCoordinates (p : ℕ) :=
  Fin p × Fin p

/-- Addition in the coordinate model of `F_{p²}`. -/
def alternatingSixQuadraticAdd {p : ℕ} [NeZero p]
    (x y : AlternatingSixQuadraticFieldCoordinates p) :
    AlternatingSixQuadraticFieldCoordinates p :=
  (x.1 + y.1, x.2 + y.2)

/-- Multiplication in the coordinate model, using `z² = z + 1`. -/
def alternatingSixQuadraticMul {p : ℕ} [NeZero p]
    (x y : AlternatingSixQuadraticFieldCoordinates p) :
    AlternatingSixQuadraticFieldCoordinates p :=
  (x.1 * y.1 + x.2 * y.2,
    x.1 * y.2 + x.2 * y.1 + x.2 * y.2)

local infixl:65 " +q " => alternatingSixQuadraticAdd
local infixl:70 " *q " => alternatingSixQuadraticMul

/-- The 81-point set underlying the double-cover representation. -/
abbrev AlternatingSixDoubleCoverSpace :=
  AlternatingSixQuadraticFieldCoordinates 3 ×
    AlternatingSixQuadraticFieldCoordinates 3

/-- The corrected first double-cover matrix, as a permutation of `F₉²`. -/
def alternatingSixDoubleCoverPermutationA :
    Equiv.Perm AlternatingSixDoubleCoverSpace where
  toFun x :=
    ((1, 1) *q x.1,
      (2, 1) *q x.1 +q (2, 2) *q x.2)
  invFun x :=
    ((2, 2) *q x.1,
      (1, 2) *q x.1 +q (1, 1) *q x.2)
  left_inv := by decide
  right_inv := by decide

/-- The second double-cover matrix, as a permutation of `F₉²`. -/
def alternatingSixDoubleCoverPermutationB :
    Equiv.Perm AlternatingSixDoubleCoverSpace where
  toFun x :=
    (x.2, (2, 0) *q x.1 +q (1, 1) *q x.2)
  invFun x :=
    ((1, 1) *q x.1 +q (2, 0) *q x.2, x.1)
  left_inv := by decide
  right_inv := by decide

/-- The 64-point set underlying the triple-cover representation. -/
abbrev AlternatingSixTripleCoverSpace :=
  AlternatingSixQuadraticFieldCoordinates 2 ×
    AlternatingSixQuadraticFieldCoordinates 2 ×
      AlternatingSixQuadraticFieldCoordinates 2

/-- The corrected first triple-cover matrix, as a permutation of `F₄³`. -/
def alternatingSixTripleCoverPermutationA :
    Equiv.Perm AlternatingSixTripleCoverSpace where
  toFun x :=
    ((1, 1) *q x.1,
      (1, 1) *q x.2.2,
      (1, 1) *q x.2.1)
  invFun x :=
    ((0, 1) *q x.1,
      (0, 1) *q x.2.2,
      (0, 1) *q x.2.1)
  left_inv := by decide
  right_inv := by decide

/-- The second triple-cover matrix, as a permutation of `F₄³`. -/
def alternatingSixTripleCoverPermutationB :
    Equiv.Perm AlternatingSixTripleCoverSpace where
  toFun x :=
    (x.2.1,
      x.1,
      x.1 +q (0, 1) *q x.2.1 +q x.2.2)
  invFun x :=
    (x.2.1,
      x.1,
      (0, 1) *q x.1 +q x.2.1 +q x.2.2)
  left_inv := by decide
  right_inv := by decide

end GroupTheory
end McKayConjecture
