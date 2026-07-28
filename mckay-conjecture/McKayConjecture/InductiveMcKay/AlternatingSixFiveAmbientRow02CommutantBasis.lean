/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixCyclotomicField

/-!
# An eigenbasis used for the ambient row 02 commutant

The second presentation generator in ambient row 02 has eigenvalues
`1, ζ³⁰, -ζ³⁰`.  This file records an explicit eigenbasis and its inverse.
Every inverse identity is checked against the proved cyclotomic relation.
-/

noncomputable section

set_option linter.style.longLine false

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- A basis in which the row 02 second generator is diagonal. -/
def alternatingSixFiveAmbientRow02Eigenbasis :
    Matrix (Fin 3) (Fin 3) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [(1, 0), (-1, 20)],
      alternatingSixCyclotomicValue [(1, 10)],
      alternatingSixCyclotomicValue [(-1, 10)]],
    ![alternatingSixCyclotomicValue
        [((1 / 2), 4), ((-1 / 2), 16), ((1 / 2), 20)],
      alternatingSixCyclotomicValue
        [((1 / 2), 2), ((1 / 2), 4), ((-1 / 2), 10),
          ((-1 / 2), 14), ((-1 / 2), 16), ((-1 / 2), 18),
          ((-1 / 2), 20), ((-1 / 2), 22), ((1 / 2), 26)],
      alternatingSixCyclotomicValue
        [((-1 / 2), 2), ((1 / 2), 4), ((1 / 2), 10),
          ((1 / 2), 14), ((-1 / 2), 16), ((1 / 2), 18),
          ((-1 / 2), 20), ((1 / 2), 22), ((-1 / 2), 26)]],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)]]
  ]

/-- The explicitly checked inverse of
`alternatingSixFiveAmbientRow02Eigenbasis`. -/
def alternatingSixFiveAmbientRow02EigenbasisInverse :
    Matrix (Fin 3) (Fin 3) ℂ :=
  ![
    ![alternatingSixCyclotomicValue
        [((1 / 4), 0), ((1 / 4), 8), ((1 / 4), 12),
          ((1 / 4), 20), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue
        [((1 / 2), 0), ((-1 / 4), 4), ((1 / 4), 8),
          ((1 / 4), 12), ((1 / 4), 16), ((-1 / 4), 20),
          ((-1 / 4), 28)],
      alternatingSixCyclotomicValue
        [((-1 / 4), 0), ((-1 / 2), 4), ((1 / 4), 8),
          ((1 / 4), 12), ((1 / 2), 16), ((1 / 4), 20),
          ((-1 / 4), 28)]],
    ![alternatingSixCyclotomicValue
        [((-1 / 8), 0), ((-1 / 8), 2), ((-1 / 8), 8),
          ((3 / 8), 10), ((-1 / 8), 12), ((1 / 8), 18),
          ((-1 / 8), 20), ((1 / 8), 22), ((1 / 8), 28),
          ((-1 / 4), 30)],
      alternatingSixCyclotomicValue
        [((-1 / 4), 0), ((1 / 8), 4), ((-1 / 8), 8),
          ((1 / 8), 10), ((-1 / 8), 12), ((-1 / 8), 14),
          ((-1 / 8), 16), ((1 / 8), 20), ((1 / 8), 26),
          ((1 / 8), 28), ((1 / 4), 30)],
      alternatingSixCyclotomicValue
        [((5 / 8), 0), ((1 / 8), 2), ((1 / 4), 4),
          ((-1 / 8), 8), ((-1 / 8), 10), ((-1 / 8), 12),
          ((-1 / 4), 14), ((-1 / 4), 16), ((-1 / 8), 18),
          ((-1 / 8), 20), ((-1 / 8), 22), ((1 / 4), 26),
          ((1 / 8), 28), ((1 / 4), 30)]],
    ![alternatingSixCyclotomicValue
        [((-1 / 8), 0), ((1 / 8), 2), ((-1 / 8), 8),
          ((-3 / 8), 10), ((-1 / 8), 12), ((-1 / 8), 18),
          ((-1 / 8), 20), ((-1 / 8), 22), ((1 / 8), 28),
          ((1 / 4), 30)],
      alternatingSixCyclotomicValue
        [((-1 / 4), 0), ((1 / 8), 4), ((-1 / 8), 8),
          ((-1 / 8), 10), ((-1 / 8), 12), ((1 / 8), 14),
          ((-1 / 8), 16), ((1 / 8), 20), ((-1 / 8), 26),
          ((1 / 8), 28), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue
        [((5 / 8), 0), ((-1 / 8), 2), ((1 / 4), 4),
          ((-1 / 8), 8), ((1 / 8), 10), ((-1 / 8), 12),
          ((1 / 4), 14), ((-1 / 4), 16), ((1 / 8), 18),
          ((-1 / 8), 20), ((1 / 8), 22), ((-1 / 4), 26),
          ((1 / 8), 28), ((-1 / 4), 30)]]
  ]

macro "close_cyclotomic" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

private theorem row02_eigenbasisInverse_mul_row00
    (j : Fin 3) :
    (alternatingSixFiveAmbientRow02EigenbasisInverse *
        alternatingSixFiveAmbientRow02Eigenbasis) 0 j =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) 0 j := by
  rw [Matrix.mul_apply]
  fin_cases j
  · simp [alternatingSixFiveAmbientRow02EigenbasisInverse,
      alternatingSixFiveAmbientRow02Eigenbasis,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ] <;>
      close_cyclotomic
        (-1 + (3 / 4 : ℂ) * ζ ^ 4 - (3 / 8 : ℂ) * ζ ^ 8 +
          (1 / 8 : ℂ) * ζ ^ 16)
  · simp [alternatingSixFiveAmbientRow02EigenbasisInverse,
      alternatingSixFiveAmbientRow02Eigenbasis,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ] <;>
      close_cyclotomic
        (-(1 / 4 : ℂ) + (1 / 4 : ℂ) * ζ ^ 2 -
          (3 / 8 : ℂ) * ζ ^ 6 + (1 / 8 : ℂ) * ζ ^ 8 +
          (1 / 2 : ℂ) * ζ ^ 10 - (1 / 4 : ℂ) * ζ ^ 14 +
          (1 / 8 : ℂ) * ζ ^ 16 + (1 / 4 : ℂ) * ζ ^ 18 -
          (1 / 8 : ℂ) * ζ ^ 22)
  · simp [alternatingSixFiveAmbientRow02EigenbasisInverse,
      alternatingSixFiveAmbientRow02Eigenbasis,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ] <;>
      close_cyclotomic
        (-(1 / 4 : ℂ) - (1 / 4 : ℂ) * ζ ^ 2 +
          (3 / 8 : ℂ) * ζ ^ 6 + (1 / 8 : ℂ) * ζ ^ 8 -
          (1 / 2 : ℂ) * ζ ^ 10 + (1 / 4 : ℂ) * ζ ^ 14 +
          (1 / 8 : ℂ) * ζ ^ 16 - (1 / 4 : ℂ) * ζ ^ 18 +
          (1 / 8 : ℂ) * ζ ^ 22)

private theorem row02_eigenbasisInverse_mul_row01
    (j : Fin 3) :
    (alternatingSixFiveAmbientRow02EigenbasisInverse *
        alternatingSixFiveAmbientRow02Eigenbasis) 1 j =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) 1 j := by
  rw [Matrix.mul_apply]
  fin_cases j
  · simp [alternatingSixFiveAmbientRow02EigenbasisInverse,
      alternatingSixFiveAmbientRow02Eigenbasis,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ] <;>
      close_cyclotomic
        ((1 / 2 : ℂ) - (3 / 8 : ℂ) * ζ ^ 4 +
          (3 / 16 : ℂ) * ζ ^ 8 + (1 / 4 : ℂ) * ζ ^ 10 -
          (7 / 16 : ℂ) * ζ ^ 14 - (1 / 16 : ℂ) * ζ ^ 16 +
          (3 / 8 : ℂ) * ζ ^ 18)
  · simp [alternatingSixFiveAmbientRow02EigenbasisInverse,
      alternatingSixFiveAmbientRow02Eigenbasis,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ] <;>
      close_cyclotomic
        (-(3 / 8 : ℂ) + (1 / 2 : ℂ) * ζ ^ 4 +
          (1 / 16 : ℂ) * ζ ^ 6 - (9 / 16 : ℂ) * ζ ^ 8 -
          (1 / 4 : ℂ) * ζ ^ 10 - (1 / 16 : ℂ) * ζ ^ 12 +
          (1 / 16 : ℂ) * ζ ^ 14 - (1 / 16 : ℂ) * ζ ^ 16 -
          (1 / 4 : ℂ) * ζ ^ 18 - (3 / 16 : ℂ) * ζ ^ 20 +
          (1 / 16 : ℂ) * ζ ^ 22 + (1 / 8 : ℂ) * ζ ^ 24)
  · simp [alternatingSixFiveAmbientRow02EigenbasisInverse,
      alternatingSixFiveAmbientRow02Eigenbasis,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ] <;>
      close_cyclotomic
        ((5 / 8 : ℂ) + (1 / 4 : ℂ) * ζ ^ 2 -
          (1 / 2 : ℂ) * ζ ^ 4 - (5 / 16 : ℂ) * ζ ^ 6 +
          (7 / 16 : ℂ) * ζ ^ 8 + (1 / 4 : ℂ) * ζ ^ 10 +
          (1 / 16 : ℂ) * ζ ^ 12 - (3 / 16 : ℂ) * ζ ^ 14 -
          (1 / 16 : ℂ) * ζ ^ 16 + (3 / 16 : ℂ) * ζ ^ 20 -
          (1 / 16 : ℂ) * ζ ^ 22 - (1 / 8 : ℂ) * ζ ^ 24)

private theorem row02_eigenbasisInverse_mul_row02
    (j : Fin 3) :
    (alternatingSixFiveAmbientRow02EigenbasisInverse *
        alternatingSixFiveAmbientRow02Eigenbasis) 2 j =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) 2 j := by
  rw [Matrix.mul_apply]
  fin_cases j
  · simp [alternatingSixFiveAmbientRow02EigenbasisInverse,
      alternatingSixFiveAmbientRow02Eigenbasis,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ] <;>
      close_cyclotomic
        ((1 / 2 : ℂ) - (3 / 8 : ℂ) * ζ ^ 4 +
          (3 / 16 : ℂ) * ζ ^ 8 - (1 / 4 : ℂ) * ζ ^ 10 +
          (7 / 16 : ℂ) * ζ ^ 14 - (1 / 16 : ℂ) * ζ ^ 16 -
          (3 / 8 : ℂ) * ζ ^ 18)
  · simp [alternatingSixFiveAmbientRow02EigenbasisInverse,
      alternatingSixFiveAmbientRow02Eigenbasis,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ] <;>
      close_cyclotomic
        ((5 / 8 : ℂ) - (1 / 4 : ℂ) * ζ ^ 2 -
          (1 / 2 : ℂ) * ζ ^ 4 + (5 / 16 : ℂ) * ζ ^ 6 +
          (7 / 16 : ℂ) * ζ ^ 8 - (1 / 4 : ℂ) * ζ ^ 10 +
          (1 / 16 : ℂ) * ζ ^ 12 + (3 / 16 : ℂ) * ζ ^ 14 -
          (1 / 16 : ℂ) * ζ ^ 16 + (3 / 16 : ℂ) * ζ ^ 20 +
          (1 / 16 : ℂ) * ζ ^ 22 - (1 / 8 : ℂ) * ζ ^ 24)
  · simp [alternatingSixFiveAmbientRow02EigenbasisInverse,
      alternatingSixFiveAmbientRow02Eigenbasis,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ] <;>
      close_cyclotomic
        (-(3 / 8 : ℂ) + (1 / 2 : ℂ) * ζ ^ 4 -
          (1 / 16 : ℂ) * ζ ^ 6 - (9 / 16 : ℂ) * ζ ^ 8 +
          (1 / 4 : ℂ) * ζ ^ 10 - (1 / 16 : ℂ) * ζ ^ 12 -
          (1 / 16 : ℂ) * ζ ^ 14 - (1 / 16 : ℂ) * ζ ^ 16 +
          (1 / 4 : ℂ) * ζ ^ 18 - (3 / 16 : ℂ) * ζ ^ 20 -
          (1 / 16 : ℂ) * ζ ^ 22 + (1 / 8 : ℂ) * ζ ^ 24)

/-- The displayed inverse is a left inverse of the row 02 eigenbasis. -/
theorem alternatingSixFiveAmbientRow02EigenbasisInverse_mul :
    alternatingSixFiveAmbientRow02EigenbasisInverse *
        alternatingSixFiveAmbientRow02Eigenbasis =
      1 := by
  ext i j
  fin_cases i
  · exact row02_eigenbasisInverse_mul_row00 j
  · exact row02_eigenbasisInverse_mul_row01 j
  · exact row02_eigenbasisInverse_mul_row02 j

/-- The same displayed matrix is also a right inverse. -/
theorem alternatingSixFiveAmbientRow02Eigenbasis_mul_inverse :
    alternatingSixFiveAmbientRow02Eigenbasis *
        alternatingSixFiveAmbientRow02EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixFiveAmbientRow02EigenbasisInverse_mul

end InductiveMcKay
end McKayConjecture
