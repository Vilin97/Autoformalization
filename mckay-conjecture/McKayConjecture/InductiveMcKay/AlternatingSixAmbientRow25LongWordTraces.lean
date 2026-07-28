/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25LongWordProducts

/-!
# Exact traces of the two long positive row-25 words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem alternatingSixAmbientRow25_longState77Reduced_trace :
    (alternatingSixAmbientRow25LongPrefix77 *
      alternatingSixAmbientRow25LongMatrixABBB).trace =
      1 := by
  change
    (∑ i : Fin 10,
      (alternatingSixAmbientRow25LongPrefix77 *
        alternatingSixAmbientRow25LongMatrixABBB) i i) =
      1
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongPrefix77,
    alternatingSixAmbientRow25LongMatrixABBB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((16 / 3) : ℂ)
          - ((16 / 3) : ℂ) * ζ ^ 4
          + ((8 / 3) : ℂ) * ζ ^ 5
          + ((16 / 3) : ℂ) * ζ ^ 8
          - ((8 / 3) : ℂ) * ζ ^ 9
          - ((10 / 3) : ℂ) * ζ ^ 10
          + ((8 / 3) : ℂ) * ζ ^ 13
          + ((10 / 3) : ℂ) * ζ ^ 14
          + ((1 / 6) : ℂ) * ζ ^ 15
          - ((10 / 3) : ℂ) * ζ ^ 18
          - ((1 / 6) : ℂ) * ζ ^ 19
          + ((7 / 6) : ℂ) * ζ ^ 20
          + ((1 / 6) : ℂ) * ζ ^ 23
          - ((7 / 6) : ℂ) * ζ ^ 24
          + ((7 / 6) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((
        ((16 / 3) : ℂ)
          - ((16 / 3) : ℂ) * ζ ^ 4
          + ((8 / 3) : ℂ) * ζ ^ 5
          + ((16 / 3) : ℂ) * ζ ^ 8
          - ((8 / 3) : ℂ) * ζ ^ 9
          - ((10 / 3) : ℂ) * ζ ^ 10
          + ((8 / 3) : ℂ) * ζ ^ 13
          + ((10 / 3) : ℂ) * ζ ^ 14
          + ((1 / 6) : ℂ) * ζ ^ 15
          - ((10 / 3) : ℂ) * ζ ^ 18
          - ((1 / 6) : ℂ) * ζ ^ 19
          + ((7 / 6) : ℂ) * ζ ^ 20
          + ((1 / 6) : ℂ) * ζ ^ 23
          - ((7 / 6) : ℂ) * ζ ^ 24
          + ((7 / 6) : ℂ) * ζ ^ 28
      ))) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem alternatingSixAmbientRow25_longState79Reduced_trace :
    (alternatingSixAmbientRow25LongPrefix79 *
      alternatingSixAmbientRow25LongMatrixABB).trace =
      1 := by
  change
    (∑ i : Fin 10,
      (alternatingSixAmbientRow25LongPrefix79 *
        alternatingSixAmbientRow25LongMatrixABB) i i) =
      1
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongPrefix79,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((31 / 6) : ℂ)
          + ((31 / 6) : ℂ) * ζ ^ 4
          - ((14 / 3) : ℂ) * ζ ^ 5
          - ((31 / 6) : ℂ) * ζ ^ 8
          + ((14 / 3) : ℂ) * ζ ^ 9
          + ((3 / 2) : ℂ) * ζ ^ 10
          - ((14 / 3) : ℂ) * ζ ^ 13
          - ((3 / 2) : ℂ) * ζ ^ 14
          + ((1 / 3) : ℂ) * ζ ^ 15
          + ((3 / 2) : ℂ) * ζ ^ 18
          - ((1 / 3) : ℂ) * ζ ^ 19
          + ((23 / 6) : ℂ) * ζ ^ 20
          + ((1 / 3) : ℂ) * ζ ^ 23
          - ((23 / 6) : ℂ) * ζ ^ 24
          + ((23 / 6) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((
        -((31 / 6) : ℂ)
          + ((31 / 6) : ℂ) * ζ ^ 4
          - ((14 / 3) : ℂ) * ζ ^ 5
          - ((31 / 6) : ℂ) * ζ ^ 8
          + ((14 / 3) : ℂ) * ζ ^ 9
          + ((3 / 2) : ℂ) * ζ ^ 10
          - ((14 / 3) : ℂ) * ζ ^ 13
          - ((3 / 2) : ℂ) * ζ ^ 14
          + ((1 / 3) : ℂ) * ζ ^ 15
          + ((3 / 2) : ℂ) * ζ ^ 18
          - ((1 / 3) : ℂ) * ζ ^ 19
          + ((23 / 6) : ℂ) * ζ ^ 20
          + ((1 / 3) : ℂ) * ζ ^ 23
          - ((23 / 6) : ℂ) * ζ ^ 24
          + ((23 / 6) : ℂ) * ζ ^ 28
      ))) *
        alternatingSixComplexCyclotomicRoot_relation

/-- Trace of the positive word `ababbabbb`. -/
theorem alternatingSixAmbientRow25_positiveState77_trace :
    (alternatingSixFiveAmbient_row25_matrixA *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixA *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixA *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixB).trace =
      1 := by
  rw [show
    alternatingSixFiveAmbient_row25_matrixA *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixA *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixA *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixB =
        (alternatingSixFiveAmbient_row25_matrixA *
          alternatingSixFiveAmbient_row25_matrixB) *
        ((alternatingSixFiveAmbient_row25_matrixA *
            alternatingSixFiveAmbient_row25_matrixB) *
          alternatingSixFiveAmbient_row25_matrixB) *
        (((alternatingSixFiveAmbient_row25_matrixA *
              alternatingSixFiveAmbient_row25_matrixB) *
            alternatingSixFiveAmbient_row25_matrixB) *
          alternatingSixFiveAmbient_row25_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow25_longMatrixABBB_eq,
    alternatingSixAmbientRow25_longMatrixABB_eq,
    alternatingSixAmbientRow25_longMatrixAB_eq,
    alternatingSixAmbientRow25_longPrefix77_mul]
  exact alternatingSixAmbientRow25_longState77Reduced_trace

/-- Trace of the positive word `ababbbabb`. -/
theorem alternatingSixAmbientRow25_positiveState79_trace :
    (alternatingSixFiveAmbient_row25_matrixA *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixA *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixA *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixB).trace =
      1 := by
  rw [show
    alternatingSixFiveAmbient_row25_matrixA *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixA *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixA *
      alternatingSixFiveAmbient_row25_matrixB *
      alternatingSixFiveAmbient_row25_matrixB =
        (alternatingSixFiveAmbient_row25_matrixA *
          alternatingSixFiveAmbient_row25_matrixB) *
        (((alternatingSixFiveAmbient_row25_matrixA *
              alternatingSixFiveAmbient_row25_matrixB) *
            alternatingSixFiveAmbient_row25_matrixB) *
          alternatingSixFiveAmbient_row25_matrixB) *
        ((alternatingSixFiveAmbient_row25_matrixA *
            alternatingSixFiveAmbient_row25_matrixB) *
          alternatingSixFiveAmbient_row25_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow25_longMatrixABBB_eq,
    alternatingSixAmbientRow25_longMatrixABB_eq,
    alternatingSixAmbientRow25_longMatrixAB_eq,
    alternatingSixAmbientRow25_longPrefix79_mul]
  exact alternatingSixAmbientRow25_longState79Reduced_trace

end InductiveMcKay
end McKayConjecture
