/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24LongWordProducts

/-!
# Exact traces of the two long positive row-24 words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem alternatingSixAmbientRow24_longState77Reduced_trace :
    (alternatingSixAmbientRow24LongPrefix77 *
      alternatingSixAmbientRow24LongMatrixABBB).trace =
      1 := by
  change
    (∑ i : Fin 10,
      (alternatingSixAmbientRow24LongPrefix77 *
        alternatingSixAmbientRow24LongMatrixABBB) i i) =
      1
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((9 / 2) : ℂ)
          + ((9 / 2) : ℂ) * ζ ^ 4
          - ((197 / 34) : ℂ) * ζ ^ 5
          - ((9 / 2) : ℂ) * ζ ^ 8
          + ((197 / 34) : ℂ) * ζ ^ 9
          - ((10 / 17) : ℂ) * ζ ^ 10
          - ((197 / 34) : ℂ) * ζ ^ 13
          + ((10 / 17) : ℂ) * ζ ^ 14
          - ((21 / 34) : ℂ) * ζ ^ 15
          - ((10 / 17) : ℂ) * ζ ^ 18
          + ((21 / 34) : ℂ) * ζ ^ 19
          - ((183 / 34) : ℂ) * ζ ^ 20
          - ((21 / 34) : ℂ) * ζ ^ 23
          + ((183 / 34) : ℂ) * ζ ^ 24
          - ((183 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((
        -((9 / 2) : ℂ)
          + ((9 / 2) : ℂ) * ζ ^ 4
          - ((197 / 34) : ℂ) * ζ ^ 5
          - ((9 / 2) : ℂ) * ζ ^ 8
          + ((197 / 34) : ℂ) * ζ ^ 9
          - ((10 / 17) : ℂ) * ζ ^ 10
          - ((197 / 34) : ℂ) * ζ ^ 13
          + ((10 / 17) : ℂ) * ζ ^ 14
          - ((21 / 34) : ℂ) * ζ ^ 15
          - ((10 / 17) : ℂ) * ζ ^ 18
          + ((21 / 34) : ℂ) * ζ ^ 19
          - ((183 / 34) : ℂ) * ζ ^ 20
          - ((21 / 34) : ℂ) * ζ ^ 23
          + ((183 / 34) : ℂ) * ζ ^ 24
          - ((183 / 34) : ℂ) * ζ ^ 28
      ))) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem alternatingSixAmbientRow24_longState79Reduced_trace :
    (alternatingSixAmbientRow24LongPrefix79 *
      alternatingSixAmbientRow24LongMatrixABB).trace =
      1 := by
  change
    (∑ i : Fin 10,
      (alternatingSixAmbientRow24LongPrefix79 *
        alternatingSixAmbientRow24LongMatrixABB) i i) =
      1
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((45 / 17) : ℂ)
          + ((45 / 17) : ℂ) * ζ ^ 4
          + ((345 / 34) : ℂ) * ζ ^ 5
          - ((45 / 17) : ℂ) * ζ ^ 8
          - ((345 / 34) : ℂ) * ζ ^ 9
          + ((387 / 34) : ℂ) * ζ ^ 10
          + ((345 / 34) : ℂ) * ζ ^ 13
          - ((387 / 34) : ℂ) * ζ ^ 14
          + ((117 / 34) : ℂ) * ζ ^ 15
          + ((387 / 34) : ℂ) * ζ ^ 18
          - ((117 / 34) : ℂ) * ζ ^ 19
          + ((193 / 17) : ℂ) * ζ ^ 20
          + ((117 / 34) : ℂ) * ζ ^ 23
          - ((193 / 17) : ℂ) * ζ ^ 24
          + ((193 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((
        -((45 / 17) : ℂ)
          + ((45 / 17) : ℂ) * ζ ^ 4
          + ((345 / 34) : ℂ) * ζ ^ 5
          - ((45 / 17) : ℂ) * ζ ^ 8
          - ((345 / 34) : ℂ) * ζ ^ 9
          + ((387 / 34) : ℂ) * ζ ^ 10
          + ((345 / 34) : ℂ) * ζ ^ 13
          - ((387 / 34) : ℂ) * ζ ^ 14
          + ((117 / 34) : ℂ) * ζ ^ 15
          + ((387 / 34) : ℂ) * ζ ^ 18
          - ((117 / 34) : ℂ) * ζ ^ 19
          + ((193 / 17) : ℂ) * ζ ^ 20
          + ((117 / 34) : ℂ) * ζ ^ 23
          - ((193 / 17) : ℂ) * ζ ^ 24
          + ((193 / 17) : ℂ) * ζ ^ 28
      ))) *
        alternatingSixComplexCyclotomicRoot_relation

/-- Trace of the positive word `ababbabbb`. -/
theorem alternatingSixAmbientRow24_positiveState77_trace :
    (alternatingSixFiveAmbient_row24_matrixA *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixA *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixA *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixB).trace =
      1 := by
  rw [show
    alternatingSixFiveAmbient_row24_matrixA *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixA *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixA *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixB =
        (alternatingSixFiveAmbient_row24_matrixA *
          alternatingSixFiveAmbient_row24_matrixB) *
        ((alternatingSixFiveAmbient_row24_matrixA *
            alternatingSixFiveAmbient_row24_matrixB) *
          alternatingSixFiveAmbient_row24_matrixB) *
        (((alternatingSixFiveAmbient_row24_matrixA *
              alternatingSixFiveAmbient_row24_matrixB) *
            alternatingSixFiveAmbient_row24_matrixB) *
          alternatingSixFiveAmbient_row24_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow24_longMatrixABBB_eq,
    alternatingSixAmbientRow24_longMatrixABB_eq,
    alternatingSixAmbientRow24_longMatrixAB_eq,
    alternatingSixAmbientRow24_longPrefix77_mul]
  exact alternatingSixAmbientRow24_longState77Reduced_trace

/-- Trace of the positive word `ababbbabb`. -/
theorem alternatingSixAmbientRow24_positiveState79_trace :
    (alternatingSixFiveAmbient_row24_matrixA *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixA *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixA *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixB).trace =
      1 := by
  rw [show
    alternatingSixFiveAmbient_row24_matrixA *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixA *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixA *
      alternatingSixFiveAmbient_row24_matrixB *
      alternatingSixFiveAmbient_row24_matrixB =
        (alternatingSixFiveAmbient_row24_matrixA *
          alternatingSixFiveAmbient_row24_matrixB) *
        (((alternatingSixFiveAmbient_row24_matrixA *
              alternatingSixFiveAmbient_row24_matrixB) *
            alternatingSixFiveAmbient_row24_matrixB) *
          alternatingSixFiveAmbient_row24_matrixB) *
        ((alternatingSixFiveAmbient_row24_matrixA *
            alternatingSixFiveAmbient_row24_matrixB) *
          alternatingSixFiveAmbient_row24_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow24_longMatrixABBB_eq,
    alternatingSixAmbientRow24_longMatrixABB_eq,
    alternatingSixAmbientRow24_longMatrixAB_eq,
    alternatingSixAmbientRow24_longPrefix79_mul]
  exact alternatingSixAmbientRow24_longState79Reduced_trace

end InductiveMcKay
end McKayConjecture
