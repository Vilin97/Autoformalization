/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow21LongWordProducts

/-!
# Exact traces of the two long positive row-21 words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

theorem alternatingSixAmbientRow21_longState77Reduced_trace :
    (alternatingSixAmbientRow21LongPrefix77 *
      alternatingSixAmbientRow21LongMatrixABBB).trace =
      0 := by
  change
    (∑ i : Fin 9,
      (alternatingSixAmbientRow21LongPrefix77 *
        alternatingSixAmbientRow21LongMatrixABBB) i i) =
      0
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow21LongPrefix77,
    alternatingSixAmbientRow21LongMatrixABBB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-((13 / 9) : ℂ) + ((13 / 9) : ℂ) * ζ ^ 4 - ((13 / 9) : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((-((13 / 9) : ℂ) + ((13 / 9) : ℂ) * ζ ^ 4 - ((13 / 9) : ℂ) * ζ ^ 8))) *
        alternatingSixComplexCyclotomicRoot_relation

theorem alternatingSixAmbientRow21_longState79Reduced_trace :
    (alternatingSixAmbientRow21LongPrefix79 *
      alternatingSixAmbientRow21LongMatrixABB).trace =
      0 := by
  change
    (∑ i : Fin 9,
      (alternatingSixAmbientRow21LongPrefix79 *
        alternatingSixAmbientRow21LongMatrixABB) i i) =
      0
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow21LongPrefix79,
    alternatingSixAmbientRow21LongMatrixABB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-((1 / 6) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((-((1 / 6) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8))) *
        alternatingSixComplexCyclotomicRoot_relation

/-- Trace of the positive word `ababbabbb`. -/
theorem alternatingSixAmbientRow21_positiveState77_trace :
    (alternatingSixFiveAmbient_row21_matrixA *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixA *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixA *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_row21_matrixA *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixA *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixA *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixB =
        (alternatingSixFiveAmbient_row21_matrixA *
          alternatingSixFiveAmbient_row21_matrixB) *
        ((alternatingSixFiveAmbient_row21_matrixA *
            alternatingSixFiveAmbient_row21_matrixB) *
          alternatingSixFiveAmbient_row21_matrixB) *
        (((alternatingSixFiveAmbient_row21_matrixA *
              alternatingSixFiveAmbient_row21_matrixB) *
            alternatingSixFiveAmbient_row21_matrixB) *
          alternatingSixFiveAmbient_row21_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow21_longMatrixABBB_eq,
    alternatingSixAmbientRow21_longMatrixABB_eq,
    alternatingSixAmbientRow21_longMatrixAB_eq,
    alternatingSixAmbientRow21_longPrefix77_mul]
  exact alternatingSixAmbientRow21_longState77Reduced_trace

/-- Trace of the positive word `ababbbabb`. -/
theorem alternatingSixAmbientRow21_positiveState79_trace :
    (alternatingSixFiveAmbient_row21_matrixA *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixA *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixA *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_row21_matrixA *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixA *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixA *
      alternatingSixFiveAmbient_row21_matrixB *
      alternatingSixFiveAmbient_row21_matrixB =
        (alternatingSixFiveAmbient_row21_matrixA *
          alternatingSixFiveAmbient_row21_matrixB) *
        (((alternatingSixFiveAmbient_row21_matrixA *
              alternatingSixFiveAmbient_row21_matrixB) *
            alternatingSixFiveAmbient_row21_matrixB) *
          alternatingSixFiveAmbient_row21_matrixB) *
        ((alternatingSixFiveAmbient_row21_matrixA *
            alternatingSixFiveAmbient_row21_matrixB) *
          alternatingSixFiveAmbient_row21_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow21_longMatrixABBB_eq,
    alternatingSixAmbientRow21_longMatrixABB_eq,
    alternatingSixAmbientRow21_longMatrixAB_eq,
    alternatingSixAmbientRow21_longPrefix79_mul]
  exact alternatingSixAmbientRow21_longState79Reduced_trace

end InductiveMcKay
end McKayConjecture
