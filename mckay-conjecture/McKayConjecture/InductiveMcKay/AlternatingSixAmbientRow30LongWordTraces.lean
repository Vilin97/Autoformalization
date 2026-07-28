/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow30LongWordProducts

/-!
# Exact traces of the two long positive row-30 words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

theorem alternatingSixAmbientRow30_longState77Reduced_trace :
    (alternatingSixAmbientRow30LongPrefix77 *
      alternatingSixAmbientRow30LongMatrixABBB).trace =
      0 := by
  change
    (∑ i : Fin 15,
      (alternatingSixAmbientRow30LongPrefix77 *
        alternatingSixAmbientRow30LongMatrixABBB) i i) =
      0
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongPrefix77,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  all_goals ring

theorem alternatingSixAmbientRow30_longState79Reduced_trace :
    (alternatingSixAmbientRow30LongPrefix79 *
      alternatingSixAmbientRow30LongMatrixABB).trace =
      0 := by
  change
    (∑ i : Fin 15,
      (alternatingSixAmbientRow30LongPrefix79 *
        alternatingSixAmbientRow30LongMatrixABB) i i) =
      0
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongPrefix79,
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  all_goals ring

/-- Trace of the positive word `ababbabbb`. -/
theorem alternatingSixAmbientRow30_positiveState77_trace :
    (alternatingSixFiveAmbient_row30_matrixA *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixA *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixA *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_row30_matrixA *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixA *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixA *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixB =
        (alternatingSixFiveAmbient_row30_matrixA *
          alternatingSixFiveAmbient_row30_matrixB) *
        ((alternatingSixFiveAmbient_row30_matrixA *
            alternatingSixFiveAmbient_row30_matrixB) *
          alternatingSixFiveAmbient_row30_matrixB) *
        (((alternatingSixFiveAmbient_row30_matrixA *
              alternatingSixFiveAmbient_row30_matrixB) *
            alternatingSixFiveAmbient_row30_matrixB) *
          alternatingSixFiveAmbient_row30_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow30_longMatrixABBB_eq,
    alternatingSixAmbientRow30_longMatrixABB_eq,
    alternatingSixAmbientRow30_longMatrixAB_eq,
    alternatingSixAmbientRow30_longPrefix77_mul]
  exact alternatingSixAmbientRow30_longState77Reduced_trace

/-- Trace of the positive word `ababbbabb`. -/
theorem alternatingSixAmbientRow30_positiveState79_trace :
    (alternatingSixFiveAmbient_row30_matrixA *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixA *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixA *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_row30_matrixA *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixA *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixA *
      alternatingSixFiveAmbient_row30_matrixB *
      alternatingSixFiveAmbient_row30_matrixB =
        (alternatingSixFiveAmbient_row30_matrixA *
          alternatingSixFiveAmbient_row30_matrixB) *
        (((alternatingSixFiveAmbient_row30_matrixA *
              alternatingSixFiveAmbient_row30_matrixB) *
            alternatingSixFiveAmbient_row30_matrixB) *
          alternatingSixFiveAmbient_row30_matrixB) *
        ((alternatingSixFiveAmbient_row30_matrixA *
            alternatingSixFiveAmbient_row30_matrixB) *
          alternatingSixFiveAmbient_row30_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow30_longMatrixABBB_eq,
    alternatingSixAmbientRow30_longMatrixABB_eq,
    alternatingSixAmbientRow30_longMatrixAB_eq,
    alternatingSixAmbientRow30_longPrefix79_mul]
  exact alternatingSixAmbientRow30_longState79Reduced_trace

end InductiveMcKay
end McKayConjecture
