/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow20LongWordProducts

/-!
# Exact traces of the two long positive row-20 words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

theorem alternatingSixAmbientRow20_longState77Reduced_trace :
    (alternatingSixAmbientRow20LongPrefix77 *
      alternatingSixAmbientRow20LongMatrixABBB).trace =
      0 := by
  change
    (∑ i : Fin 9,
      (alternatingSixAmbientRow20LongPrefix77 *
        alternatingSixAmbientRow20LongMatrixABBB) i i) =
      0
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixAmbientRow20LongMatrixABBB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]; ring

theorem alternatingSixAmbientRow20_longState79Reduced_trace :
    (alternatingSixAmbientRow20LongPrefix79 *
      alternatingSixAmbientRow20LongMatrixABB).trace =
      0 := by
  change
    (∑ i : Fin 9,
      (alternatingSixAmbientRow20LongPrefix79 *
        alternatingSixAmbientRow20LongMatrixABB) i i) =
      0
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongPrefix79,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]; ring

/-- Trace of the positive word `ababbabbb`. -/
theorem alternatingSixAmbientRow20_positiveState77_trace :
    (alternatingSixFiveAmbient_row20_matrixA *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixA *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixA *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_row20_matrixA *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixA *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixA *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixB =
        (alternatingSixFiveAmbient_row20_matrixA *
          alternatingSixFiveAmbient_row20_matrixB) *
        ((alternatingSixFiveAmbient_row20_matrixA *
            alternatingSixFiveAmbient_row20_matrixB) *
          alternatingSixFiveAmbient_row20_matrixB) *
        (((alternatingSixFiveAmbient_row20_matrixA *
              alternatingSixFiveAmbient_row20_matrixB) *
            alternatingSixFiveAmbient_row20_matrixB) *
          alternatingSixFiveAmbient_row20_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow20_longMatrixABBB_eq,
    alternatingSixAmbientRow20_longMatrixABB_eq,
    alternatingSixAmbientRow20_longMatrixAB_eq,
    alternatingSixAmbientRow20_longPrefix77_mul]
  exact alternatingSixAmbientRow20_longState77Reduced_trace

/-- Trace of the positive word `ababbbabb`. -/
theorem alternatingSixAmbientRow20_positiveState79_trace :
    (alternatingSixFiveAmbient_row20_matrixA *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixA *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixA *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_row20_matrixA *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixA *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixA *
      alternatingSixFiveAmbient_row20_matrixB *
      alternatingSixFiveAmbient_row20_matrixB =
        (alternatingSixFiveAmbient_row20_matrixA *
          alternatingSixFiveAmbient_row20_matrixB) *
        (((alternatingSixFiveAmbient_row20_matrixA *
              alternatingSixFiveAmbient_row20_matrixB) *
            alternatingSixFiveAmbient_row20_matrixB) *
          alternatingSixFiveAmbient_row20_matrixB) *
        ((alternatingSixFiveAmbient_row20_matrixA *
            alternatingSixFiveAmbient_row20_matrixB) *
          alternatingSixFiveAmbient_row20_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow20_longMatrixABBB_eq,
    alternatingSixAmbientRow20_longMatrixABB_eq,
    alternatingSixAmbientRow20_longMatrixAB_eq,
    alternatingSixAmbientRow20_longPrefix79_mul]
  exact alternatingSixAmbientRow20_longState79Reduced_trace

end InductiveMcKay
end McKayConjecture
