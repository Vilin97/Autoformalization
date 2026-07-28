/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow23LongWordProducts

/-!
# Exact traces of the two long positive row-23 words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

theorem alternatingSixAmbientRow23_longState77Reduced_trace :
    (alternatingSixAmbientRow23LongPrefix77 *
      alternatingSixAmbientRow23LongMatrixABBB).trace =
      1 := by
  change
    (∑ i : Fin 10,
      (alternatingSixAmbientRow23LongPrefix77 *
        alternatingSixAmbientRow23LongMatrixABBB) i i) =
      1
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixAmbientRow23LongMatrixABBB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]

theorem alternatingSixAmbientRow23_longState79Reduced_trace :
    (alternatingSixAmbientRow23LongPrefix79 *
      alternatingSixAmbientRow23LongMatrixABB).trace =
      1 := by
  change
    (∑ i : Fin 10,
      (alternatingSixAmbientRow23LongPrefix79 *
        alternatingSixAmbientRow23LongMatrixABB) i i) =
      1
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongPrefix79,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]

/-- Trace of the positive word `ababbabbb`. -/
theorem alternatingSixAmbientRow23_positiveState77_trace :
    (alternatingSixFiveAmbient_row23_matrixA *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixA *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixA *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixB).trace =
      1 := by
  rw [show
    alternatingSixFiveAmbient_row23_matrixA *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixA *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixA *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixB =
        (alternatingSixFiveAmbient_row23_matrixA *
          alternatingSixFiveAmbient_row23_matrixB) *
        ((alternatingSixFiveAmbient_row23_matrixA *
            alternatingSixFiveAmbient_row23_matrixB) *
          alternatingSixFiveAmbient_row23_matrixB) *
        (((alternatingSixFiveAmbient_row23_matrixA *
              alternatingSixFiveAmbient_row23_matrixB) *
            alternatingSixFiveAmbient_row23_matrixB) *
          alternatingSixFiveAmbient_row23_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow23_longMatrixABBB_eq,
    alternatingSixAmbientRow23_longMatrixABB_eq,
    alternatingSixAmbientRow23_longMatrixAB_eq,
    alternatingSixAmbientRow23_longPrefix77_mul]
  exact alternatingSixAmbientRow23_longState77Reduced_trace

/-- Trace of the positive word `ababbbabb`. -/
theorem alternatingSixAmbientRow23_positiveState79_trace :
    (alternatingSixFiveAmbient_row23_matrixA *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixA *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixA *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixB).trace =
      1 := by
  rw [show
    alternatingSixFiveAmbient_row23_matrixA *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixA *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixA *
      alternatingSixFiveAmbient_row23_matrixB *
      alternatingSixFiveAmbient_row23_matrixB =
        (alternatingSixFiveAmbient_row23_matrixA *
          alternatingSixFiveAmbient_row23_matrixB) *
        (((alternatingSixFiveAmbient_row23_matrixA *
              alternatingSixFiveAmbient_row23_matrixB) *
            alternatingSixFiveAmbient_row23_matrixB) *
          alternatingSixFiveAmbient_row23_matrixB) *
        ((alternatingSixFiveAmbient_row23_matrixA *
            alternatingSixFiveAmbient_row23_matrixB) *
          alternatingSixFiveAmbient_row23_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow23_longMatrixABBB_eq,
    alternatingSixAmbientRow23_longMatrixABB_eq,
    alternatingSixAmbientRow23_longMatrixAB_eq,
    alternatingSixAmbientRow23_longPrefix79_mul]
  exact alternatingSixAmbientRow23_longState79Reduced_trace

end InductiveMcKay
end McKayConjecture
