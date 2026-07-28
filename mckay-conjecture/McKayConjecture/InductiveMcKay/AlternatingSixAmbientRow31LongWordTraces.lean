/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow31LongWordProducts

/-!
# Exact traces of the two long positive row-31 words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem alternatingSixAmbientRow31_longState77Reduced_trace :
    (alternatingSixAmbientRow31LongPrefix77 *
      alternatingSixAmbientRow31LongMatrixABBB).trace =
      0 := by
  change
    (∑ i : Fin 15,
      (alternatingSixAmbientRow31LongPrefix77 *
        alternatingSixAmbientRow31LongMatrixABBB) i i) =
      0
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow31LongPrefix77,
    alternatingSixAmbientRow31LongMatrixABBB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((6 : ℂ) - (6 : ℂ) * ζ ^ 4 + (6 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(((6 : ℂ) - (6 : ℂ) * ζ ^ 4 + (6 : ℂ) * ζ ^ 8))) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem alternatingSixAmbientRow31_longState79Reduced_trace :
    (alternatingSixAmbientRow31LongPrefix79 *
      alternatingSixAmbientRow31LongMatrixABB).trace =
      0 := by
  change
    (∑ i : Fin 15,
      (alternatingSixAmbientRow31LongPrefix79 *
        alternatingSixAmbientRow31LongMatrixABB) i i) =
      0
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow31LongPrefix79,
    alternatingSixAmbientRow31LongMatrixABB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(((2 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8))) *
        alternatingSixComplexCyclotomicRoot_relation

/-- Trace of the positive word `ababbabbb`. -/
theorem alternatingSixAmbientRow31_positiveState77_trace :
    (alternatingSixFiveAmbient_row31_matrixA *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixA *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixA *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_row31_matrixA *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixA *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixA *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixB =
        (alternatingSixFiveAmbient_row31_matrixA *
          alternatingSixFiveAmbient_row31_matrixB) *
        ((alternatingSixFiveAmbient_row31_matrixA *
            alternatingSixFiveAmbient_row31_matrixB) *
          alternatingSixFiveAmbient_row31_matrixB) *
        (((alternatingSixFiveAmbient_row31_matrixA *
              alternatingSixFiveAmbient_row31_matrixB) *
            alternatingSixFiveAmbient_row31_matrixB) *
          alternatingSixFiveAmbient_row31_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow31_longMatrixABBB_eq,
    alternatingSixAmbientRow31_longMatrixABB_eq,
    alternatingSixAmbientRow31_longMatrixAB_eq,
    alternatingSixAmbientRow31_longPrefix77_mul]
  exact alternatingSixAmbientRow31_longState77Reduced_trace

/-- Trace of the positive word `ababbbabb`. -/
theorem alternatingSixAmbientRow31_positiveState79_trace :
    (alternatingSixFiveAmbient_row31_matrixA *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixA *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixA *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_row31_matrixA *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixA *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixA *
      alternatingSixFiveAmbient_row31_matrixB *
      alternatingSixFiveAmbient_row31_matrixB =
        (alternatingSixFiveAmbient_row31_matrixA *
          alternatingSixFiveAmbient_row31_matrixB) *
        (((alternatingSixFiveAmbient_row31_matrixA *
              alternatingSixFiveAmbient_row31_matrixB) *
            alternatingSixFiveAmbient_row31_matrixB) *
          alternatingSixFiveAmbient_row31_matrixB) *
        ((alternatingSixFiveAmbient_row31_matrixA *
            alternatingSixFiveAmbient_row31_matrixB) *
          alternatingSixFiveAmbient_row31_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow31_longMatrixABBB_eq,
    alternatingSixAmbientRow31_longMatrixABB_eq,
    alternatingSixAmbientRow31_longMatrixAB_eq,
    alternatingSixAmbientRow31_longPrefix79_mul]
  exact alternatingSixAmbientRow31_longState79Reduced_trace

end InductiveMcKay
end McKayConjecture
