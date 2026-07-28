/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow22LongWordProducts

/-!
# Exact traces of the two long positive row-22 words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem alternatingSixAmbientRow22_longState77Reduced_trace :
    (alternatingSixAmbientRow22LongPrefix77 *
      alternatingSixAmbientRow22LongMatrixABBB).trace =
      0 := by
  change
    (∑ i : Fin 9,
      (alternatingSixAmbientRow22LongPrefix77 *
        alternatingSixAmbientRow22LongMatrixABBB) i i) =
      0
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongPrefix77,
    alternatingSixAmbientRow22LongMatrixABBB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((9 : ℂ) - (9 : ℂ) * ζ ^ 4 + (9 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(((9 : ℂ) - (9 : ℂ) * ζ ^ 4 + (9 : ℂ) * ζ ^ 8))) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem alternatingSixAmbientRow22_longState79Reduced_trace :
    (alternatingSixAmbientRow22LongPrefix79 *
      alternatingSixAmbientRow22LongMatrixABB).trace =
      0 := by
  change
    (∑ i : Fin 9,
      (alternatingSixAmbientRow22LongPrefix79 *
        alternatingSixAmbientRow22LongMatrixABB) i i) =
      0
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongPrefix79,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(60 : ℂ) + (60 : ℂ) * ζ ^ 4 - (60 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((-(60 : ℂ) + (60 : ℂ) * ζ ^ 4 - (60 : ℂ) * ζ ^ 8))) *
        alternatingSixComplexCyclotomicRoot_relation

/-- Trace of the positive word `ababbabbb`. -/
theorem alternatingSixAmbientRow22_positiveState77_trace :
    (alternatingSixFiveAmbient_row22_matrixA *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixA *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixA *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_row22_matrixA *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixA *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixA *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixB =
        (alternatingSixFiveAmbient_row22_matrixA *
          alternatingSixFiveAmbient_row22_matrixB) *
        ((alternatingSixFiveAmbient_row22_matrixA *
            alternatingSixFiveAmbient_row22_matrixB) *
          alternatingSixFiveAmbient_row22_matrixB) *
        (((alternatingSixFiveAmbient_row22_matrixA *
              alternatingSixFiveAmbient_row22_matrixB) *
            alternatingSixFiveAmbient_row22_matrixB) *
          alternatingSixFiveAmbient_row22_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow22_longMatrixABBB_eq,
    alternatingSixAmbientRow22_longMatrixABB_eq,
    alternatingSixAmbientRow22_longMatrixAB_eq,
    alternatingSixAmbientRow22_longPrefix77_mul]
  exact alternatingSixAmbientRow22_longState77Reduced_trace

/-- Trace of the positive word `ababbbabb`. -/
theorem alternatingSixAmbientRow22_positiveState79_trace :
    (alternatingSixFiveAmbient_row22_matrixA *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixA *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixA *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_row22_matrixA *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixA *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixA *
      alternatingSixFiveAmbient_row22_matrixB *
      alternatingSixFiveAmbient_row22_matrixB =
        (alternatingSixFiveAmbient_row22_matrixA *
          alternatingSixFiveAmbient_row22_matrixB) *
        (((alternatingSixFiveAmbient_row22_matrixA *
              alternatingSixFiveAmbient_row22_matrixB) *
            alternatingSixFiveAmbient_row22_matrixB) *
          alternatingSixFiveAmbient_row22_matrixB) *
        ((alternatingSixFiveAmbient_row22_matrixA *
            alternatingSixFiveAmbient_row22_matrixB) *
          alternatingSixFiveAmbient_row22_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow22_longMatrixABBB_eq,
    alternatingSixAmbientRow22_longMatrixABB_eq,
    alternatingSixAmbientRow22_longMatrixAB_eq,
    alternatingSixAmbientRow22_longPrefix79_mul]
  exact alternatingSixAmbientRow22_longState79Reduced_trace

end InductiveMcKay
end McKayConjecture
