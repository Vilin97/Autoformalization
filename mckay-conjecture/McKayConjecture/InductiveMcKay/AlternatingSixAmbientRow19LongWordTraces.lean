/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19LongWordProducts

/-!
# Exact traces of the two long positive row-19 words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem alternatingSixAmbientRow19_longState77Reduced_trace :
    (alternatingSixAmbientRow19LongPrefix77 *
      alternatingSixAmbientRow19LongMatrixABBB).trace =
      -1 := by
  change
    (∑ i : Fin 8,
      (alternatingSixAmbientRow19LongPrefix77 *
        alternatingSixAmbientRow19LongMatrixABBB) i i) =
      -1
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongPrefix77,
    alternatingSixAmbientRow19LongMatrixABBB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((21 / 11) : ℂ)
          - ((21 / 11) : ℂ) * ζ ^ 4
          + ((10 / 11) : ℂ) * ζ ^ 8
          - ((7 / 11) : ℂ) * ζ ^ 12
          + ((27 / 11) : ℂ) * ζ ^ 16
          + ((7 / 11) : ℂ) * ζ ^ 20
          + ((20 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((
        ((21 / 11) : ℂ)
          - ((21 / 11) : ℂ) * ζ ^ 4
          + ((10 / 11) : ℂ) * ζ ^ 8
          - ((7 / 11) : ℂ) * ζ ^ 12
          + ((27 / 11) : ℂ) * ζ ^ 16
          + ((7 / 11) : ℂ) * ζ ^ 20
          + ((20 / 11) : ℂ) * ζ ^ 24
      ))) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem alternatingSixAmbientRow19_longState79Reduced_trace :
    (alternatingSixAmbientRow19LongPrefix79 *
      alternatingSixAmbientRow19LongMatrixABB).trace =
      -1 := by
  change
    (∑ i : Fin 8,
      (alternatingSixAmbientRow19LongPrefix79 *
        alternatingSixAmbientRow19LongMatrixABB) i i) =
      -1
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongPrefix79,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((18 / 11) : ℂ)
          + ((18 / 11) : ℂ) * ζ ^ 4
          + ((46 / 11) : ℂ) * ζ ^ 8
          - ((10 / 11) : ℂ) * ζ ^ 12
          - ((31 / 11) : ℂ) * ζ ^ 16
          - ((8 / 11) : ℂ) * ζ ^ 20
          - ((41 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((
        -((18 / 11) : ℂ)
          + ((18 / 11) : ℂ) * ζ ^ 4
          + ((46 / 11) : ℂ) * ζ ^ 8
          - ((10 / 11) : ℂ) * ζ ^ 12
          - ((31 / 11) : ℂ) * ζ ^ 16
          - ((8 / 11) : ℂ) * ζ ^ 20
          - ((41 / 11) : ℂ) * ζ ^ 24
      ))) *
        alternatingSixComplexCyclotomicRoot_relation

/-- Trace of the positive word `ababbabbb`. -/
theorem alternatingSixAmbientRow19_positiveState77_trace :
    (alternatingSixFiveAmbient_row19_matrixA *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixA *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixA *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixB).trace =
      -1 := by
  rw [show
    alternatingSixFiveAmbient_row19_matrixA *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixA *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixA *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixB =
        (alternatingSixFiveAmbient_row19_matrixA *
          alternatingSixFiveAmbient_row19_matrixB) *
        ((alternatingSixFiveAmbient_row19_matrixA *
            alternatingSixFiveAmbient_row19_matrixB) *
          alternatingSixFiveAmbient_row19_matrixB) *
        (((alternatingSixFiveAmbient_row19_matrixA *
              alternatingSixFiveAmbient_row19_matrixB) *
            alternatingSixFiveAmbient_row19_matrixB) *
          alternatingSixFiveAmbient_row19_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow19_longMatrixABBB_eq,
    alternatingSixAmbientRow19_longMatrixABB_eq,
    alternatingSixAmbientRow19_longMatrixAB_eq,
    alternatingSixAmbientRow19_longPrefix77_mul]
  exact alternatingSixAmbientRow19_longState77Reduced_trace

/-- Trace of the positive word `ababbbabb`. -/
theorem alternatingSixAmbientRow19_positiveState79_trace :
    (alternatingSixFiveAmbient_row19_matrixA *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixA *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixA *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixB).trace =
      -1 := by
  rw [show
    alternatingSixFiveAmbient_row19_matrixA *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixA *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixA *
      alternatingSixFiveAmbient_row19_matrixB *
      alternatingSixFiveAmbient_row19_matrixB =
        (alternatingSixFiveAmbient_row19_matrixA *
          alternatingSixFiveAmbient_row19_matrixB) *
        (((alternatingSixFiveAmbient_row19_matrixA *
              alternatingSixFiveAmbient_row19_matrixB) *
            alternatingSixFiveAmbient_row19_matrixB) *
          alternatingSixFiveAmbient_row19_matrixB) *
        ((alternatingSixFiveAmbient_row19_matrixA *
            alternatingSixFiveAmbient_row19_matrixB) *
          alternatingSixFiveAmbient_row19_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow19_longMatrixABBB_eq,
    alternatingSixAmbientRow19_longMatrixABB_eq,
    alternatingSixAmbientRow19_longMatrixAB_eq,
    alternatingSixAmbientRow19_longPrefix79_mul]
  exact alternatingSixAmbientRow19_longState79Reduced_trace

end InductiveMcKay
end McKayConjecture
