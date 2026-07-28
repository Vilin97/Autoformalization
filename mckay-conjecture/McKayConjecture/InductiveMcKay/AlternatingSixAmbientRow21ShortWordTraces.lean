/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow21ClassMatrixCertificate

/-!
# Short matrix-word traces for ambient row 21

These exact calculations cover the two generators and the words `ab` and
`ab²` among the seven class-representative base words.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

macro "close_row21_short_trace" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

/-- Trace of the row-21 first generator. -/
theorem alternatingSixAmbientRow21_matrixA_trace :
    alternatingSixFiveAmbient_row21_matrixA.trace =
      alternatingSixCyclotomicValue [(-1, 0), (1, 20)] := by
  change
    (∑ i : Fin 9,
      alternatingSixFiveAmbient_row21_matrixA i i) = _
  simp [alternatingSixFiveAmbient_row21_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the row-21 second generator. -/
theorem alternatingSixAmbientRow21_matrixB_trace :
    alternatingSixFiveAmbient_row21_matrixB.trace = 1 := by
  change
    (∑ i : Fin 9,
      alternatingSixFiveAmbient_row21_matrixB i i) = 1
  simp [alternatingSixFiveAmbient_row21_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the row-21 word `ab`. -/
theorem alternatingSixAmbientRow21_matrixAB_trace :
    (alternatingSixFiveAmbient_row21_matrixA *
          alternatingSixFiveAmbient_row21_matrixB).trace =
      alternatingSixCyclotomicValue [(1, 20)] := by
  change
    (∑ i : Fin 9,
      (alternatingSixFiveAmbient_row21_matrixA *
        alternatingSixFiveAmbient_row21_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row21_matrixA,
    alternatingSixFiveAmbient_row21_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_row21_short_trace
    (-((19 / 3) : ℂ) + ((19 / 3) : ℂ) * ζ ^ 4 -
      ((19 / 3) : ℂ) * ζ ^ 8)

/-- Trace of the row-21 word `ab²`. -/
theorem alternatingSixAmbientRow21_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row21_matrixA *
          alternatingSixFiveAmbient_row21_matrixB ^ 2).trace =
      alternatingSixCyclotomicValue [(1, 0), (-1, 20)] := by
  change
    (∑ i : Fin 9,
      (alternatingSixFiveAmbient_row21_matrixA *
        alternatingSixFiveAmbient_row21_matrixB ^ 2) i i) = _
  simp only [pow_two]
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row21_matrixA,
    alternatingSixFiveAmbient_row21_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_row21_short_trace
    (-((13 / 36) : ℂ) + ((13 / 36) : ℂ) * ζ ^ 4 -
      ((13 / 36) : ℂ) * ζ ^ 8 +
      ((31 / 18) : ℂ) * ζ ^ 20 -
      ((31 / 18) : ℂ) * ζ ^ 24 +
      ((31 / 18) : ℂ) * ζ ^ 28)

end InductiveMcKay
end McKayConjecture
