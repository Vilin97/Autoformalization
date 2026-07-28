/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow22ClassMatrixCertificate

/-!
# Short matrix-word traces for ambient row 22

These exact calculations cover the two generators and the words `ab` and
`ab²` among the seven class-representative base words.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

macro "close_row22_short_trace" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

/-- Trace of the row-22 first generator. -/
theorem alternatingSixAmbientRow22_matrixA_trace :
    alternatingSixFiveAmbient_row22_matrixA.trace =
      alternatingSixCyclotomicValue [(-1, 20)] := by
  change
    (∑ i : Fin 9,
      alternatingSixFiveAmbient_row22_matrixA i i) = _
  simp [alternatingSixFiveAmbient_row22_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the row-22 second generator. -/
theorem alternatingSixAmbientRow22_matrixB_trace :
    alternatingSixFiveAmbient_row22_matrixB.trace = 1 := by
  change
    (∑ i : Fin 9,
      alternatingSixFiveAmbient_row22_matrixB i i) = 1
  simp [alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the row-22 word `ab`. -/
theorem alternatingSixAmbientRow22_matrixAB_trace :
    (alternatingSixFiveAmbient_row22_matrixA *
          alternatingSixFiveAmbient_row22_matrixB).trace =
      alternatingSixCyclotomicValue [(1, 0), (-1, 20)] := by
  change
    (∑ i : Fin 9,
      (alternatingSixFiveAmbient_row22_matrixA *
        alternatingSixFiveAmbient_row22_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row22_matrixA,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_row22_short_trace
    ((6 : ℂ) - 6 * ζ ^ 4 + 6 * ζ ^ 8)

/-- Trace of the row-22 word `ab²`. -/
theorem alternatingSixAmbientRow22_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row22_matrixA *
          alternatingSixFiveAmbient_row22_matrixB ^ 2).trace =
      alternatingSixCyclotomicValue [(1, 20)] := by
  change
    (∑ i : Fin 9,
      (alternatingSixFiveAmbient_row22_matrixA *
        alternatingSixFiveAmbient_row22_matrixB ^ 2) i i) = _
  simp only [pow_two]
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row22_matrixA,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_row22_short_trace
    (-(30 : ℂ) + 30 * ζ ^ 4 - 30 * ζ ^ 8 +
      6 * ζ ^ 20 - 6 * ζ ^ 24 + 6 * ζ ^ 28)

end InductiveMcKay
end McKayConjecture
