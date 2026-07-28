/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow30ClassMatrixCertificate

/-!
# Short matrix-word traces for ambient row 30

These exact calculations cover the two generators and the words `ab` and
`ab²` among the seven class-representative base words.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

macro "close_row30_short_trace" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

/-- Trace of the row-30 first generator. -/
theorem alternatingSixAmbientRow30_matrixA_trace :
    alternatingSixFiveAmbient_row30_matrixA.trace =
      alternatingSixCyclotomicValue [(1, 0), (-1, 20)] := by
  change
    (∑ i : Fin 15,
      alternatingSixFiveAmbient_row30_matrixA i i) = _
  simp [alternatingSixFiveAmbient_row30_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the row-30 second generator. -/
theorem alternatingSixAmbientRow30_matrixB_trace :
    alternatingSixFiveAmbient_row30_matrixB.trace = -1 := by
  change
    (∑ i : Fin 15,
      alternatingSixFiveAmbient_row30_matrixB i i) = -1
  simp [alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]

/-- Trace of the row-30 word `ab`. -/
theorem alternatingSixAmbientRow30_matrixAB_trace :
    (alternatingSixFiveAmbient_row30_matrixA *
          alternatingSixFiveAmbient_row30_matrixB).trace =
      0 := by
  change
    (∑ i : Fin 15,
      (alternatingSixFiveAmbient_row30_matrixA *
        alternatingSixFiveAmbient_row30_matrixB) i i) = 0
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row30_matrixA,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_row30_short_trace
    (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)

/-- Trace of the row-30 word `ab²`. -/
theorem alternatingSixAmbientRow30_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row30_matrixA *
          alternatingSixFiveAmbient_row30_matrixB ^ 2).trace =
      0 := by
  change
    (∑ i : Fin 15,
      (alternatingSixFiveAmbient_row30_matrixA *
        alternatingSixFiveAmbient_row30_matrixB ^ 2) i i) = 0
  simp only [pow_two]
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row30_matrixA,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_row30_short_trace
    (ζ ^ 20 - ζ ^ 24 + ζ ^ 28)

end InductiveMcKay
end McKayConjecture
