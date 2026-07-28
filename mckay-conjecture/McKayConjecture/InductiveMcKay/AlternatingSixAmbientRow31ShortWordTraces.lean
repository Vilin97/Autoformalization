/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow31ClassMatrixCertificate

/-!
# Short matrix-word traces for ambient row 31

These exact calculations cover the two generators and the words `ab` and
`ab²` among the seven class-representative base words.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

macro "close_row31_short_trace" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

/-- Trace of the row-31 first generator. -/
theorem alternatingSixAmbientRow31_matrixA_trace :
    alternatingSixFiveAmbient_row31_matrixA.trace =
      alternatingSixCyclotomicValue [(1, 20)] := by
  change
    (∑ i : Fin 15,
      alternatingSixFiveAmbient_row31_matrixA i i) = _
  simp [alternatingSixFiveAmbient_row31_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]

/-- Trace of the row-31 second generator. -/
theorem alternatingSixAmbientRow31_matrixB_trace :
    alternatingSixFiveAmbient_row31_matrixB.trace = -1 := by
  change
    (∑ i : Fin 15,
      alternatingSixFiveAmbient_row31_matrixB i i) = -1
  simp [alternatingSixFiveAmbient_row31_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]

/-- Trace of the row-31 word `ab`. -/
theorem alternatingSixAmbientRow31_matrixAB_trace :
    (alternatingSixFiveAmbient_row31_matrixA *
          alternatingSixFiveAmbient_row31_matrixB).trace =
      0 := by
  change
    (∑ i : Fin 15,
      (alternatingSixFiveAmbient_row31_matrixA *
        alternatingSixFiveAmbient_row31_matrixB) i i) = 0
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row31_matrixA,
    alternatingSixFiveAmbient_row31_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_row31_short_trace
    ((1 : ℂ) - ζ ^ 4 + ζ ^ 8)

/-- Trace of the row-31 word `ab²`. -/
theorem alternatingSixAmbientRow31_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row31_matrixA *
          alternatingSixFiveAmbient_row31_matrixB ^ 2).trace =
      0 := by
  change
    (∑ i : Fin 15,
      (alternatingSixFiveAmbient_row31_matrixA *
        alternatingSixFiveAmbient_row31_matrixB ^ 2) i i) = 0
  simp only [pow_two]
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row31_matrixA,
    alternatingSixFiveAmbient_row31_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_row31_short_trace
    ((3 : ℂ) - (3 : ℂ) * ζ ^ 4 + (3 : ℂ) * ζ ^ 8 -
      (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24 -
      (2 : ℂ) * ζ ^ 28)

end InductiveMcKay
end McKayConjecture
