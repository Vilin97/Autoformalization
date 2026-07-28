/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19ClassMatrixCertificate

/-!
# Short matrix-word traces for ambient row 19

These four independent calculations cover five of the seven noncentral words
used by the checked class representatives: the identity needs no certificate,
the two generators have trace zero, and `ab` and `ab²` have the displayed
cyclotomic traces.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

macro "close_row19_short_trace" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

/-- Trace of the row-19 first generator. -/
theorem alternatingSixAmbientRow19_matrixA_trace :
    alternatingSixFiveAmbient_row19_matrixA.trace = 0 := by
  change
    (∑ i : Fin 8,
      alternatingSixFiveAmbient_row19_matrixA i i) = 0
  simp [alternatingSixFiveAmbient_row19_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the row-19 second generator. -/
theorem alternatingSixAmbientRow19_matrixB_trace :
    alternatingSixFiveAmbient_row19_matrixB.trace = 0 := by
  change
    (∑ i : Fin 8,
      alternatingSixFiveAmbient_row19_matrixB i i) = 0
  simp [alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the row-19 word `ab`. -/
theorem alternatingSixAmbientRow19_matrixAB_trace :
    (alternatingSixFiveAmbient_row19_matrixA *
          alternatingSixFiveAmbient_row19_matrixB).trace =
      alternatingSixCyclotomicValue
        [(-1, 8), (-1, 12), (1, 28)] := by
  change
    (∑ i : Fin 8,
      (alternatingSixFiveAmbient_row19_matrixA *
        alternatingSixFiveAmbient_row19_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row19_matrixA,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_row19_short_trace
    (-(13 / 11 : ℂ) + (13 / 11 : ℂ) * ζ ^ 4 -
      (7 / 11 : ℂ) * ζ ^ 8 + (42 / 11 : ℂ) * ζ ^ 12 -
      (31 / 11 : ℂ) * ζ ^ 16 + (15 / 11 : ℂ) * ζ ^ 20 +
      ζ ^ 24)

/-- Trace of the row-19 word `ab²`. -/
theorem alternatingSixAmbientRow19_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row19_matrixA *
          alternatingSixFiveAmbient_row19_matrixB ^ 2).trace =
      alternatingSixCyclotomicValue
        [(-1, 0), (1, 8), (1, 12), (-1, 28)] := by
  change
    (∑ i : Fin 8,
      (alternatingSixFiveAmbient_row19_matrixA *
        alternatingSixFiveAmbient_row19_matrixB ^ 2) i i) = _
  simp only [pow_two]
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row19_matrixA,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_row19_short_trace
    (-(108 / 11 : ℂ) + (108 / 11 : ℂ) * ζ ^ 4 +
      (215 / 11 : ℂ) * ζ ^ 8 - (109 / 11 : ℂ) * ζ ^ 12 -
      (269 / 11 : ℂ) * ζ ^ 16 - (49 / 11 : ℂ) * ζ ^ 20 -
      (70 / 11 : ℂ) * ζ ^ 24 - (23 / 11 : ℂ) * ζ ^ 28 +
      (382 / 11 : ℂ) * ζ ^ 32 + (188 / 11 : ℂ) * ζ ^ 36 -
      (83 / 11 : ℂ) * ζ ^ 40 - (153 / 11 : ℂ) * ζ ^ 44 -
      (16 / 11 : ℂ) * ζ ^ 48 - (164 / 11 : ℂ) * ζ ^ 52)

end InductiveMcKay
end McKayConjecture
