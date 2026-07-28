/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24ClassMatrixCertificate

/-!
# Short matrix-word traces for ambient row 24

These exact calculations cover the two generators and the words `ab` and
`ab²` among the seven class-representative base words.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

macro "close_row24_short_trace" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

/-- Trace of the row-24 first generator. -/
theorem alternatingSixAmbientRow24_matrixA_trace :
    alternatingSixFiveAmbient_row24_matrixA.trace = 0 := by
  change
    (∑ i : Fin 10,
      alternatingSixFiveAmbient_row24_matrixA i i) = 0
  simp [alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the row-24 second generator. -/
theorem alternatingSixAmbientRow24_matrixB_trace :
    alternatingSixFiveAmbient_row24_matrixB.trace =
      alternatingSixCyclotomicValue
        [(-1, 5), (-1, 15), (1, 25)] := by
  change
    (∑ i : Fin 10,
      alternatingSixFiveAmbient_row24_matrixB i i) = _
  simp [alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the row-24 word `ab`. -/
theorem alternatingSixAmbientRow24_matrixAB_trace :
    (alternatingSixFiveAmbient_row24_matrixA *
          alternatingSixFiveAmbient_row24_matrixB).trace =
      0 := by
  change
    (∑ i : Fin 10,
      (alternatingSixFiveAmbient_row24_matrixA *
        alternatingSixFiveAmbient_row24_matrixB) i i) = 0
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_row24_short_trace
    ((64 / 17 : ℂ) - (64 / 17 : ℂ) * ζ ^ 4 +
      (134 / 17 : ℂ) * ζ ^ 5 + (64 / 17 : ℂ) * ζ ^ 8 -
      (134 / 17 : ℂ) * ζ ^ 9 + (114 / 17 : ℂ) * ζ ^ 10 +
      (134 / 17 : ℂ) * ζ ^ 13 - (114 / 17 : ℂ) * ζ ^ 14 +
      (160 / 17 : ℂ) * ζ ^ 15 + (114 / 17 : ℂ) * ζ ^ 18 -
      (160 / 17 : ℂ) * ζ ^ 19 + (5 : ℂ) * ζ ^ 20 +
      (160 / 17 : ℂ) * ζ ^ 23 - (5 : ℂ) * ζ ^ 24 +
      (5 : ℂ) * ζ ^ 28)

/-- Trace of the row-24 word `ab²`. -/
theorem alternatingSixAmbientRow24_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row24_matrixA *
          alternatingSixFiveAmbient_row24_matrixB ^ 2).trace =
      0 := by
  change
    (∑ i : Fin 10,
      (alternatingSixFiveAmbient_row24_matrixA *
        alternatingSixFiveAmbient_row24_matrixB ^ 2) i i) = 0
  simp only [pow_two]
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_row24_short_trace
    (-(71 / 34 : ℂ) + (71 / 34 : ℂ) * ζ ^ 4 -
      (143 / 34 : ℂ) * ζ ^ 5 - (71 / 34 : ℂ) * ζ ^ 8 +
      (143 / 34 : ℂ) * ζ ^ 9 - (69 / 17 : ℂ) * ζ ^ 10 -
      (143 / 34 : ℂ) * ζ ^ 13 + (69 / 17 : ℂ) * ζ ^ 14 -
      (125 / 34 : ℂ) * ζ ^ 15 - (69 / 17 : ℂ) * ζ ^ 18 +
      (125 / 34 : ℂ) * ζ ^ 19 - (140 / 17 : ℂ) * ζ ^ 20 -
      (125 / 34 : ℂ) * ζ ^ 23 + (140 / 17 : ℂ) * ζ ^ 24 -
      (127 / 34 : ℂ) * ζ ^ 25 - (140 / 17 : ℂ) * ζ ^ 28 +
      (127 / 34 : ℂ) * ζ ^ 29 - (49 / 17 : ℂ) * ζ ^ 30 -
      (127 / 34 : ℂ) * ζ ^ 33 + (49 / 17 : ℂ) * ζ ^ 34 +
      (3 : ℂ) * ζ ^ 35 - (49 / 17 : ℂ) * ζ ^ 38 -
      (3 : ℂ) * ζ ^ 39 + (107 / 34 : ℂ) * ζ ^ 40 +
      (3 : ℂ) * ζ ^ 43 - (107 / 34 : ℂ) * ζ ^ 44 +
      (8 : ℂ) * ζ ^ 45 + (107 / 34 : ℂ) * ζ ^ 48 -
      (8 : ℂ) * ζ ^ 49 + (31 / 34 : ℂ) * ζ ^ 50 +
      (8 : ℂ) * ζ ^ 53 - (31 / 34 : ℂ) * ζ ^ 54 +
      (31 / 34 : ℂ) * ζ ^ 58)

end InductiveMcKay
end McKayConjecture
