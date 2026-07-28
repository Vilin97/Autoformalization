/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow23ClassMatrixCertificate

/-!
# Short matrix-word traces for ambient row 23

These exact calculations cover the two generators and the words `ab` and
`ab²` among the seven class-representative base words.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Trace of the row-23 first generator. -/
theorem alternatingSixAmbientRow23_matrixA_trace :
    alternatingSixFiveAmbient_row23_matrixA.trace = -2 := by
  change
    (∑ i : Fin 10,
      alternatingSixFiveAmbient_row23_matrixA i i) = -2
  simp [alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the row-23 second generator. -/
theorem alternatingSixAmbientRow23_matrixB_trace :
    alternatingSixFiveAmbient_row23_matrixB.trace = 0 := by
  change
    (∑ i : Fin 10,
      alternatingSixFiveAmbient_row23_matrixB i i) = 0
  simp [alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]

/-- Trace of the row-23 word `ab`. -/
theorem alternatingSixAmbientRow23_matrixAB_trace :
    (alternatingSixFiveAmbient_row23_matrixA *
          alternatingSixFiveAmbient_row23_matrixB).trace =
      0 := by
  change
    (∑ i : Fin 10,
      (alternatingSixFiveAmbient_row23_matrixA *
        alternatingSixFiveAmbient_row23_matrixB) i i) = 0
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]

/-- Trace of the row-23 word `ab²`. -/
theorem alternatingSixAmbientRow23_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row23_matrixA *
          alternatingSixFiveAmbient_row23_matrixB ^ 2).trace =
      0 := by
  change
    (∑ i : Fin 10,
      (alternatingSixFiveAmbient_row23_matrixA *
        alternatingSixFiveAmbient_row23_matrixB ^ 2) i i) = 0
  simp only [pow_two]
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]

end InductiveMcKay
end McKayConjecture
