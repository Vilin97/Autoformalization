/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25ClassMatrixCertificate
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25LongWordProducts

/-!
# Short matrix-word traces for ambient row 25

These exact calculations cover the two generators and the words `ab` and
`ab²` among the seven class-representative base words. The already checked
reduced products keep the two product traces independent of a second
large-entry multiplication proof.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Trace of the row-25 first generator. -/
theorem alternatingSixAmbientRow25_matrixA_trace :
    alternatingSixFiveAmbient_row25_matrixA.trace = 0 := by
  change
    (∑ i : Fin 10,
      alternatingSixFiveAmbient_row25_matrixA i i) = 0
  simp [alternatingSixFiveAmbient_row25_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the row-25 second generator. -/
theorem alternatingSixAmbientRow25_matrixB_trace :
    alternatingSixFiveAmbient_row25_matrixB.trace =
      alternatingSixCyclotomicValue [(1, 5), (1, 15), (-1, 25)] := by
  change
    (∑ i : Fin 10,
      alternatingSixFiveAmbient_row25_matrixB i i) = _
  simp [alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the row-25 word `ab`. -/
theorem alternatingSixAmbientRow25_matrixAB_trace :
    (alternatingSixFiveAmbient_row25_matrixA *
      alternatingSixFiveAmbient_row25_matrixB).trace = 0 := by
  rw [alternatingSixAmbientRow25_longMatrixAB_eq]
  change
    (∑ i : Fin 10,
      alternatingSixAmbientRow25LongMatrixAB i i) = 0
  simp [alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the row-25 word `ab²`. -/
theorem alternatingSixAmbientRow25_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row25_matrixA *
      alternatingSixFiveAmbient_row25_matrixB ^ 2).trace = 0 := by
  rw [pow_two, ← Matrix.mul_assoc,
    alternatingSixAmbientRow25_longMatrixABB_eq]
  change
    (∑ i : Fin 10,
      alternatingSixAmbientRow25LongMatrixABB i i) = 0
  simp [alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

end InductiveMcKay
end McKayConjecture
