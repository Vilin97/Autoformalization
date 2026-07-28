/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow20ClassMatrixCertificate
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow20LongWordProducts

/-!
# Short matrix-word traces for ambient row 20

The first two calculations evaluate the generator traces directly. The
remaining two reuse the reduced `ab` and `ab²` products that also feed the
long-word certificates.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Trace of the row-20 first generator. -/
theorem alternatingSixAmbientRow20_matrixA_trace :
    alternatingSixFiveAmbient_row20_matrixA.trace = 1 := by
  change
    (∑ i : Fin 9,
      alternatingSixFiveAmbient_row20_matrixA i i) = 1
  simp [alternatingSixFiveAmbient_row20_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]

/-- Trace of the row-20 second generator. -/
theorem alternatingSixAmbientRow20_matrixB_trace :
    alternatingSixFiveAmbient_row20_matrixB.trace = 1 := by
  change
    (∑ i : Fin 9,
      alternatingSixFiveAmbient_row20_matrixB i i) = 1
  simp [alternatingSixFiveAmbient_row20_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the row-20 word `ab`. -/
theorem alternatingSixAmbientRow20_matrixAB_trace :
    (alternatingSixFiveAmbient_row20_matrixA *
          alternatingSixFiveAmbient_row20_matrixB).trace =
      -1 := by
  rw [alternatingSixAmbientRow20_longMatrixAB_eq]
  change
    (∑ i : Fin 9,
      alternatingSixAmbientRow20LongMatrixAB i i) = -1
  simp [alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the row-20 word `ab²`. -/
theorem alternatingSixAmbientRow20_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row20_matrixA *
          alternatingSixFiveAmbient_row20_matrixB ^ 2).trace =
      -1 := by
  rw [pow_two, ← Matrix.mul_assoc,
    alternatingSixAmbientRow20_longMatrixABB_eq]
  change
    (∑ i : Fin 9,
      alternatingSixAmbientRow20LongMatrixABB i i) = -1
  simp [alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

end InductiveMcKay
end McKayConjecture
