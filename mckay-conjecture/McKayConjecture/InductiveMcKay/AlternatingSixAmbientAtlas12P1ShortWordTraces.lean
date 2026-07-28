/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P1ClassMatrixCertificate
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P1LongWordProducts

/-!
# Short matrix-word traces for ATLAS degree 12, power 1

These exact calculations cover the two generators and the words `ab` and
`ab²`. The product traces use the independently checked reduced products, so
no single proof exceeds the stock heartbeat budget.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Trace of the first ATLAS power-one generator. -/
theorem alternatingSixAmbientAtlas12P1_matrixA_trace :
    alternatingSixFiveAmbient_atlas12Power1_matrixA.trace = 0 := by
  change
    (∑ i : Fin 12,
      alternatingSixFiveAmbient_atlas12Power1_matrixA i i) = 0
  simp [alternatingSixFiveAmbient_atlas12Power1_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]

/-- Trace of the second ATLAS power-one generator. -/
theorem alternatingSixAmbientAtlas12P1_matrixB_trace :
    alternatingSixFiveAmbient_atlas12Power1_matrixB.trace = 0 := by
  change
    (∑ i : Fin 12,
      alternatingSixFiveAmbient_atlas12Power1_matrixB i i) = 0
  simp [alternatingSixFiveAmbient_atlas12Power1_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the ATLAS power-one word `ab`. -/
theorem alternatingSixAmbientAtlas12P1_matrixAB_trace :
    (alternatingSixFiveAmbient_atlas12Power1_matrixA *
      alternatingSixFiveAmbient_atlas12Power1_matrixB).trace =
      alternatingSixCyclotomicValue
        [(-1, 0), (-1, 4), (1, 8), (1, 12),
          (1, 16), (-1, 28)] := by
  rw [alternatingSixAmbientAtlas12P1_longMatrixAB_eq]
  change
    (∑ i : Fin 12,
      alternatingSixAmbientAtlas12P1LongMatrixAB i i) = _
  simp [alternatingSixAmbientAtlas12P1LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]

/-- Trace of the ATLAS power-one word `ab²`. -/
theorem alternatingSixAmbientAtlas12P1_matrixABSquared_trace :
    (alternatingSixFiveAmbient_atlas12Power1_matrixA *
      alternatingSixFiveAmbient_atlas12Power1_matrixB ^ 2).trace =
      alternatingSixCyclotomicValue
        [(-1, 0), (-1, 4), (1, 16), (1, 20)] := by
  rw [pow_two, ← Matrix.mul_assoc,
    alternatingSixAmbientAtlas12P1_longMatrixABB_eq]
  change
    (∑ i : Fin 12,
      alternatingSixAmbientAtlas12P1LongMatrixABB i i) = _
  simp [alternatingSixAmbientAtlas12P1LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

end InductiveMcKay
end McKayConjecture
