/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import
  McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenClassMatrixCertificate
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenLongWordProducts

/-!
# Short-word traces for the ATLAS degree-12 power-seven row

These exact calculations cover the two generators and the words `ab` and
`ab²`.  The product traces use independently checked reduced products.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Trace of the first ATLAS power-seven generator. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_matrixA_trace :
    alternatingSixFiveAmbient_atlas12Power7_matrixA.trace = 0 := by
  change
    (∑ i : Fin 12,
      alternatingSixFiveAmbient_atlas12Power7_matrixA i i) = 0
  simp [alternatingSixFiveAmbient_atlas12Power7_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]

/-- Trace of the second ATLAS power-seven generator. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_matrixB_trace :
    alternatingSixFiveAmbient_atlas12Power7_matrixB.trace = 0 := by
  change
    (∑ i : Fin 12,
      alternatingSixFiveAmbient_atlas12Power7_matrixB i i) = 0
  simp [alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the ATLAS power-seven word `ab`. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_matrixAB_trace :
    (alternatingSixFiveAmbient_atlas12Power7_matrixA *
      alternatingSixFiveAmbient_atlas12Power7_matrixB).trace =
      alternatingSixCyclotomicValue
        [(1, 0), (1, 4), (-1, 8), (-1, 12), (-1, 16),
          (-1, 20), (1, 28)] := by
  rw [alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixAB_eq]
  change
    (∑ i : Fin 12,
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB i i) = _
  simp [alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]

/-- Trace of the ATLAS power-seven word `ab²`. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_matrixABSquared_trace :
    (alternatingSixFiveAmbient_atlas12Power7_matrixA *
      alternatingSixFiveAmbient_atlas12Power7_matrixB ^ 2).trace =
      alternatingSixCyclotomicValue [(1, 4), (-1, 16)] := by
  rw [pow_two, ← Matrix.mul_assoc,
    alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABB_eq]
  change
    (∑ i : Fin 12,
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB i i) = _
  simp [alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

end InductiveMcKay
end McKayConjecture
