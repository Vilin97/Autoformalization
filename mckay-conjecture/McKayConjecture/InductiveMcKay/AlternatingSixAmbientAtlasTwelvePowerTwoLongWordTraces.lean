/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoLongWordProducts

/-!
# Exact traces of the ATLAS power-2 long words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77Reduced_trace :
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77.trace =
      0 := by
  change
    (∑ i : Fin 12, alternatingSixAmbientAtlasTwelvePowerTwoLongState77 i i) =
      0
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  all_goals ring

theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState79Reduced_trace :
    alternatingSixAmbientAtlasTwelvePowerTwoLongState79.trace =
      0 := by
  change
    (∑ i : Fin 12, alternatingSixAmbientAtlasTwelvePowerTwoLongState79 i i) =
      0
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongState79,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  all_goals ring

/-- Trace of the positive word `ababbabbb`. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_positiveState77_trace :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixA *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixA *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_atlas12Power2_matrixA *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixA *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixA *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixB =
        (alternatingSixFiveAmbient_atlas12Power2_matrixA *
          alternatingSixFiveAmbient_atlas12Power2_matrixB) *
        ((alternatingSixFiveAmbient_atlas12Power2_matrixA *
            alternatingSixFiveAmbient_atlas12Power2_matrixB) *
          alternatingSixFiveAmbient_atlas12Power2_matrixB) *
        (((alternatingSixFiveAmbient_atlas12Power2_matrixA *
              alternatingSixFiveAmbient_atlas12Power2_matrixB) *
            alternatingSixFiveAmbient_atlas12Power2_matrixB) *
          alternatingSixFiveAmbient_atlas12Power2_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixABBB_eq,
    alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixABB_eq,
    alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_eq,
    alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix77_mul,
    alternatingSixAmbientAtlasTwelvePowerTwo_longState77_mul]
  exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77Reduced_trace

/-- Trace of the positive word `ababbbabb`. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_positiveState79_trace :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixA *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixA *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_atlas12Power2_matrixA *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixA *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixA *
      alternatingSixFiveAmbient_atlas12Power2_matrixB *
      alternatingSixFiveAmbient_atlas12Power2_matrixB =
        (alternatingSixFiveAmbient_atlas12Power2_matrixA *
          alternatingSixFiveAmbient_atlas12Power2_matrixB) *
        (((alternatingSixFiveAmbient_atlas12Power2_matrixA *
              alternatingSixFiveAmbient_atlas12Power2_matrixB) *
            alternatingSixFiveAmbient_atlas12Power2_matrixB) *
          alternatingSixFiveAmbient_atlas12Power2_matrixB) *
        ((alternatingSixFiveAmbient_atlas12Power2_matrixA *
            alternatingSixFiveAmbient_atlas12Power2_matrixB) *
          alternatingSixFiveAmbient_atlas12Power2_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixABBB_eq,
    alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixABB_eq,
    alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_eq,
    alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_mul,
    alternatingSixAmbientAtlasTwelvePowerTwo_longState79_mul]
  exact alternatingSixAmbientAtlasTwelvePowerTwo_longState79Reduced_trace

end InductiveMcKay
end McKayConjecture
