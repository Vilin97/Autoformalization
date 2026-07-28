/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenLongWordProducts

/-!
# Exact traces of the two long positive ATLAS degree-12 power-seven words
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem alternatingSixAmbientAtlasTwelvePowerSeven_longState77Reduced_trace :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix77 *
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB).trace =
      0 := by
  change
    (∑ i : Fin 12,
      (alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix77 *
        alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB) i i) =
      0
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(14 : ℂ)
          - (4 : ℂ) * ζ ^ 4
          - (6 : ℂ) * ζ ^ 8
          - (8 : ℂ) * ζ ^ 12
          + (8 : ℂ) * ζ ^ 16
          + (4 : ℂ) * ζ ^ 20
          - (4 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((
        -(14 : ℂ)
          - (4 : ℂ) * ζ ^ 4
          - (6 : ℂ) * ζ ^ 8
          - (8 : ℂ) * ζ ^ 12
          + (8 : ℂ) * ζ ^ 16
          + (4 : ℂ) * ζ ^ 20
          - (4 : ℂ) * ζ ^ 24
      ))) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem alternatingSixAmbientAtlasTwelvePowerSeven_longState79Reduced_trace :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79 *
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB).trace =
      0 := by
  change
    (∑ i : Fin 12,
      (alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79 *
        alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB) i i) =
      0
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixCyclotomicValue,
    Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(21 : ℂ)
          - (9 : ℂ) * ζ ^ 4
          + (9 : ℂ) * ζ ^ 8
          - (4 : ℂ) * ζ ^ 12
          + (5 : ℂ) * ζ ^ 16
          + (12 : ℂ) * ζ ^ 20
          - (12 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((
        -(21 : ℂ)
          - (9 : ℂ) * ζ ^ 4
          + (9 : ℂ) * ζ ^ 8
          - (4 : ℂ) * ζ ^ 12
          + (5 : ℂ) * ζ ^ 16
          + (12 : ℂ) * ζ ^ 20
          - (12 : ℂ) * ζ ^ 24
      ))) *
        alternatingSixComplexCyclotomicRoot_relation

/-- Trace of the positive word `ababbabbb`. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_positiveState77_trace :
    (alternatingSixFiveAmbient_atlas12Power7_matrixA *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixA *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixA *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_atlas12Power7_matrixA *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixA *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixA *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixB =
        (alternatingSixFiveAmbient_atlas12Power7_matrixA *
          alternatingSixFiveAmbient_atlas12Power7_matrixB) *
        ((alternatingSixFiveAmbient_atlas12Power7_matrixA *
            alternatingSixFiveAmbient_atlas12Power7_matrixB) *
          alternatingSixFiveAmbient_atlas12Power7_matrixB) *
        (((alternatingSixFiveAmbient_atlas12Power7_matrixA *
              alternatingSixFiveAmbient_atlas12Power7_matrixB) *
            alternatingSixFiveAmbient_atlas12Power7_matrixB) *
          alternatingSixFiveAmbient_atlas12Power7_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_eq,
    alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABB_eq,
    alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixAB_eq,
    alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix77_mul]
  exact alternatingSixAmbientAtlasTwelvePowerSeven_longState77Reduced_trace

/-- Trace of the positive word `ababbbabb`. -/
theorem alternatingSixAmbientAtlasTwelvePowerSeven_positiveState79_trace :
    (alternatingSixFiveAmbient_atlas12Power7_matrixA *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixA *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixA *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixB).trace =
      0 := by
  rw [show
    alternatingSixFiveAmbient_atlas12Power7_matrixA *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixA *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixA *
      alternatingSixFiveAmbient_atlas12Power7_matrixB *
      alternatingSixFiveAmbient_atlas12Power7_matrixB =
        (alternatingSixFiveAmbient_atlas12Power7_matrixA *
          alternatingSixFiveAmbient_atlas12Power7_matrixB) *
        (((alternatingSixFiveAmbient_atlas12Power7_matrixA *
              alternatingSixFiveAmbient_atlas12Power7_matrixB) *
            alternatingSixFiveAmbient_atlas12Power7_matrixB) *
          alternatingSixFiveAmbient_atlas12Power7_matrixB) *
        ((alternatingSixFiveAmbient_atlas12Power7_matrixA *
            alternatingSixFiveAmbient_atlas12Power7_matrixB) *
          alternatingSixFiveAmbient_atlas12Power7_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_eq,
    alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABB_eq,
    alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixAB_eq,
    alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_mul]
  exact alternatingSixAmbientAtlasTwelvePowerSeven_longState79Reduced_trace

end InductiveMcKay
end McKayConjecture
