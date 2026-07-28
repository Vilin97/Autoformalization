/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerSevenLongWordData

/-!
# One checked ATLAS degree-12 power-seven long-word multiplication

This split generated module keeps each 12 by 12 multiplication
independently compilable under the default resource limits.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (0 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (0 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (0 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (0 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (0 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (0 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (0 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (0 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (0 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (0 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (0 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (0 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (0 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (0 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (0 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (0 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (0 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (0 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (0 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (0 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (0 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (0 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (0 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (0 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (1 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (1 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (1 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (1 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (1 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (1 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (1 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (1 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (1 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (1 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (1 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (1 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (1 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (1 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (1 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (1 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (1 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (1 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (1 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (1 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (1 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (1 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (1 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (1 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (2 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (2 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (2 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (2 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (2 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (2 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (2 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (2 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (2 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (2 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (2 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (2 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (2 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (2 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (2 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (2 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (2 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (2 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (2 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (2 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (2 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (2 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (2 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (2 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (3 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (3 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (3 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (3 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (3 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (3 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (3 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (3 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (3 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (3 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (3 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (3 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (3 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (3 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (3 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (3 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (3 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (3 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (3 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (3 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (3 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (3 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (3 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (3 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (4 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (4 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - ζ ^ 8 + (2 : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - ζ ^ 8 + (2 : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (4 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (4 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 8 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 8 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (4 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (4 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (4 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (4 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 8 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 8 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (4 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (4 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (4 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (4 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) - ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) - ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (4 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (4 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (4 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (4 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (4 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (4 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (4 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (4 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (4 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (4 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (4 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (4 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (5 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (5 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (5 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (5 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((3 : ℂ) - (2 : ℂ) * ζ ^ 8 + (3 : ℂ) * ζ ^ 12 - (3 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((3 : ℂ) - (2 : ℂ) * ζ ^ 8 + (3 : ℂ) * ζ ^ 12 - (3 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (5 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (5 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(3 : ℂ) + ζ ^ 8 - (3 : ℂ) * ζ ^ 12 + (3 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(3 : ℂ) + ζ ^ 8 - (3 : ℂ) * ζ ^ 12 + (3 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (5 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (5 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (5 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (5 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (5 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (5 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(3 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(3 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (5 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (5 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((3 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((3 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (5 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (5 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (5 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (5 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (5 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (5 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (5 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (5 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (5 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (5 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (6 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (6 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (6 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (6 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (6 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (6 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (6 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (6 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (6 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (6 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (6 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (6 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (6 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (6 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (6 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (6 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (6 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (6 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (6 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (6 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (6 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (6 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (6 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (6 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (7 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (7 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 8 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 8 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (7 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (7 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (7 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (7 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 8 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 8 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (7 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (7 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((3 : ℂ) - ζ ^ 8 + (3 : ℂ) * ζ ^ 12 - (3 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((3 : ℂ) - ζ ^ 8 + (3 : ℂ) * ζ ^ 12 - (3 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (7 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (7 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (7 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (7 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) + (2 : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) + (2 : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (7 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (7 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) - ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) - ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (7 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (7 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(3 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(3 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (7 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (7 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (7 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (7 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (7 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (7 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (7 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (7 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (8 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (8 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (8 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (8 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (8 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (8 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (8 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (8 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (8 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (8 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (8 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (8 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (8 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (8 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (8 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (8 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (8 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (8 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (8 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (8 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (8 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (8 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (8 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (8 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (9 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (9 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (9 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (9 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (9 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (9 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (9 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (9 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (9 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (9 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (9 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (9 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (9 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (9 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (9 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (9 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (9 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (9 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (9 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (9 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (9 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (9 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (9 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (9 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (10 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (10 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (10 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (10 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (10 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (10 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (10 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (10 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (10 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (10 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (10 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (10 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (10 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (10 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (10 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (10 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (10 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (10 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (10 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (10 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (10 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (10 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (10 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (10 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (11 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (11 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (11 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (11 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (11 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (11 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (11 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (11 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (11 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (11 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (11 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (11 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (11 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (11 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (11 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (11 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (11 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (11 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (11 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (11 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (11 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (11 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB
        * alternatingSixFiveAmbient_atlas12Power7_matrixB)
          (11 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB
        (11 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB,
    alternatingSixFiveAmbient_atlas12Power7_matrixB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

theorem alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_mul :
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABB *
        alternatingSixFiveAmbient_atlas12Power7_matrixB =
      alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry00_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry01_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry02_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry03_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry04_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry05_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry06_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry07_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry08_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry09_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry10_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longMatrixABBB_entry11_11

end InductiveMcKay
end McKayConjecture
