/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoLongWordData

/-!
# One checked ATLAS power-2 long-word multiplication

This split module is independently compilable under the default limits.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_00 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (0 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (0 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_01 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (0 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (0 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_02 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (0 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (0 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_03 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (0 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (0 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_04 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (0 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (0 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_05 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (0 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (0 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_06 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (0 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (0 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_07 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (0 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (0 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_08 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (0 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (0 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_09 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (0 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (0 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_10 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (0 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (0 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_11 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (0 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (0 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_00 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (1 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (1 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_01 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (1 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (1 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_02 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (1 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (1 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_03 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (1 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (1 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_04 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (1 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (1 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_05 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (1 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (1 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_06 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (1 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (1 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_07 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (1 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (1 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_08 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (1 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (1 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_09 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (1 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (1 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_10 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (1 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (1 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_11 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (1 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (1 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_00 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (2 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (2 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_01 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (2 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (2 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_02 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (2 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (2 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_03 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (2 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (2 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_04 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (2 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (2 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_05 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (2 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (2 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_06 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (2 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (2 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_07 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (2 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (2 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_08 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (2 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (2 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_09 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (2 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (2 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_10 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (2 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (2 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_11 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (2 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (2 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_00 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (3 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (3 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_01 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (3 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (3 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_02 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (3 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (3 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_03 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (3 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (3 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_04 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (3 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (3 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_05 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (3 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (3 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_06 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (3 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (3 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_07 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (3 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (3 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_08 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (3 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (3 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_09 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (3 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (3 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_10 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (3 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (3 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_11 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (3 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (3 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_00 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (4 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (4 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_01 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (4 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (4 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_02 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (4 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (4 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_03 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (4 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (4 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_04 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (4 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (4 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_05 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (4 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (4 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_06 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (4 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (4 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_07 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (4 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (4 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_08 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (4 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (4 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_09 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (4 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (4 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_10 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (4 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (4 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_11 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (4 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (4 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_00 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (5 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (5 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_01 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (5 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (5 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_02 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (5 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (5 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_03 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (5 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (5 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_04 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (5 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (5 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_05 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (5 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (5 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_06 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (5 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (5 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_07 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (5 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (5 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_08 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (5 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (5 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_09 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (5 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (5 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_10 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (5 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (5 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_11 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (5 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (5 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_00 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (6 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (6 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_01 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (6 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (6 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_02 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (6 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (6 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_03 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (6 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (6 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_04 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (6 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (6 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_05 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (6 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (6 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_06 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (6 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (6 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_07 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (6 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (6 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_08 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (6 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (6 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_09 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (6 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (6 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_10 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (6 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (6 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_11 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (6 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (6 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_00 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (7 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (7 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_01 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (7 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (7 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_02 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (7 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (7 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_03 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (7 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (7 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_04 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (7 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (7 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_05 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (7 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (7 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_06 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (7 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (7 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_07 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (7 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (7 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_08 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (7 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (7 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_09 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (7 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (7 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_10 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (7 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (7 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_11 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (7 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (7 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_00 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (8 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (8 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_01 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (8 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (8 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_02 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (8 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (8 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_03 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (8 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (8 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_04 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (8 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (8 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_05 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (8 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (8 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_06 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (8 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (8 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_07 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (8 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (8 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_08 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (8 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (8 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_09 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (8 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (8 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_10 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (8 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (8 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_11 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (8 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (8 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_00 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (9 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (9 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_01 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (9 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (9 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_02 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (9 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (9 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_03 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (9 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (9 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_04 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (9 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (9 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_05 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (9 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (9 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_06 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (9 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (9 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_07 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (9 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (9 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_08 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (9 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (9 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_09 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (9 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (9 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_10 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (9 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (9 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_11 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (9 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (9 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_00 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (10 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (10 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_01 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (10 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (10 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_02 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (10 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (10 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_03 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (10 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (10 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_04 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (10 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (10 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_05 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (10 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (10 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_06 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (10 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (10 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_07 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (10 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (10 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_08 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (10 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (10 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_09 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (10 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (10 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_10 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (10 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (10 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_11 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (10 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (10 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_00 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (11 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (11 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_01 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (11 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (11 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_02 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (11 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (11 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_03 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (11 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (11 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_04 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (11 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (11 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_05 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (11 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (11 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_06 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (11 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (11 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_07 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (11 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (11 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_08 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (11 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (11 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_09 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (11 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (11 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_10 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (11 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (11 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_11 :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA
        * alternatingSixFiveAmbient_atlas12Power2_matrixB)
          (11 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        (11 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

theorem alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_mul :
    alternatingSixFiveAmbient_atlas12Power2_matrixA *
        alternatingSixFiveAmbient_atlas12Power2_matrixB =
      alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry00_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry01_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry02_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry03_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry04_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry05_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry06_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry07_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry08_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry09_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry10_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longMatrixAB_entry11_11

end InductiveMcKay
end McKayConjecture
