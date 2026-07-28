/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow23LongWordData

/-!
# One checked row-23 long-word multiplication

This split generated module keeps each 10 by 10 multiplication
independently compilable under the default resource limits.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry00_00 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (0 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (0 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry00_01 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (0 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (0 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry00_02 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (0 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (0 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry00_03 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (0 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (0 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry00_04 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (0 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (0 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry00_05 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (0 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (0 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry00_06 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (0 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (0 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry00_07 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (0 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (0 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry00_08 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (0 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (0 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry00_09 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (0 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (0 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry01_00 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (1 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (1 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry01_01 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (1 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (1 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry01_02 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (1 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (1 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry01_03 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (1 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (1 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry01_04 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (1 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (1 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry01_05 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (1 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (1 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry01_06 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (1 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (1 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry01_07 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (1 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (1 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry01_08 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (1 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (1 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry01_09 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (1 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (1 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry02_00 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (2 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (2 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry02_01 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (2 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (2 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry02_02 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (2 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (2 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry02_03 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (2 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (2 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry02_04 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (2 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (2 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry02_05 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (2 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (2 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry02_06 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (2 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (2 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry02_07 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (2 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (2 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry02_08 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (2 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (2 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry02_09 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (2 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (2 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry03_00 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (3 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (3 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry03_01 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (3 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (3 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry03_02 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (3 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (3 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry03_03 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (3 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (3 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry03_04 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (3 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (3 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry03_05 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (3 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (3 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry03_06 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (3 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (3 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry03_07 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (3 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (3 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry03_08 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (3 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (3 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry03_09 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (3 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (3 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry04_00 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (4 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (4 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry04_01 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (4 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (4 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry04_02 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (4 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (4 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry04_03 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (4 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (4 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry04_04 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (4 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (4 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry04_05 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (4 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (4 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry04_06 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (4 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (4 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry04_07 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (4 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (4 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry04_08 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (4 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (4 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry04_09 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (4 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (4 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry05_00 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (5 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (5 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry05_01 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (5 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (5 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry05_02 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (5 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (5 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry05_03 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (5 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (5 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry05_04 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (5 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (5 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry05_05 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (5 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (5 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry05_06 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (5 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (5 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry05_07 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (5 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (5 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry05_08 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (5 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (5 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry05_09 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (5 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (5 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry06_00 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (6 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (6 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry06_01 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (6 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (6 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry06_02 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (6 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (6 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry06_03 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (6 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (6 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry06_04 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (6 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (6 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry06_05 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (6 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (6 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry06_06 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (6 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (6 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry06_07 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (6 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (6 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry06_08 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (6 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (6 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry06_09 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (6 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (6 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry07_00 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (7 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (7 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry07_01 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (7 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (7 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry07_02 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (7 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (7 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry07_03 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (7 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (7 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry07_04 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (7 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (7 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry07_05 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (7 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (7 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry07_06 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (7 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (7 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry07_07 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (7 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (7 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry07_08 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (7 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (7 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry07_09 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (7 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (7 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry08_00 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (8 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (8 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry08_01 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (8 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (8 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry08_02 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (8 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (8 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry08_03 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (8 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (8 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry08_04 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (8 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (8 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry08_05 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (8 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (8 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry08_06 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (8 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (8 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry08_07 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (8 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (8 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry08_08 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (8 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (8 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry08_09 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (8 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (8 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry09_00 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (9 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (9 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry09_01 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (9 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (9 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry09_02 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (9 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (9 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry09_03 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (9 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (9 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry09_04 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (9 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (9 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry09_05 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (9 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (9 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry09_06 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (9 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (9 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry09_07 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (9 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (9 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry09_08 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (9 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (9 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longMatrixAB_entry09_09 :
    (alternatingSixFiveAmbient_row23_matrixA
        * alternatingSixFiveAmbient_row23_matrixB)
          (9 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongMatrixAB
        (9 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row23_matrixA,
    alternatingSixFiveAmbient_row23_matrixB,
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

theorem alternatingSixAmbientRow23_longMatrixAB_mul :
    alternatingSixFiveAmbient_row23_matrixA *
        alternatingSixFiveAmbient_row23_matrixB =
      alternatingSixAmbientRow23LongMatrixAB := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientRow23_longMatrixAB_entry00_00
  · exact alternatingSixAmbientRow23_longMatrixAB_entry00_01
  · exact alternatingSixAmbientRow23_longMatrixAB_entry00_02
  · exact alternatingSixAmbientRow23_longMatrixAB_entry00_03
  · exact alternatingSixAmbientRow23_longMatrixAB_entry00_04
  · exact alternatingSixAmbientRow23_longMatrixAB_entry00_05
  · exact alternatingSixAmbientRow23_longMatrixAB_entry00_06
  · exact alternatingSixAmbientRow23_longMatrixAB_entry00_07
  · exact alternatingSixAmbientRow23_longMatrixAB_entry00_08
  · exact alternatingSixAmbientRow23_longMatrixAB_entry00_09
  · exact alternatingSixAmbientRow23_longMatrixAB_entry01_00
  · exact alternatingSixAmbientRow23_longMatrixAB_entry01_01
  · exact alternatingSixAmbientRow23_longMatrixAB_entry01_02
  · exact alternatingSixAmbientRow23_longMatrixAB_entry01_03
  · exact alternatingSixAmbientRow23_longMatrixAB_entry01_04
  · exact alternatingSixAmbientRow23_longMatrixAB_entry01_05
  · exact alternatingSixAmbientRow23_longMatrixAB_entry01_06
  · exact alternatingSixAmbientRow23_longMatrixAB_entry01_07
  · exact alternatingSixAmbientRow23_longMatrixAB_entry01_08
  · exact alternatingSixAmbientRow23_longMatrixAB_entry01_09
  · exact alternatingSixAmbientRow23_longMatrixAB_entry02_00
  · exact alternatingSixAmbientRow23_longMatrixAB_entry02_01
  · exact alternatingSixAmbientRow23_longMatrixAB_entry02_02
  · exact alternatingSixAmbientRow23_longMatrixAB_entry02_03
  · exact alternatingSixAmbientRow23_longMatrixAB_entry02_04
  · exact alternatingSixAmbientRow23_longMatrixAB_entry02_05
  · exact alternatingSixAmbientRow23_longMatrixAB_entry02_06
  · exact alternatingSixAmbientRow23_longMatrixAB_entry02_07
  · exact alternatingSixAmbientRow23_longMatrixAB_entry02_08
  · exact alternatingSixAmbientRow23_longMatrixAB_entry02_09
  · exact alternatingSixAmbientRow23_longMatrixAB_entry03_00
  · exact alternatingSixAmbientRow23_longMatrixAB_entry03_01
  · exact alternatingSixAmbientRow23_longMatrixAB_entry03_02
  · exact alternatingSixAmbientRow23_longMatrixAB_entry03_03
  · exact alternatingSixAmbientRow23_longMatrixAB_entry03_04
  · exact alternatingSixAmbientRow23_longMatrixAB_entry03_05
  · exact alternatingSixAmbientRow23_longMatrixAB_entry03_06
  · exact alternatingSixAmbientRow23_longMatrixAB_entry03_07
  · exact alternatingSixAmbientRow23_longMatrixAB_entry03_08
  · exact alternatingSixAmbientRow23_longMatrixAB_entry03_09
  · exact alternatingSixAmbientRow23_longMatrixAB_entry04_00
  · exact alternatingSixAmbientRow23_longMatrixAB_entry04_01
  · exact alternatingSixAmbientRow23_longMatrixAB_entry04_02
  · exact alternatingSixAmbientRow23_longMatrixAB_entry04_03
  · exact alternatingSixAmbientRow23_longMatrixAB_entry04_04
  · exact alternatingSixAmbientRow23_longMatrixAB_entry04_05
  · exact alternatingSixAmbientRow23_longMatrixAB_entry04_06
  · exact alternatingSixAmbientRow23_longMatrixAB_entry04_07
  · exact alternatingSixAmbientRow23_longMatrixAB_entry04_08
  · exact alternatingSixAmbientRow23_longMatrixAB_entry04_09
  · exact alternatingSixAmbientRow23_longMatrixAB_entry05_00
  · exact alternatingSixAmbientRow23_longMatrixAB_entry05_01
  · exact alternatingSixAmbientRow23_longMatrixAB_entry05_02
  · exact alternatingSixAmbientRow23_longMatrixAB_entry05_03
  · exact alternatingSixAmbientRow23_longMatrixAB_entry05_04
  · exact alternatingSixAmbientRow23_longMatrixAB_entry05_05
  · exact alternatingSixAmbientRow23_longMatrixAB_entry05_06
  · exact alternatingSixAmbientRow23_longMatrixAB_entry05_07
  · exact alternatingSixAmbientRow23_longMatrixAB_entry05_08
  · exact alternatingSixAmbientRow23_longMatrixAB_entry05_09
  · exact alternatingSixAmbientRow23_longMatrixAB_entry06_00
  · exact alternatingSixAmbientRow23_longMatrixAB_entry06_01
  · exact alternatingSixAmbientRow23_longMatrixAB_entry06_02
  · exact alternatingSixAmbientRow23_longMatrixAB_entry06_03
  · exact alternatingSixAmbientRow23_longMatrixAB_entry06_04
  · exact alternatingSixAmbientRow23_longMatrixAB_entry06_05
  · exact alternatingSixAmbientRow23_longMatrixAB_entry06_06
  · exact alternatingSixAmbientRow23_longMatrixAB_entry06_07
  · exact alternatingSixAmbientRow23_longMatrixAB_entry06_08
  · exact alternatingSixAmbientRow23_longMatrixAB_entry06_09
  · exact alternatingSixAmbientRow23_longMatrixAB_entry07_00
  · exact alternatingSixAmbientRow23_longMatrixAB_entry07_01
  · exact alternatingSixAmbientRow23_longMatrixAB_entry07_02
  · exact alternatingSixAmbientRow23_longMatrixAB_entry07_03
  · exact alternatingSixAmbientRow23_longMatrixAB_entry07_04
  · exact alternatingSixAmbientRow23_longMatrixAB_entry07_05
  · exact alternatingSixAmbientRow23_longMatrixAB_entry07_06
  · exact alternatingSixAmbientRow23_longMatrixAB_entry07_07
  · exact alternatingSixAmbientRow23_longMatrixAB_entry07_08
  · exact alternatingSixAmbientRow23_longMatrixAB_entry07_09
  · exact alternatingSixAmbientRow23_longMatrixAB_entry08_00
  · exact alternatingSixAmbientRow23_longMatrixAB_entry08_01
  · exact alternatingSixAmbientRow23_longMatrixAB_entry08_02
  · exact alternatingSixAmbientRow23_longMatrixAB_entry08_03
  · exact alternatingSixAmbientRow23_longMatrixAB_entry08_04
  · exact alternatingSixAmbientRow23_longMatrixAB_entry08_05
  · exact alternatingSixAmbientRow23_longMatrixAB_entry08_06
  · exact alternatingSixAmbientRow23_longMatrixAB_entry08_07
  · exact alternatingSixAmbientRow23_longMatrixAB_entry08_08
  · exact alternatingSixAmbientRow23_longMatrixAB_entry08_09
  · exact alternatingSixAmbientRow23_longMatrixAB_entry09_00
  · exact alternatingSixAmbientRow23_longMatrixAB_entry09_01
  · exact alternatingSixAmbientRow23_longMatrixAB_entry09_02
  · exact alternatingSixAmbientRow23_longMatrixAB_entry09_03
  · exact alternatingSixAmbientRow23_longMatrixAB_entry09_04
  · exact alternatingSixAmbientRow23_longMatrixAB_entry09_05
  · exact alternatingSixAmbientRow23_longMatrixAB_entry09_06
  · exact alternatingSixAmbientRow23_longMatrixAB_entry09_07
  · exact alternatingSixAmbientRow23_longMatrixAB_entry09_08
  · exact alternatingSixAmbientRow23_longMatrixAB_entry09_09

end InductiveMcKay
end McKayConjecture
