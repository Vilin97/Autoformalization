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
private theorem alternatingSixAmbientRow23_longPrefix77_entry00_00 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (0 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (0 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry00_01 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (0 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (0 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry00_02 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (0 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (0 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry00_03 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (0 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (0 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry00_04 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (0 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (0 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry00_05 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (0 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (0 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry00_06 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (0 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (0 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry00_07 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (0 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (0 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry00_08 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (0 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (0 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry00_09 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (0 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (0 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry01_00 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (1 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (1 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry01_01 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (1 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (1 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry01_02 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (1 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (1 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry01_03 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (1 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (1 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry01_04 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (1 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (1 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry01_05 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (1 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (1 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry01_06 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (1 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (1 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry01_07 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (1 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (1 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry01_08 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (1 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (1 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry01_09 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (1 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (1 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry02_00 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (2 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (2 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry02_01 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (2 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (2 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry02_02 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (2 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (2 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry02_03 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (2 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (2 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry02_04 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (2 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (2 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry02_05 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (2 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (2 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry02_06 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (2 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (2 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry02_07 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (2 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (2 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry02_08 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (2 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (2 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry02_09 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (2 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (2 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry03_00 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (3 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (3 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry03_01 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (3 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (3 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry03_02 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (3 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (3 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry03_03 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (3 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (3 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry03_04 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (3 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (3 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry03_05 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (3 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (3 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry03_06 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (3 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (3 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry03_07 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (3 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (3 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry03_08 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (3 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (3 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry03_09 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (3 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (3 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry04_00 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (4 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (4 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry04_01 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (4 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (4 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry04_02 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (4 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (4 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry04_03 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (4 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (4 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry04_04 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (4 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (4 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry04_05 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (4 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (4 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry04_06 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (4 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (4 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry04_07 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (4 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (4 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry04_08 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (4 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (4 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry04_09 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (4 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (4 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry05_00 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (5 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (5 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry05_01 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (5 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (5 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry05_02 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (5 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (5 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry05_03 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (5 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (5 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry05_04 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (5 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (5 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry05_05 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (5 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (5 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry05_06 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (5 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (5 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry05_07 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (5 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (5 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry05_08 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (5 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (5 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry05_09 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (5 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (5 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry06_00 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (6 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (6 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry06_01 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (6 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (6 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry06_02 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (6 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (6 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry06_03 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (6 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (6 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry06_04 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (6 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (6 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry06_05 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (6 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (6 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry06_06 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (6 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (6 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry06_07 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (6 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (6 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry06_08 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (6 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (6 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry06_09 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (6 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (6 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry07_00 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (7 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (7 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry07_01 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (7 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (7 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry07_02 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (7 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (7 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry07_03 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (7 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (7 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry07_04 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (7 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (7 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry07_05 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (7 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (7 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry07_06 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (7 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (7 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry07_07 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (7 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (7 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry07_08 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (7 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (7 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry07_09 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (7 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (7 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry08_00 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (8 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (8 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry08_01 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (8 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (8 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry08_02 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (8 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (8 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry08_03 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (8 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (8 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry08_04 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (8 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (8 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry08_05 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (8 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (8 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry08_06 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (8 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (8 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry08_07 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (8 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (8 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry08_08 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (8 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (8 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry08_09 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (8 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (8 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry09_00 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (9 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (9 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry09_01 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (9 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (9 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry09_02 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (9 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (9 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry09_03 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (9 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (9 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry09_04 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (9 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (9 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry09_05 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (9 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (9 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry09_06 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (9 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (9 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry09_07 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (9 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (9 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry09_08 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (9 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (9 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow23_longPrefix77_entry09_09 :
    (alternatingSixAmbientRow23LongMatrixAB
        * alternatingSixAmbientRow23LongMatrixABB)
          (9 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow23LongPrefix77
        (9 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow23LongMatrixAB,
    alternatingSixAmbientRow23LongMatrixABB,
    alternatingSixAmbientRow23LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

theorem alternatingSixAmbientRow23_longPrefix77_mul :
    alternatingSixAmbientRow23LongMatrixAB *
        alternatingSixAmbientRow23LongMatrixABB =
      alternatingSixAmbientRow23LongPrefix77 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientRow23_longPrefix77_entry00_00
  · exact alternatingSixAmbientRow23_longPrefix77_entry00_01
  · exact alternatingSixAmbientRow23_longPrefix77_entry00_02
  · exact alternatingSixAmbientRow23_longPrefix77_entry00_03
  · exact alternatingSixAmbientRow23_longPrefix77_entry00_04
  · exact alternatingSixAmbientRow23_longPrefix77_entry00_05
  · exact alternatingSixAmbientRow23_longPrefix77_entry00_06
  · exact alternatingSixAmbientRow23_longPrefix77_entry00_07
  · exact alternatingSixAmbientRow23_longPrefix77_entry00_08
  · exact alternatingSixAmbientRow23_longPrefix77_entry00_09
  · exact alternatingSixAmbientRow23_longPrefix77_entry01_00
  · exact alternatingSixAmbientRow23_longPrefix77_entry01_01
  · exact alternatingSixAmbientRow23_longPrefix77_entry01_02
  · exact alternatingSixAmbientRow23_longPrefix77_entry01_03
  · exact alternatingSixAmbientRow23_longPrefix77_entry01_04
  · exact alternatingSixAmbientRow23_longPrefix77_entry01_05
  · exact alternatingSixAmbientRow23_longPrefix77_entry01_06
  · exact alternatingSixAmbientRow23_longPrefix77_entry01_07
  · exact alternatingSixAmbientRow23_longPrefix77_entry01_08
  · exact alternatingSixAmbientRow23_longPrefix77_entry01_09
  · exact alternatingSixAmbientRow23_longPrefix77_entry02_00
  · exact alternatingSixAmbientRow23_longPrefix77_entry02_01
  · exact alternatingSixAmbientRow23_longPrefix77_entry02_02
  · exact alternatingSixAmbientRow23_longPrefix77_entry02_03
  · exact alternatingSixAmbientRow23_longPrefix77_entry02_04
  · exact alternatingSixAmbientRow23_longPrefix77_entry02_05
  · exact alternatingSixAmbientRow23_longPrefix77_entry02_06
  · exact alternatingSixAmbientRow23_longPrefix77_entry02_07
  · exact alternatingSixAmbientRow23_longPrefix77_entry02_08
  · exact alternatingSixAmbientRow23_longPrefix77_entry02_09
  · exact alternatingSixAmbientRow23_longPrefix77_entry03_00
  · exact alternatingSixAmbientRow23_longPrefix77_entry03_01
  · exact alternatingSixAmbientRow23_longPrefix77_entry03_02
  · exact alternatingSixAmbientRow23_longPrefix77_entry03_03
  · exact alternatingSixAmbientRow23_longPrefix77_entry03_04
  · exact alternatingSixAmbientRow23_longPrefix77_entry03_05
  · exact alternatingSixAmbientRow23_longPrefix77_entry03_06
  · exact alternatingSixAmbientRow23_longPrefix77_entry03_07
  · exact alternatingSixAmbientRow23_longPrefix77_entry03_08
  · exact alternatingSixAmbientRow23_longPrefix77_entry03_09
  · exact alternatingSixAmbientRow23_longPrefix77_entry04_00
  · exact alternatingSixAmbientRow23_longPrefix77_entry04_01
  · exact alternatingSixAmbientRow23_longPrefix77_entry04_02
  · exact alternatingSixAmbientRow23_longPrefix77_entry04_03
  · exact alternatingSixAmbientRow23_longPrefix77_entry04_04
  · exact alternatingSixAmbientRow23_longPrefix77_entry04_05
  · exact alternatingSixAmbientRow23_longPrefix77_entry04_06
  · exact alternatingSixAmbientRow23_longPrefix77_entry04_07
  · exact alternatingSixAmbientRow23_longPrefix77_entry04_08
  · exact alternatingSixAmbientRow23_longPrefix77_entry04_09
  · exact alternatingSixAmbientRow23_longPrefix77_entry05_00
  · exact alternatingSixAmbientRow23_longPrefix77_entry05_01
  · exact alternatingSixAmbientRow23_longPrefix77_entry05_02
  · exact alternatingSixAmbientRow23_longPrefix77_entry05_03
  · exact alternatingSixAmbientRow23_longPrefix77_entry05_04
  · exact alternatingSixAmbientRow23_longPrefix77_entry05_05
  · exact alternatingSixAmbientRow23_longPrefix77_entry05_06
  · exact alternatingSixAmbientRow23_longPrefix77_entry05_07
  · exact alternatingSixAmbientRow23_longPrefix77_entry05_08
  · exact alternatingSixAmbientRow23_longPrefix77_entry05_09
  · exact alternatingSixAmbientRow23_longPrefix77_entry06_00
  · exact alternatingSixAmbientRow23_longPrefix77_entry06_01
  · exact alternatingSixAmbientRow23_longPrefix77_entry06_02
  · exact alternatingSixAmbientRow23_longPrefix77_entry06_03
  · exact alternatingSixAmbientRow23_longPrefix77_entry06_04
  · exact alternatingSixAmbientRow23_longPrefix77_entry06_05
  · exact alternatingSixAmbientRow23_longPrefix77_entry06_06
  · exact alternatingSixAmbientRow23_longPrefix77_entry06_07
  · exact alternatingSixAmbientRow23_longPrefix77_entry06_08
  · exact alternatingSixAmbientRow23_longPrefix77_entry06_09
  · exact alternatingSixAmbientRow23_longPrefix77_entry07_00
  · exact alternatingSixAmbientRow23_longPrefix77_entry07_01
  · exact alternatingSixAmbientRow23_longPrefix77_entry07_02
  · exact alternatingSixAmbientRow23_longPrefix77_entry07_03
  · exact alternatingSixAmbientRow23_longPrefix77_entry07_04
  · exact alternatingSixAmbientRow23_longPrefix77_entry07_05
  · exact alternatingSixAmbientRow23_longPrefix77_entry07_06
  · exact alternatingSixAmbientRow23_longPrefix77_entry07_07
  · exact alternatingSixAmbientRow23_longPrefix77_entry07_08
  · exact alternatingSixAmbientRow23_longPrefix77_entry07_09
  · exact alternatingSixAmbientRow23_longPrefix77_entry08_00
  · exact alternatingSixAmbientRow23_longPrefix77_entry08_01
  · exact alternatingSixAmbientRow23_longPrefix77_entry08_02
  · exact alternatingSixAmbientRow23_longPrefix77_entry08_03
  · exact alternatingSixAmbientRow23_longPrefix77_entry08_04
  · exact alternatingSixAmbientRow23_longPrefix77_entry08_05
  · exact alternatingSixAmbientRow23_longPrefix77_entry08_06
  · exact alternatingSixAmbientRow23_longPrefix77_entry08_07
  · exact alternatingSixAmbientRow23_longPrefix77_entry08_08
  · exact alternatingSixAmbientRow23_longPrefix77_entry08_09
  · exact alternatingSixAmbientRow23_longPrefix77_entry09_00
  · exact alternatingSixAmbientRow23_longPrefix77_entry09_01
  · exact alternatingSixAmbientRow23_longPrefix77_entry09_02
  · exact alternatingSixAmbientRow23_longPrefix77_entry09_03
  · exact alternatingSixAmbientRow23_longPrefix77_entry09_04
  · exact alternatingSixAmbientRow23_longPrefix77_entry09_05
  · exact alternatingSixAmbientRow23_longPrefix77_entry09_06
  · exact alternatingSixAmbientRow23_longPrefix77_entry09_07
  · exact alternatingSixAmbientRow23_longPrefix77_entry09_08
  · exact alternatingSixAmbientRow23_longPrefix77_entry09_09

end InductiveMcKay
end McKayConjecture
