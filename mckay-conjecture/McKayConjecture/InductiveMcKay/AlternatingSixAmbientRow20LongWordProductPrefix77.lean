/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow20LongWordData

/-!
# One checked row-20 long-word multiplication

This split generated module keeps each 9 by 9 multiplication
independently compilable under the default resource limits.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry00_00 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (0 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (0 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry00_01 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (0 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (0 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry00_02 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (0 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (0 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry00_03 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (0 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (0 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry00_04 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (0 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (0 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry00_05 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (0 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (0 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry00_06 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (0 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (0 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry00_07 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (0 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (0 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry00_08 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (0 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (0 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry01_00 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (1 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (1 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry01_01 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (1 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (1 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry01_02 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (1 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (1 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry01_03 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (1 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (1 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry01_04 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (1 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (1 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry01_05 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (1 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (1 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry01_06 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (1 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (1 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry01_07 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (1 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (1 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry01_08 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (1 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (1 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry02_00 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (2 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (2 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry02_01 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (2 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (2 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry02_02 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (2 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (2 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry02_03 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (2 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (2 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry02_04 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (2 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (2 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry02_05 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (2 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (2 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry02_06 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (2 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (2 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry02_07 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (2 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (2 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry02_08 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (2 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (2 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry03_00 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (3 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (3 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry03_01 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (3 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (3 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry03_02 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (3 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (3 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry03_03 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (3 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (3 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry03_04 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (3 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (3 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry03_05 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (3 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (3 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry03_06 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (3 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (3 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry03_07 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (3 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (3 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry03_08 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (3 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (3 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry04_00 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (4 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (4 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry04_01 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (4 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (4 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry04_02 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (4 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (4 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry04_03 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (4 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (4 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry04_04 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (4 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (4 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry04_05 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (4 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (4 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry04_06 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (4 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (4 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry04_07 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (4 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (4 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry04_08 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (4 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (4 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry05_00 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (5 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (5 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry05_01 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (5 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (5 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry05_02 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (5 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (5 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry05_03 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (5 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (5 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry05_04 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (5 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (5 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry05_05 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (5 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (5 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry05_06 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (5 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (5 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry05_07 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (5 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (5 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry05_08 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (5 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (5 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry06_00 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (6 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (6 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry06_01 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (6 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (6 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry06_02 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (6 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (6 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry06_03 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (6 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (6 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry06_04 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (6 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (6 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry06_05 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (6 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (6 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry06_06 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (6 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (6 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry06_07 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (6 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (6 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry06_08 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (6 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (6 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry07_00 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (7 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (7 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry07_01 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (7 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (7 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry07_02 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (7 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (7 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry07_03 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (7 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (7 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry07_04 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (7 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (7 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry07_05 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (7 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (7 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry07_06 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (7 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (7 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry07_07 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (7 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (7 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry07_08 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (7 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (7 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry08_00 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (8 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (8 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry08_01 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (8 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (8 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry08_02 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (8 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (8 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry08_03 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (8 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (8 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry08_04 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (8 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (8 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry08_05 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (8 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (8 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry08_06 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (8 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (8 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry08_07 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (8 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (8 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow20_longPrefix77_entry08_08 :
    (alternatingSixAmbientRow20LongMatrixAB
        * alternatingSixAmbientRow20LongMatrixABB)
          (8 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow20LongPrefix77
        (8 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow20LongMatrixAB,
    alternatingSixAmbientRow20LongMatrixABB,
    alternatingSixAmbientRow20LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

theorem alternatingSixAmbientRow20_longPrefix77_mul :
    alternatingSixAmbientRow20LongMatrixAB *
        alternatingSixAmbientRow20LongMatrixABB =
      alternatingSixAmbientRow20LongPrefix77 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientRow20_longPrefix77_entry00_00
  · exact alternatingSixAmbientRow20_longPrefix77_entry00_01
  · exact alternatingSixAmbientRow20_longPrefix77_entry00_02
  · exact alternatingSixAmbientRow20_longPrefix77_entry00_03
  · exact alternatingSixAmbientRow20_longPrefix77_entry00_04
  · exact alternatingSixAmbientRow20_longPrefix77_entry00_05
  · exact alternatingSixAmbientRow20_longPrefix77_entry00_06
  · exact alternatingSixAmbientRow20_longPrefix77_entry00_07
  · exact alternatingSixAmbientRow20_longPrefix77_entry00_08
  · exact alternatingSixAmbientRow20_longPrefix77_entry01_00
  · exact alternatingSixAmbientRow20_longPrefix77_entry01_01
  · exact alternatingSixAmbientRow20_longPrefix77_entry01_02
  · exact alternatingSixAmbientRow20_longPrefix77_entry01_03
  · exact alternatingSixAmbientRow20_longPrefix77_entry01_04
  · exact alternatingSixAmbientRow20_longPrefix77_entry01_05
  · exact alternatingSixAmbientRow20_longPrefix77_entry01_06
  · exact alternatingSixAmbientRow20_longPrefix77_entry01_07
  · exact alternatingSixAmbientRow20_longPrefix77_entry01_08
  · exact alternatingSixAmbientRow20_longPrefix77_entry02_00
  · exact alternatingSixAmbientRow20_longPrefix77_entry02_01
  · exact alternatingSixAmbientRow20_longPrefix77_entry02_02
  · exact alternatingSixAmbientRow20_longPrefix77_entry02_03
  · exact alternatingSixAmbientRow20_longPrefix77_entry02_04
  · exact alternatingSixAmbientRow20_longPrefix77_entry02_05
  · exact alternatingSixAmbientRow20_longPrefix77_entry02_06
  · exact alternatingSixAmbientRow20_longPrefix77_entry02_07
  · exact alternatingSixAmbientRow20_longPrefix77_entry02_08
  · exact alternatingSixAmbientRow20_longPrefix77_entry03_00
  · exact alternatingSixAmbientRow20_longPrefix77_entry03_01
  · exact alternatingSixAmbientRow20_longPrefix77_entry03_02
  · exact alternatingSixAmbientRow20_longPrefix77_entry03_03
  · exact alternatingSixAmbientRow20_longPrefix77_entry03_04
  · exact alternatingSixAmbientRow20_longPrefix77_entry03_05
  · exact alternatingSixAmbientRow20_longPrefix77_entry03_06
  · exact alternatingSixAmbientRow20_longPrefix77_entry03_07
  · exact alternatingSixAmbientRow20_longPrefix77_entry03_08
  · exact alternatingSixAmbientRow20_longPrefix77_entry04_00
  · exact alternatingSixAmbientRow20_longPrefix77_entry04_01
  · exact alternatingSixAmbientRow20_longPrefix77_entry04_02
  · exact alternatingSixAmbientRow20_longPrefix77_entry04_03
  · exact alternatingSixAmbientRow20_longPrefix77_entry04_04
  · exact alternatingSixAmbientRow20_longPrefix77_entry04_05
  · exact alternatingSixAmbientRow20_longPrefix77_entry04_06
  · exact alternatingSixAmbientRow20_longPrefix77_entry04_07
  · exact alternatingSixAmbientRow20_longPrefix77_entry04_08
  · exact alternatingSixAmbientRow20_longPrefix77_entry05_00
  · exact alternatingSixAmbientRow20_longPrefix77_entry05_01
  · exact alternatingSixAmbientRow20_longPrefix77_entry05_02
  · exact alternatingSixAmbientRow20_longPrefix77_entry05_03
  · exact alternatingSixAmbientRow20_longPrefix77_entry05_04
  · exact alternatingSixAmbientRow20_longPrefix77_entry05_05
  · exact alternatingSixAmbientRow20_longPrefix77_entry05_06
  · exact alternatingSixAmbientRow20_longPrefix77_entry05_07
  · exact alternatingSixAmbientRow20_longPrefix77_entry05_08
  · exact alternatingSixAmbientRow20_longPrefix77_entry06_00
  · exact alternatingSixAmbientRow20_longPrefix77_entry06_01
  · exact alternatingSixAmbientRow20_longPrefix77_entry06_02
  · exact alternatingSixAmbientRow20_longPrefix77_entry06_03
  · exact alternatingSixAmbientRow20_longPrefix77_entry06_04
  · exact alternatingSixAmbientRow20_longPrefix77_entry06_05
  · exact alternatingSixAmbientRow20_longPrefix77_entry06_06
  · exact alternatingSixAmbientRow20_longPrefix77_entry06_07
  · exact alternatingSixAmbientRow20_longPrefix77_entry06_08
  · exact alternatingSixAmbientRow20_longPrefix77_entry07_00
  · exact alternatingSixAmbientRow20_longPrefix77_entry07_01
  · exact alternatingSixAmbientRow20_longPrefix77_entry07_02
  · exact alternatingSixAmbientRow20_longPrefix77_entry07_03
  · exact alternatingSixAmbientRow20_longPrefix77_entry07_04
  · exact alternatingSixAmbientRow20_longPrefix77_entry07_05
  · exact alternatingSixAmbientRow20_longPrefix77_entry07_06
  · exact alternatingSixAmbientRow20_longPrefix77_entry07_07
  · exact alternatingSixAmbientRow20_longPrefix77_entry07_08
  · exact alternatingSixAmbientRow20_longPrefix77_entry08_00
  · exact alternatingSixAmbientRow20_longPrefix77_entry08_01
  · exact alternatingSixAmbientRow20_longPrefix77_entry08_02
  · exact alternatingSixAmbientRow20_longPrefix77_entry08_03
  · exact alternatingSixAmbientRow20_longPrefix77_entry08_04
  · exact alternatingSixAmbientRow20_longPrefix77_entry08_05
  · exact alternatingSixAmbientRow20_longPrefix77_entry08_06
  · exact alternatingSixAmbientRow20_longPrefix77_entry08_07
  · exact alternatingSixAmbientRow20_longPrefix77_entry08_08

end InductiveMcKay
end McKayConjecture
