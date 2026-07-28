/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow30LongWordData

/-!
# One checked row-30 long-word multiplication

This split generated module keeps each 15 by 15 multiplication
independently compilable under the default resource limits.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry00_00 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (0 : Fin 15) (0 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (0 : Fin 15) (0 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry00_01 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (0 : Fin 15) (1 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (0 : Fin 15) (1 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry00_02 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (0 : Fin 15) (2 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (0 : Fin 15) (2 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry00_03 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (0 : Fin 15) (3 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (0 : Fin 15) (3 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry00_04 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (0 : Fin 15) (4 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (0 : Fin 15) (4 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry00_05 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (0 : Fin 15) (5 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (0 : Fin 15) (5 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry00_06 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (0 : Fin 15) (6 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (0 : Fin 15) (6 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry00_07 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (0 : Fin 15) (7 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (0 : Fin 15) (7 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry00_08 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (0 : Fin 15) (8 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (0 : Fin 15) (8 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry00_09 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (0 : Fin 15) (9 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (0 : Fin 15) (9 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry00_10 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (0 : Fin 15) (10 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (0 : Fin 15) (10 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry00_11 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (0 : Fin 15) (11 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (0 : Fin 15) (11 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry00_12 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (0 : Fin 15) (12 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (0 : Fin 15) (12 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry00_13 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (0 : Fin 15) (13 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (0 : Fin 15) (13 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry00_14 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (0 : Fin 15) (14 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (0 : Fin 15) (14 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry01_00 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (1 : Fin 15) (0 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (1 : Fin 15) (0 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry01_01 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (1 : Fin 15) (1 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (1 : Fin 15) (1 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry01_02 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (1 : Fin 15) (2 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (1 : Fin 15) (2 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry01_03 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (1 : Fin 15) (3 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (1 : Fin 15) (3 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry01_04 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (1 : Fin 15) (4 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (1 : Fin 15) (4 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry01_05 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (1 : Fin 15) (5 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (1 : Fin 15) (5 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry01_06 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (1 : Fin 15) (6 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (1 : Fin 15) (6 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry01_07 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (1 : Fin 15) (7 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (1 : Fin 15) (7 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry01_08 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (1 : Fin 15) (8 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (1 : Fin 15) (8 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry01_09 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (1 : Fin 15) (9 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (1 : Fin 15) (9 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) + (2 : ℂ) * ζ ^ 4 - (2 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) + (2 : ℂ) * ζ ^ 4 - (2 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry01_10 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (1 : Fin 15) (10 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (1 : Fin 15) (10 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry01_11 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (1 : Fin 15) (11 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (1 : Fin 15) (11 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry01_12 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (1 : Fin 15) (12 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (1 : Fin 15) (12 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry01_13 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (1 : Fin 15) (13 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (1 : Fin 15) (13 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry01_14 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (1 : Fin 15) (14 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (1 : Fin 15) (14 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry02_00 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (2 : Fin 15) (0 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (2 : Fin 15) (0 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry02_01 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (2 : Fin 15) (1 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (2 : Fin 15) (1 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry02_02 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (2 : Fin 15) (2 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (2 : Fin 15) (2 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry02_03 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (2 : Fin 15) (3 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (2 : Fin 15) (3 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry02_04 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (2 : Fin 15) (4 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (2 : Fin 15) (4 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry02_05 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (2 : Fin 15) (5 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (2 : Fin 15) (5 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry02_06 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (2 : Fin 15) (6 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (2 : Fin 15) (6 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry02_07 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (2 : Fin 15) (7 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (2 : Fin 15) (7 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry02_08 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (2 : Fin 15) (8 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (2 : Fin 15) (8 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry02_09 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (2 : Fin 15) (9 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (2 : Fin 15) (9 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry02_10 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (2 : Fin 15) (10 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (2 : Fin 15) (10 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry02_11 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (2 : Fin 15) (11 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (2 : Fin 15) (11 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry02_12 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (2 : Fin 15) (12 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (2 : Fin 15) (12 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry02_13 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (2 : Fin 15) (13 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (2 : Fin 15) (13 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry02_14 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (2 : Fin 15) (14 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (2 : Fin 15) (14 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry03_00 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (3 : Fin 15) (0 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (3 : Fin 15) (0 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry03_01 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (3 : Fin 15) (1 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (3 : Fin 15) (1 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry03_02 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (3 : Fin 15) (2 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (3 : Fin 15) (2 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry03_03 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (3 : Fin 15) (3 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (3 : Fin 15) (3 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry03_04 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (3 : Fin 15) (4 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (3 : Fin 15) (4 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry03_05 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (3 : Fin 15) (5 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (3 : Fin 15) (5 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry03_06 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (3 : Fin 15) (6 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (3 : Fin 15) (6 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry03_07 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (3 : Fin 15) (7 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (3 : Fin 15) (7 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry03_08 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (3 : Fin 15) (8 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (3 : Fin 15) (8 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry03_09 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (3 : Fin 15) (9 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (3 : Fin 15) (9 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry03_10 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (3 : Fin 15) (10 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (3 : Fin 15) (10 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry03_11 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (3 : Fin 15) (11 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (3 : Fin 15) (11 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry03_12 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (3 : Fin 15) (12 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (3 : Fin 15) (12 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry03_13 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (3 : Fin 15) (13 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (3 : Fin 15) (13 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry03_14 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (3 : Fin 15) (14 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (3 : Fin 15) (14 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry04_00 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (4 : Fin 15) (0 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (4 : Fin 15) (0 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry04_01 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (4 : Fin 15) (1 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (4 : Fin 15) (1 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry04_02 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (4 : Fin 15) (2 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (4 : Fin 15) (2 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry04_03 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (4 : Fin 15) (3 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (4 : Fin 15) (3 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry04_04 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (4 : Fin 15) (4 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (4 : Fin 15) (4 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry04_05 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (4 : Fin 15) (5 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (4 : Fin 15) (5 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry04_06 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (4 : Fin 15) (6 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (4 : Fin 15) (6 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry04_07 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (4 : Fin 15) (7 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (4 : Fin 15) (7 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry04_08 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (4 : Fin 15) (8 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (4 : Fin 15) (8 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry04_09 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (4 : Fin 15) (9 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (4 : Fin 15) (9 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry04_10 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (4 : Fin 15) (10 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (4 : Fin 15) (10 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry04_11 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (4 : Fin 15) (11 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (4 : Fin 15) (11 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry04_12 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (4 : Fin 15) (12 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (4 : Fin 15) (12 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry04_13 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (4 : Fin 15) (13 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (4 : Fin 15) (13 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry04_14 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (4 : Fin 15) (14 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (4 : Fin 15) (14 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry05_00 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (5 : Fin 15) (0 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (5 : Fin 15) (0 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry05_01 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (5 : Fin 15) (1 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (5 : Fin 15) (1 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry05_02 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (5 : Fin 15) (2 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (5 : Fin 15) (2 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry05_03 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (5 : Fin 15) (3 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (5 : Fin 15) (3 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry05_04 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (5 : Fin 15) (4 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (5 : Fin 15) (4 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry05_05 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (5 : Fin 15) (5 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (5 : Fin 15) (5 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry05_06 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (5 : Fin 15) (6 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (5 : Fin 15) (6 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry05_07 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (5 : Fin 15) (7 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (5 : Fin 15) (7 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry05_08 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (5 : Fin 15) (8 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (5 : Fin 15) (8 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry05_09 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (5 : Fin 15) (9 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (5 : Fin 15) (9 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry05_10 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (5 : Fin 15) (10 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (5 : Fin 15) (10 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry05_11 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (5 : Fin 15) (11 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (5 : Fin 15) (11 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry05_12 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (5 : Fin 15) (12 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (5 : Fin 15) (12 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry05_13 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (5 : Fin 15) (13 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (5 : Fin 15) (13 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry05_14 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (5 : Fin 15) (14 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (5 : Fin 15) (14 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry06_00 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (6 : Fin 15) (0 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (6 : Fin 15) (0 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry06_01 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (6 : Fin 15) (1 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (6 : Fin 15) (1 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry06_02 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (6 : Fin 15) (2 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (6 : Fin 15) (2 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry06_03 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (6 : Fin 15) (3 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (6 : Fin 15) (3 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry06_04 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (6 : Fin 15) (4 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (6 : Fin 15) (4 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry06_05 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (6 : Fin 15) (5 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (6 : Fin 15) (5 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry06_06 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (6 : Fin 15) (6 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (6 : Fin 15) (6 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry06_07 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (6 : Fin 15) (7 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (6 : Fin 15) (7 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry06_08 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (6 : Fin 15) (8 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (6 : Fin 15) (8 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry06_09 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (6 : Fin 15) (9 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (6 : Fin 15) (9 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry06_10 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (6 : Fin 15) (10 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (6 : Fin 15) (10 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry06_11 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (6 : Fin 15) (11 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (6 : Fin 15) (11 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry06_12 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (6 : Fin 15) (12 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (6 : Fin 15) (12 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry06_13 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (6 : Fin 15) (13 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (6 : Fin 15) (13 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry06_14 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (6 : Fin 15) (14 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (6 : Fin 15) (14 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry07_00 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (7 : Fin 15) (0 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (7 : Fin 15) (0 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry07_01 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (7 : Fin 15) (1 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (7 : Fin 15) (1 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry07_02 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (7 : Fin 15) (2 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (7 : Fin 15) (2 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry07_03 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (7 : Fin 15) (3 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (7 : Fin 15) (3 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry07_04 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (7 : Fin 15) (4 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (7 : Fin 15) (4 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry07_05 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (7 : Fin 15) (5 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (7 : Fin 15) (5 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry07_06 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (7 : Fin 15) (6 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (7 : Fin 15) (6 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry07_07 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (7 : Fin 15) (7 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (7 : Fin 15) (7 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry07_08 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (7 : Fin 15) (8 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (7 : Fin 15) (8 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry07_09 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (7 : Fin 15) (9 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (7 : Fin 15) (9 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry07_10 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (7 : Fin 15) (10 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (7 : Fin 15) (10 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry07_11 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (7 : Fin 15) (11 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (7 : Fin 15) (11 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry07_12 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (7 : Fin 15) (12 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (7 : Fin 15) (12 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry07_13 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (7 : Fin 15) (13 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (7 : Fin 15) (13 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry07_14 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (7 : Fin 15) (14 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (7 : Fin 15) (14 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry08_00 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (8 : Fin 15) (0 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (8 : Fin 15) (0 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry08_01 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (8 : Fin 15) (1 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (8 : Fin 15) (1 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry08_02 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (8 : Fin 15) (2 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (8 : Fin 15) (2 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry08_03 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (8 : Fin 15) (3 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (8 : Fin 15) (3 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry08_04 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (8 : Fin 15) (4 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (8 : Fin 15) (4 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry08_05 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (8 : Fin 15) (5 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (8 : Fin 15) (5 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry08_06 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (8 : Fin 15) (6 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (8 : Fin 15) (6 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry08_07 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (8 : Fin 15) (7 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (8 : Fin 15) (7 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry08_08 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (8 : Fin 15) (8 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (8 : Fin 15) (8 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry08_09 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (8 : Fin 15) (9 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (8 : Fin 15) (9 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry08_10 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (8 : Fin 15) (10 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (8 : Fin 15) (10 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry08_11 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (8 : Fin 15) (11 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (8 : Fin 15) (11 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry08_12 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (8 : Fin 15) (12 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (8 : Fin 15) (12 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry08_13 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (8 : Fin 15) (13 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (8 : Fin 15) (13 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry08_14 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (8 : Fin 15) (14 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (8 : Fin 15) (14 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry09_00 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (9 : Fin 15) (0 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (9 : Fin 15) (0 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry09_01 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (9 : Fin 15) (1 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (9 : Fin 15) (1 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry09_02 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (9 : Fin 15) (2 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (9 : Fin 15) (2 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry09_03 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (9 : Fin 15) (3 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (9 : Fin 15) (3 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry09_04 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (9 : Fin 15) (4 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (9 : Fin 15) (4 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry09_05 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (9 : Fin 15) (5 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (9 : Fin 15) (5 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry09_06 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (9 : Fin 15) (6 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (9 : Fin 15) (6 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry09_07 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (9 : Fin 15) (7 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (9 : Fin 15) (7 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry09_08 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (9 : Fin 15) (8 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (9 : Fin 15) (8 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry09_09 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (9 : Fin 15) (9 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (9 : Fin 15) (9 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry09_10 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (9 : Fin 15) (10 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (9 : Fin 15) (10 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry09_11 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (9 : Fin 15) (11 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (9 : Fin 15) (11 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry09_12 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (9 : Fin 15) (12 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (9 : Fin 15) (12 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry09_13 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (9 : Fin 15) (13 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (9 : Fin 15) (13 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry09_14 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (9 : Fin 15) (14 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (9 : Fin 15) (14 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry10_00 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (10 : Fin 15) (0 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (10 : Fin 15) (0 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry10_01 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (10 : Fin 15) (1 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (10 : Fin 15) (1 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry10_02 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (10 : Fin 15) (2 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (10 : Fin 15) (2 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry10_03 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (10 : Fin 15) (3 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (10 : Fin 15) (3 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry10_04 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (10 : Fin 15) (4 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (10 : Fin 15) (4 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry10_05 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (10 : Fin 15) (5 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (10 : Fin 15) (5 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry10_06 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (10 : Fin 15) (6 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (10 : Fin 15) (6 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry10_07 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (10 : Fin 15) (7 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (10 : Fin 15) (7 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry10_08 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (10 : Fin 15) (8 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (10 : Fin 15) (8 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry10_09 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (10 : Fin 15) (9 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (10 : Fin 15) (9 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry10_10 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (10 : Fin 15) (10 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (10 : Fin 15) (10 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry10_11 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (10 : Fin 15) (11 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (10 : Fin 15) (11 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry10_12 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (10 : Fin 15) (12 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (10 : Fin 15) (12 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry10_13 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (10 : Fin 15) (13 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (10 : Fin 15) (13 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry10_14 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (10 : Fin 15) (14 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (10 : Fin 15) (14 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry11_00 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (11 : Fin 15) (0 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (11 : Fin 15) (0 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry11_01 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (11 : Fin 15) (1 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (11 : Fin 15) (1 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry11_02 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (11 : Fin 15) (2 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (11 : Fin 15) (2 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry11_03 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (11 : Fin 15) (3 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (11 : Fin 15) (3 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry11_04 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (11 : Fin 15) (4 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (11 : Fin 15) (4 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry11_05 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (11 : Fin 15) (5 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (11 : Fin 15) (5 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry11_06 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (11 : Fin 15) (6 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (11 : Fin 15) (6 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry11_07 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (11 : Fin 15) (7 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (11 : Fin 15) (7 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry11_08 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (11 : Fin 15) (8 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (11 : Fin 15) (8 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry11_09 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (11 : Fin 15) (9 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (11 : Fin 15) (9 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry11_10 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (11 : Fin 15) (10 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (11 : Fin 15) (10 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry11_11 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (11 : Fin 15) (11 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (11 : Fin 15) (11 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry11_12 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (11 : Fin 15) (12 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (11 : Fin 15) (12 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry11_13 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (11 : Fin 15) (13 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (11 : Fin 15) (13 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry11_14 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (11 : Fin 15) (14 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (11 : Fin 15) (14 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry12_00 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (12 : Fin 15) (0 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (12 : Fin 15) (0 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry12_01 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (12 : Fin 15) (1 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (12 : Fin 15) (1 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry12_02 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (12 : Fin 15) (2 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (12 : Fin 15) (2 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry12_03 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (12 : Fin 15) (3 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (12 : Fin 15) (3 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry12_04 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (12 : Fin 15) (4 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (12 : Fin 15) (4 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry12_05 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (12 : Fin 15) (5 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (12 : Fin 15) (5 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry12_06 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (12 : Fin 15) (6 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (12 : Fin 15) (6 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry12_07 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (12 : Fin 15) (7 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (12 : Fin 15) (7 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry12_08 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (12 : Fin 15) (8 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (12 : Fin 15) (8 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry12_09 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (12 : Fin 15) (9 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (12 : Fin 15) (9 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry12_10 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (12 : Fin 15) (10 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (12 : Fin 15) (10 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry12_11 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (12 : Fin 15) (11 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (12 : Fin 15) (11 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry12_12 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (12 : Fin 15) (12 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (12 : Fin 15) (12 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry12_13 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (12 : Fin 15) (13 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (12 : Fin 15) (13 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry12_14 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (12 : Fin 15) (14 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (12 : Fin 15) (14 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry13_00 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (13 : Fin 15) (0 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (13 : Fin 15) (0 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry13_01 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (13 : Fin 15) (1 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (13 : Fin 15) (1 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry13_02 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (13 : Fin 15) (2 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (13 : Fin 15) (2 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry13_03 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (13 : Fin 15) (3 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (13 : Fin 15) (3 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry13_04 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (13 : Fin 15) (4 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (13 : Fin 15) (4 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry13_05 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (13 : Fin 15) (5 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (13 : Fin 15) (5 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry13_06 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (13 : Fin 15) (6 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (13 : Fin 15) (6 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry13_07 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (13 : Fin 15) (7 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (13 : Fin 15) (7 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry13_08 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (13 : Fin 15) (8 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (13 : Fin 15) (8 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry13_09 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (13 : Fin 15) (9 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (13 : Fin 15) (9 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry13_10 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (13 : Fin 15) (10 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (13 : Fin 15) (10 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry13_11 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (13 : Fin 15) (11 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (13 : Fin 15) (11 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry13_12 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (13 : Fin 15) (12 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (13 : Fin 15) (12 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry13_13 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (13 : Fin 15) (13 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (13 : Fin 15) (13 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry13_14 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (13 : Fin 15) (14 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (13 : Fin 15) (14 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry14_00 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (14 : Fin 15) (0 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (14 : Fin 15) (0 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry14_01 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (14 : Fin 15) (1 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (14 : Fin 15) (1 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry14_02 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (14 : Fin 15) (2 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (14 : Fin 15) (2 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry14_03 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (14 : Fin 15) (3 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (14 : Fin 15) (3 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry14_04 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (14 : Fin 15) (4 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (14 : Fin 15) (4 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry14_05 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (14 : Fin 15) (5 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (14 : Fin 15) (5 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry14_06 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (14 : Fin 15) (6 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (14 : Fin 15) (6 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry14_07 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (14 : Fin 15) (7 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (14 : Fin 15) (7 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry14_08 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (14 : Fin 15) (8 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (14 : Fin 15) (8 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry14_09 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (14 : Fin 15) (9 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (14 : Fin 15) (9 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry14_10 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (14 : Fin 15) (10 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (14 : Fin 15) (10 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry14_11 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (14 : Fin 15) (11 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (14 : Fin 15) (11 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry14_12 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (14 : Fin 15) (12 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (14 : Fin 15) (12 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
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
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry14_13 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (14 : Fin 15) (13 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (14 : Fin 15) (13 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow30_longMatrixABBB_entry14_14 :
    (alternatingSixAmbientRow30LongMatrixABB
        * alternatingSixFiveAmbient_row30_matrixB)
          (14 : Fin 15) (14 : Fin 15) =
      alternatingSixAmbientRow30LongMatrixABBB
        (14 : Fin 15) (14 : Fin 15) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow30LongMatrixABB,
    alternatingSixFiveAmbient_row30_matrixB,
    alternatingSixAmbientRow30LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

theorem alternatingSixAmbientRow30_longMatrixABBB_mul :
    alternatingSixAmbientRow30LongMatrixABB *
        alternatingSixFiveAmbient_row30_matrixB =
      alternatingSixAmbientRow30LongMatrixABBB := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry00_00
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry00_01
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry00_02
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry00_03
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry00_04
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry00_05
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry00_06
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry00_07
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry00_08
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry00_09
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry00_10
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry00_11
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry00_12
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry00_13
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry00_14
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry01_00
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry01_01
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry01_02
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry01_03
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry01_04
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry01_05
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry01_06
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry01_07
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry01_08
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry01_09
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry01_10
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry01_11
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry01_12
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry01_13
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry01_14
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry02_00
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry02_01
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry02_02
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry02_03
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry02_04
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry02_05
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry02_06
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry02_07
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry02_08
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry02_09
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry02_10
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry02_11
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry02_12
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry02_13
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry02_14
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry03_00
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry03_01
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry03_02
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry03_03
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry03_04
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry03_05
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry03_06
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry03_07
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry03_08
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry03_09
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry03_10
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry03_11
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry03_12
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry03_13
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry03_14
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry04_00
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry04_01
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry04_02
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry04_03
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry04_04
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry04_05
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry04_06
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry04_07
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry04_08
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry04_09
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry04_10
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry04_11
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry04_12
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry04_13
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry04_14
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry05_00
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry05_01
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry05_02
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry05_03
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry05_04
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry05_05
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry05_06
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry05_07
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry05_08
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry05_09
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry05_10
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry05_11
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry05_12
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry05_13
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry05_14
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry06_00
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry06_01
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry06_02
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry06_03
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry06_04
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry06_05
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry06_06
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry06_07
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry06_08
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry06_09
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry06_10
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry06_11
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry06_12
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry06_13
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry06_14
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry07_00
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry07_01
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry07_02
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry07_03
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry07_04
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry07_05
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry07_06
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry07_07
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry07_08
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry07_09
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry07_10
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry07_11
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry07_12
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry07_13
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry07_14
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry08_00
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry08_01
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry08_02
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry08_03
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry08_04
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry08_05
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry08_06
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry08_07
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry08_08
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry08_09
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry08_10
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry08_11
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry08_12
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry08_13
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry08_14
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry09_00
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry09_01
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry09_02
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry09_03
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry09_04
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry09_05
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry09_06
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry09_07
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry09_08
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry09_09
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry09_10
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry09_11
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry09_12
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry09_13
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry09_14
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry10_00
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry10_01
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry10_02
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry10_03
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry10_04
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry10_05
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry10_06
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry10_07
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry10_08
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry10_09
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry10_10
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry10_11
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry10_12
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry10_13
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry10_14
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry11_00
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry11_01
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry11_02
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry11_03
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry11_04
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry11_05
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry11_06
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry11_07
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry11_08
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry11_09
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry11_10
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry11_11
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry11_12
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry11_13
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry11_14
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry12_00
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry12_01
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry12_02
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry12_03
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry12_04
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry12_05
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry12_06
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry12_07
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry12_08
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry12_09
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry12_10
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry12_11
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry12_12
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry12_13
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry12_14
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry13_00
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry13_01
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry13_02
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry13_03
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry13_04
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry13_05
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry13_06
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry13_07
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry13_08
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry13_09
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry13_10
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry13_11
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry13_12
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry13_13
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry13_14
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry14_00
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry14_01
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry14_02
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry14_03
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry14_04
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry14_05
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry14_06
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry14_07
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry14_08
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry14_09
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry14_10
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry14_11
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry14_12
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry14_13
  · exact alternatingSixAmbientRow30_longMatrixABBB_entry14_14

end InductiveMcKay
end McKayConjecture
