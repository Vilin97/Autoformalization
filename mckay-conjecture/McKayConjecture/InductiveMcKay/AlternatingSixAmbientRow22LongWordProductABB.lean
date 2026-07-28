/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow22LongWordData

/-!
# One checked row-22 long-word multiplication

This split generated module keeps each 9 by 9 multiplication
independently compilable under the default resource limits.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry00_00 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (0 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (0 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((8 : ℂ) - (8 : ℂ) * ζ ^ 4 + (8 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((8 : ℂ) - (8 : ℂ) * ζ ^ 4 + (8 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry00_01 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (0 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (0 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(5 : ℂ) + (5 : ℂ) * ζ ^ 4 - (5 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(5 : ℂ) + (5 : ℂ) * ζ ^ 4 - (5 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry00_02 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (0 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (0 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(11 : ℂ) + (11 : ℂ) * ζ ^ 4 - (11 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(11 : ℂ) + (11 : ℂ) * ζ ^ 4 - (11 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry00_03 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (0 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (0 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(6 : ℂ) + (6 : ℂ) * ζ ^ 4 - (6 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(6 : ℂ) + (6 : ℂ) * ζ ^ 4 - (6 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry00_04 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (0 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (0 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((7 : ℂ) - (7 : ℂ) * ζ ^ 4 + (7 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((7 : ℂ) - (7 : ℂ) * ζ ^ 4 + (7 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry00_05 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (0 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (0 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(8 : ℂ) + (8 : ℂ) * ζ ^ 4 - (8 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(8 : ℂ) + (8 : ℂ) * ζ ^ 4 - (8 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry00_06 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (0 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (0 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry00_07 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (0 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (0 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry00_08 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (0 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (0 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(11 : ℂ) + (11 : ℂ) * ζ ^ 4 - (11 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(11 : ℂ) + (11 : ℂ) * ζ ^ 4 - (11 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry01_00 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (1 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (1 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(13 : ℂ) + (13 : ℂ) * ζ ^ 4 - (13 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(13 : ℂ) + (13 : ℂ) * ζ ^ 4 - (13 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry01_01 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (1 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (1 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((9 : ℂ) - (9 : ℂ) * ζ ^ 4 + (9 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((9 : ℂ) - (9 : ℂ) * ζ ^ 4 + (9 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry01_02 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (1 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (1 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((22 : ℂ) - (22 : ℂ) * ζ ^ 4 + (22 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((22 : ℂ) - (22 : ℂ) * ζ ^ 4 + (22 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry01_03 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (1 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (1 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((14 : ℂ) - (14 : ℂ) * ζ ^ 4 + (14 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((14 : ℂ) - (14 : ℂ) * ζ ^ 4 + (14 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry01_04 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (1 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (1 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(15 : ℂ) + (15 : ℂ) * ζ ^ 4 - (15 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(15 : ℂ) + (15 : ℂ) * ζ ^ 4 - (15 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry01_05 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (1 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (1 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((19 : ℂ) - (19 : ℂ) * ζ ^ 4 + (19 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((19 : ℂ) - (19 : ℂ) * ζ ^ 4 + (19 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry01_06 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (1 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (1 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(4 : ℂ) + (4 : ℂ) * ζ ^ 4 - (4 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(4 : ℂ) + (4 : ℂ) * ζ ^ 4 - (4 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry01_07 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (1 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (1 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry01_08 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (1 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (1 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((18 : ℂ) - (18 : ℂ) * ζ ^ 4 + (18 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((18 : ℂ) - (18 : ℂ) * ζ ^ 4 + (18 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry02_00 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (2 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (2 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((8 : ℂ) - (8 : ℂ) * ζ ^ 4 + (8 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((8 : ℂ) - (8 : ℂ) * ζ ^ 4 + (8 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry02_01 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (2 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (2 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(4 : ℂ) + (4 : ℂ) * ζ ^ 4 - (4 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(4 : ℂ) + (4 : ℂ) * ζ ^ 4 - (4 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry02_02 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (2 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (2 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(15 : ℂ) + (15 : ℂ) * ζ ^ 4 - (15 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(15 : ℂ) + (15 : ℂ) * ζ ^ 4 - (15 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry02_03 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (2 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (2 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(10 : ℂ) + (10 : ℂ) * ζ ^ 4 - (10 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(10 : ℂ) + (10 : ℂ) * ζ ^ 4 - (10 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry02_04 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (2 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (2 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((10 : ℂ) - (10 : ℂ) * ζ ^ 4 + (10 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((10 : ℂ) - (10 : ℂ) * ζ ^ 4 + (10 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry02_05 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (2 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (2 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(14 : ℂ) + (14 : ℂ) * ζ ^ 4 - (14 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(14 : ℂ) + (14 : ℂ) * ζ ^ 4 - (14 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry02_06 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (2 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (2 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((3 : ℂ) - (3 : ℂ) * ζ ^ 4 + (3 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((3 : ℂ) - (3 : ℂ) * ζ ^ 4 + (3 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry02_07 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (2 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (2 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry02_08 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (2 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (2 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(11 : ℂ) + (11 : ℂ) * ζ ^ 4 - (11 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(11 : ℂ) + (11 : ℂ) * ζ ^ 4 - (11 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry03_00 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (3 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (3 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((4 : ℂ) - (4 : ℂ) * ζ ^ 4 + (4 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((4 : ℂ) - (4 : ℂ) * ζ ^ 4 + (4 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry03_01 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (3 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (3 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry03_02 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (3 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (3 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry03_03 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (3 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (3 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry03_04 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (3 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (3 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry03_05 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (3 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (3 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry03_06 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (3 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (3 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry03_07 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (3 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (3 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(3 : ℂ) + (3 : ℂ) * ζ ^ 4 - (3 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(3 : ℂ) + (3 : ℂ) * ζ ^ 4 - (3 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry03_08 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (3 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (3 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(6 : ℂ) + (6 : ℂ) * ζ ^ 4 - (6 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(6 : ℂ) + (6 : ℂ) * ζ ^ 4 - (6 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry04_00 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (4 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (4 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(23 : ℂ) + (23 : ℂ) * ζ ^ 4 - (23 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(23 : ℂ) + (23 : ℂ) * ζ ^ 4 - (23 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry04_01 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (4 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (4 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(6 : ℂ) + (6 : ℂ) * ζ ^ 4 - (6 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(6 : ℂ) + (6 : ℂ) * ζ ^ 4 - (6 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry04_02 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (4 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (4 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(3 : ℂ) + (3 : ℂ) * ζ ^ 4 - (3 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(3 : ℂ) + (3 : ℂ) * ζ ^ 4 - (3 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry04_03 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (4 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (4 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry04_04 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (4 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (4 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((6 : ℂ) - (6 : ℂ) * ζ ^ 4 + (6 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((6 : ℂ) - (6 : ℂ) * ζ ^ 4 + (6 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry04_05 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (4 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (4 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(7 : ℂ) + (7 : ℂ) * ζ ^ 4 - (7 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(7 : ℂ) + (7 : ℂ) * ζ ^ 4 - (7 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry04_06 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (4 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (4 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry04_07 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (4 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (4 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((13 : ℂ) - (13 : ℂ) * ζ ^ 4 + (13 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((13 : ℂ) - (13 : ℂ) * ζ ^ 4 + (13 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry04_08 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (4 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (4 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((30 : ℂ) - (30 : ℂ) * ζ ^ 4 + (30 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((30 : ℂ) - (30 : ℂ) * ζ ^ 4 + (30 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry05_00 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (5 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (5 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(14 : ℂ) + (14 : ℂ) * ζ ^ 4 - (14 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(14 : ℂ) + (14 : ℂ) * ζ ^ 4 - (14 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry05_01 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (5 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (5 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry05_02 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (5 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (5 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((4 : ℂ) - (4 : ℂ) * ζ ^ 4 + (4 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((4 : ℂ) - (4 : ℂ) * ζ ^ 4 + (4 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry05_03 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (5 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (5 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((3 : ℂ) - (3 : ℂ) * ζ ^ 4 + (3 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((3 : ℂ) - (3 : ℂ) * ζ ^ 4 + (3 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry05_04 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (5 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (5 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry05_05 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (5 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (5 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry05_06 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (5 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (5 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry05_07 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (5 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (5 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((6 : ℂ) - (6 : ℂ) * ζ ^ 4 + (6 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((6 : ℂ) - (6 : ℂ) * ζ ^ 4 + (6 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry05_08 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (5 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (5 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((19 : ℂ) - (19 : ℂ) * ζ ^ 4 + (19 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((19 : ℂ) - (19 : ℂ) * ζ ^ 4 + (19 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry06_00 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (6 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (6 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((10 : ℂ) - (10 : ℂ) * ζ ^ 4 + (10 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((10 : ℂ) - (10 : ℂ) * ζ ^ 4 + (10 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry06_01 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (6 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (6 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry06_02 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (6 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (6 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(5 : ℂ) + (5 : ℂ) * ζ ^ 4 - (5 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(5 : ℂ) + (5 : ℂ) * ζ ^ 4 - (5 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry06_03 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (6 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (6 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(4 : ℂ) + (4 : ℂ) * ζ ^ 4 - (4 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(4 : ℂ) + (4 : ℂ) * ζ ^ 4 - (4 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry06_04 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (6 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (6 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry06_05 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (6 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (6 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(4 : ℂ) + (4 : ℂ) * ζ ^ 4 - (4 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(4 : ℂ) + (4 : ℂ) * ζ ^ 4 - (4 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry06_06 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (6 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (6 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry06_07 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (6 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (6 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(3 : ℂ) + (3 : ℂ) * ζ ^ 4 - (3 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(3 : ℂ) + (3 : ℂ) * ζ ^ 4 - (3 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry06_08 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (6 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (6 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(11 : ℂ) + (11 : ℂ) * ζ ^ 4 - (11 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(11 : ℂ) + (11 : ℂ) * ζ ^ 4 - (11 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry07_00 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (7 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (7 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((10 : ℂ) - (10 : ℂ) * ζ ^ 4 + (10 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((10 : ℂ) - (10 : ℂ) * ζ ^ 4 + (10 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry07_01 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (7 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (7 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry07_02 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (7 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (7 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(5 : ℂ) + (5 : ℂ) * ζ ^ 4 - (5 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(5 : ℂ) + (5 : ℂ) * ζ ^ 4 - (5 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry07_03 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (7 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (7 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(4 : ℂ) + (4 : ℂ) * ζ ^ 4 - (4 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(4 : ℂ) + (4 : ℂ) * ζ ^ 4 - (4 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry07_04 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (7 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (7 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry07_05 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (7 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (7 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(4 : ℂ) + (4 : ℂ) * ζ ^ 4 - (4 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(4 : ℂ) + (4 : ℂ) * ζ ^ 4 - (4 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry07_06 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (7 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (7 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
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
private theorem alternatingSixAmbientRow22_longMatrixABB_entry07_07 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (7 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (7 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(3 : ℂ) + (3 : ℂ) * ζ ^ 4 - (3 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(3 : ℂ) + (3 : ℂ) * ζ ^ 4 - (3 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry07_08 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (7 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (7 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(13 : ℂ) + (13 : ℂ) * ζ ^ 4 - (13 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(13 : ℂ) + (13 : ℂ) * ζ ^ 4 - (13 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry08_00 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (8 : Fin 9) (0 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (8 : Fin 9) (0 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry08_01 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (8 : Fin 9) (1 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (8 : Fin 9) (1 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry08_02 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (8 : Fin 9) (2 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (8 : Fin 9) (2 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry08_03 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (8 : Fin 9) (3 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (8 : Fin 9) (3 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry08_04 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (8 : Fin 9) (4 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (8 : Fin 9) (4 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry08_05 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (8 : Fin 9) (5 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (8 : Fin 9) (5 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry08_06 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (8 : Fin 9) (6 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (8 : Fin 9) (6 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry08_07 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (8 : Fin 9) (7 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (8 : Fin 9) (7 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow22_longMatrixABB_entry08_08 :
    (alternatingSixAmbientRow22LongMatrixAB
        * alternatingSixFiveAmbient_row22_matrixB)
          (8 : Fin 9) (8 : Fin 9) =
      alternatingSixAmbientRow22LongMatrixABB
        (8 : Fin 9) (8 : Fin 9) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow22LongMatrixAB,
    alternatingSixFiveAmbient_row22_matrixB,
    alternatingSixAmbientRow22LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

theorem alternatingSixAmbientRow22_longMatrixABB_mul :
    alternatingSixAmbientRow22LongMatrixAB *
        alternatingSixFiveAmbient_row22_matrixB =
      alternatingSixAmbientRow22LongMatrixABB := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientRow22_longMatrixABB_entry00_00
  · exact alternatingSixAmbientRow22_longMatrixABB_entry00_01
  · exact alternatingSixAmbientRow22_longMatrixABB_entry00_02
  · exact alternatingSixAmbientRow22_longMatrixABB_entry00_03
  · exact alternatingSixAmbientRow22_longMatrixABB_entry00_04
  · exact alternatingSixAmbientRow22_longMatrixABB_entry00_05
  · exact alternatingSixAmbientRow22_longMatrixABB_entry00_06
  · exact alternatingSixAmbientRow22_longMatrixABB_entry00_07
  · exact alternatingSixAmbientRow22_longMatrixABB_entry00_08
  · exact alternatingSixAmbientRow22_longMatrixABB_entry01_00
  · exact alternatingSixAmbientRow22_longMatrixABB_entry01_01
  · exact alternatingSixAmbientRow22_longMatrixABB_entry01_02
  · exact alternatingSixAmbientRow22_longMatrixABB_entry01_03
  · exact alternatingSixAmbientRow22_longMatrixABB_entry01_04
  · exact alternatingSixAmbientRow22_longMatrixABB_entry01_05
  · exact alternatingSixAmbientRow22_longMatrixABB_entry01_06
  · exact alternatingSixAmbientRow22_longMatrixABB_entry01_07
  · exact alternatingSixAmbientRow22_longMatrixABB_entry01_08
  · exact alternatingSixAmbientRow22_longMatrixABB_entry02_00
  · exact alternatingSixAmbientRow22_longMatrixABB_entry02_01
  · exact alternatingSixAmbientRow22_longMatrixABB_entry02_02
  · exact alternatingSixAmbientRow22_longMatrixABB_entry02_03
  · exact alternatingSixAmbientRow22_longMatrixABB_entry02_04
  · exact alternatingSixAmbientRow22_longMatrixABB_entry02_05
  · exact alternatingSixAmbientRow22_longMatrixABB_entry02_06
  · exact alternatingSixAmbientRow22_longMatrixABB_entry02_07
  · exact alternatingSixAmbientRow22_longMatrixABB_entry02_08
  · exact alternatingSixAmbientRow22_longMatrixABB_entry03_00
  · exact alternatingSixAmbientRow22_longMatrixABB_entry03_01
  · exact alternatingSixAmbientRow22_longMatrixABB_entry03_02
  · exact alternatingSixAmbientRow22_longMatrixABB_entry03_03
  · exact alternatingSixAmbientRow22_longMatrixABB_entry03_04
  · exact alternatingSixAmbientRow22_longMatrixABB_entry03_05
  · exact alternatingSixAmbientRow22_longMatrixABB_entry03_06
  · exact alternatingSixAmbientRow22_longMatrixABB_entry03_07
  · exact alternatingSixAmbientRow22_longMatrixABB_entry03_08
  · exact alternatingSixAmbientRow22_longMatrixABB_entry04_00
  · exact alternatingSixAmbientRow22_longMatrixABB_entry04_01
  · exact alternatingSixAmbientRow22_longMatrixABB_entry04_02
  · exact alternatingSixAmbientRow22_longMatrixABB_entry04_03
  · exact alternatingSixAmbientRow22_longMatrixABB_entry04_04
  · exact alternatingSixAmbientRow22_longMatrixABB_entry04_05
  · exact alternatingSixAmbientRow22_longMatrixABB_entry04_06
  · exact alternatingSixAmbientRow22_longMatrixABB_entry04_07
  · exact alternatingSixAmbientRow22_longMatrixABB_entry04_08
  · exact alternatingSixAmbientRow22_longMatrixABB_entry05_00
  · exact alternatingSixAmbientRow22_longMatrixABB_entry05_01
  · exact alternatingSixAmbientRow22_longMatrixABB_entry05_02
  · exact alternatingSixAmbientRow22_longMatrixABB_entry05_03
  · exact alternatingSixAmbientRow22_longMatrixABB_entry05_04
  · exact alternatingSixAmbientRow22_longMatrixABB_entry05_05
  · exact alternatingSixAmbientRow22_longMatrixABB_entry05_06
  · exact alternatingSixAmbientRow22_longMatrixABB_entry05_07
  · exact alternatingSixAmbientRow22_longMatrixABB_entry05_08
  · exact alternatingSixAmbientRow22_longMatrixABB_entry06_00
  · exact alternatingSixAmbientRow22_longMatrixABB_entry06_01
  · exact alternatingSixAmbientRow22_longMatrixABB_entry06_02
  · exact alternatingSixAmbientRow22_longMatrixABB_entry06_03
  · exact alternatingSixAmbientRow22_longMatrixABB_entry06_04
  · exact alternatingSixAmbientRow22_longMatrixABB_entry06_05
  · exact alternatingSixAmbientRow22_longMatrixABB_entry06_06
  · exact alternatingSixAmbientRow22_longMatrixABB_entry06_07
  · exact alternatingSixAmbientRow22_longMatrixABB_entry06_08
  · exact alternatingSixAmbientRow22_longMatrixABB_entry07_00
  · exact alternatingSixAmbientRow22_longMatrixABB_entry07_01
  · exact alternatingSixAmbientRow22_longMatrixABB_entry07_02
  · exact alternatingSixAmbientRow22_longMatrixABB_entry07_03
  · exact alternatingSixAmbientRow22_longMatrixABB_entry07_04
  · exact alternatingSixAmbientRow22_longMatrixABB_entry07_05
  · exact alternatingSixAmbientRow22_longMatrixABB_entry07_06
  · exact alternatingSixAmbientRow22_longMatrixABB_entry07_07
  · exact alternatingSixAmbientRow22_longMatrixABB_entry07_08
  · exact alternatingSixAmbientRow22_longMatrixABB_entry08_00
  · exact alternatingSixAmbientRow22_longMatrixABB_entry08_01
  · exact alternatingSixAmbientRow22_longMatrixABB_entry08_02
  · exact alternatingSixAmbientRow22_longMatrixABB_entry08_03
  · exact alternatingSixAmbientRow22_longMatrixABB_entry08_04
  · exact alternatingSixAmbientRow22_longMatrixABB_entry08_05
  · exact alternatingSixAmbientRow22_longMatrixABB_entry08_06
  · exact alternatingSixAmbientRow22_longMatrixABB_entry08_07
  · exact alternatingSixAmbientRow22_longMatrixABB_entry08_08

end InductiveMcKay
end McKayConjecture
